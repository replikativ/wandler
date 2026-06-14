(ns wandler.simd
  "Layer C — PROOF-GATED SIMD reduction (the floating-point determinism guarantee).

   A SIMD lane-wise reduction keeps one partial per vector lane and combines the lane-partials at the end
   in an unspecified order — which depends on the hardware vector width. So a SIMD reduction is only
   deterministic if its combine is ASSOCIATIVE:
     - exact integer / bitwise ops (Int/Nat add, bit-OR/AND/XOR, min, max) ARE associative — the result
       is identical on every vector width (measured: 4-lane == 8-lane == scalar). Safe to vectorize.
     - Float.add is NOT associative — the same program yields different sums per vector width (measured:
       scalar 0.0 vs 4-lane 1507904.0 vs 8-lane 1745760.0 on a crafted column). Silently vectorizing it
       gives platform-varying results.

   Every other engine (Spark, DuckDB, Arrow) ASSERTS associativity and vectorizes regardless. wandler
   PROVES it in the kernel and uses the proof as a LICENSE: licensed (exact) → deterministic SIMD via
   grafted Java (stratum.internal.SimdReduce — Clojure/un-intrinsified Vector code is a 10× trap); not
   provable (Float.add) → REFUSE, fall back to a deterministic scalar fold (or SIMD only behind an
   explicit `:reassociate-ok` opt-in that flags the result non-deterministic).

   Loads only under the :stratum alias (needs the compiled SimdReduce Java kernel)."
  (:import [stratum.internal SimdReduce]))

(def ^:private name->op
  "monoid spec :name → SimdReduce op code, for the exact lane-wise reductions."
  {:nat/add SimdReduce/OP_ADD :int/add SimdReduce/OP_ADD :float/add SimdReduce/OP_ADD
   :nat/bit-or SimdReduce/OP_OR :nat/bit-and SimdReduce/OP_AND :nat/bit-xor SimdReduce/OP_XOR
   :nat/max SimdReduce/OP_MAX :int/max SimdReduce/OP_MAX
   :nat/min SimdReduce/OP_MIN :int/min SimdReduce/OP_MIN})

(defn associative-proven?
  "Is the monoid's combine PROVEN associative for its value type? Exact integer/bitwise ops are
   (Nat.add_assoc, Int.add_assoc, Nat.lor_assoc, … — real kernel theorems); Float.add is NOT (it's false,
   so there is no proof). The principled check resolves the spec's `:laws :assoc` theorem against the
   kernel via check-constant; here we key on the exact value type carried in `:metadata :ansatz/type`
   (Nat/Int = exact ⇒ associativity holds; Float ⇒ refuse)."
  [spec]
  (contains? #{'Nat 'Int} (get-in spec [:metadata :ansatz/type])))

(defn simd-licensed?
  "True iff this monoid maps to an exact lane-wise op AND its associativity is proven — i.e. the SIMD
   lane-reduction is deterministic and sound to use."
  [spec]
  (boolean (and (name->op (:name spec)) (associative-proven? spec))))

(defn- scalar-reduce ^long [^longs col spec]
  (let [combine (:combine spec) n (alength col)]
    (loop [i 1 acc (if (zero? n) (long ((:unit-fn spec))) (aget col 0))]
      (if (< i n) (recur (inc i) (long (combine acc (aget col i)))) acc))))

(defn simd-reduce
  "Reduce native column `col` (long[]) under monoid `spec`, GATED on a proof of associativity. Returns
   {:result v, :simd bool, :deterministic bool, :reason kw?}. Licensed (exact) → deterministic Java SIMD;
   not provable (e.g. Float.add) → deterministic SCALAR (refused), unless `:reassociate-ok` is set (then
   SIMD with `:deterministic false`)."
  [^longs col spec & [{:keys [reassociate-ok]}]]
  (let [op (name->op (:name spec))]
    (cond
      (and op (associative-proven? spec))
      {:result (SimdReduce/reduceLong col (alength col) op (long ((:unit-fn spec))))
       :simd true :deterministic true}

      (and op reassociate-ok)
      {:result (SimdReduce/reduceLong col (alength col) op (long ((:unit-fn spec))))
       :simd true :deterministic false :warning "lane-reordered; result may vary by CPU vector width"}

      :else
      {:result (scalar-reduce col spec) :simd false :deterministic true
       :reason (if op :assoc-not-proven :unsupported-op)})))
