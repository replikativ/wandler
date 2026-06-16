(ns wandler.backend.simd
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
  (:import [stratum.internal SimdReduce ColumnOps]))

(def ^:private long-arr-class (class (long-array 0)))
(def ^:private double-arr-class (class (double-array 0)))

(def ^:private name->op
  "monoid spec :name → SimdReduce op code, for the exact lane-wise reductions."
  {:nat/add SimdReduce/OP_ADD :int/add SimdReduce/OP_ADD :float/add SimdReduce/OP_ADD
   :nat/bit-or SimdReduce/OP_OR :nat/bit-and SimdReduce/OP_AND :nat/bit-xor SimdReduce/OP_XOR
   :nat/max SimdReduce/OP_MAX :int/max SimdReduce/OP_MAX
   :nat/min SimdReduce/OP_MIN :int/min SimdReduce/OP_MIN})

(def ^:private order-independent-ops
  "Ops associative for EVERY value type (selection/bitwise — no rounding): the lane-reorder is always
   sound, float or not."
  #{SimdReduce/OP_OR SimdReduce/OP_AND SimdReduce/OP_XOR SimdReduce/OP_MIN SimdReduce/OP_MAX})

(defn associative-proven?
  "Is the monoid's combine PROVEN associative for its value type — so the SIMD lane-reorder is sound?
   min/max/AND/OR/XOR are associative for ANY type (they just select/combine bits — no rounding).
   ADD/MUL are associative for EXACT types (Nat.add_assoc, Int.add_assoc — real kernel theorems) but NOT
   for Float (rounding). So the gate is op×type, not type alone. (The principled check resolves the spec's
   `:laws :assoc` theorem against the kernel via check-constant; here we key on the op and the exact value
   type in `:metadata :ansatz/type`.)"
  [spec]
  (let [op (name->op (:name spec))]
    (boolean
     (and op
          (or (contains? order-independent-ops op)                  ; min/max/bitwise: any type
              (contains? #{'Nat 'Int} (get-in spec [:metadata :ansatz/type])))))))  ; add/mul: exact only

(defn simd-licensed?
  "True iff the SIMD lane-reduction is deterministic and sound to use for this monoid."
  [spec]
  (boolean (and (name->op (:name spec)) (associative-proven? spec))))

(defn- scalar-long ^long [^longs col spec]
  (let [combine (:combine spec) n (alength col)]
    (loop [i 1 acc (if (zero? n) (long ((:unit-fn spec))) (aget col 0))]
      (if (< i n) (recur (inc i) (long (combine acc (aget col i)))) acc))))

(defn- scalar-double ^double [^doubles col]
  (let [n (alength col)] (loop [i 0 acc 0.0] (if (< i n) (recur (inc i) (+ acc (aget col i))) acc))))

(defn simd-reduce
  "Reduce a native column (`long[]` or `double[]`) under monoid `spec`, GATED on a proof of associativity.
   Returns {:result v, :simd bool, :deterministic bool, :reason/:warning?}.
     long[]   licensed (exact op) → deterministic Java SIMD (stratum.internal.SimdReduce);
     double[] add → REFUSED (Float.add isn't associative) → deterministic scalar; with `:reassociate-ok`
              → SIMD via ColumnOps.sumDouble, flagged non-deterministic.
   This is the front door: bulk numeric column in, proof-gated reduction out."
  [col spec & [{:keys [reassociate-ok]}]]
  (let [c (class col) op (name->op (:name spec))]
    (cond
      (= c long-arr-class)
      (let [^longs col col]
        (if (and op (associative-proven? spec))
          {:result (SimdReduce/reduceLong col (alength col) op (long ((:unit-fn spec))))
           :simd true :deterministic true}
          {:result (scalar-long col spec) :simd false :deterministic true
           :reason (if op :assoc-not-proven :unsupported-op)}))

      (= c double-arr-class)
      (let [^doubles col col]
        (cond
          ;; min/max over doubles ARE associative (no rounding) → could license; here we wire only the
          ;; add path (the famous hazard), so add is refused unless explicitly opted in.
          reassociate-ok
          {:result (ColumnOps/sumDouble col 0 (alength col)) :simd true :deterministic false
           :warning "Float.add lane-reordered; result varies by CPU vector width"}
          :else
          {:result (scalar-double col) :simd false :deterministic true :reason :assoc-not-proven}))

      :else (throw (ex-info "simd-reduce expects a long[] or double[] column" {:class c})))))
