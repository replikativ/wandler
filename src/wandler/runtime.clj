;; Wandler runtime + lowering: the collection/relational/stream vocabulary as
;; CODEGEN-REGISTRY entries (ansatz SEAM 3) + the specialized runtime ops
;; (unboxed long[]/double[] map/filter/fold, the PARALLEL fork-join fold whose
;; licence is a kernel-proved monoid, windowed coalgebra observation).
;;
;; "Verification licenses the fast representation": each lowering pairs a kernel
;; DENOTATION (List.foldl, Map.join, Strm.scan ...) with an observationally-equal
;; fast Clojure implementation; the parallel fold is GATED on the associativity +
;; identity theorems being present in the env.
(ns wandler.runtime
  (:require [clojure.core.reducers :as ccr]
            [wandler.algebra :as algebra]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

;; ── specialized runtime ops ─────────────────────────────────────────────────

(def ^:private long-array-class (class (long-array 0)))
(def ^:private double-array-class (class (double-array 0)))
(clojure.core/defn amapl
  "`map` specialized for UNBOXED data: over a primitive `long[]` produce a new `long[]`
   (or `double[]`→`double[]` for `Float`/`Real` element fns) with ZERO boxing — and when `f`
   carries the matching primitive arity (`IFn$LL`/`IFn$DD`, which our induced `^long`/`^double`
   element fns do), call it via `invokePrim` so the whole loop is primitive end-to-end (this is
   what breaks the `mapv` boxing ceiling). Non-array input falls straight back to `mapv`, so
   existing vector pipelines are unchanged — a user opts in by passing a `long-array`/`double-array`."
  [f xs]
  (cond
    (instance? long-array-class xs)
    (if (instance? clojure.lang.IFn$LL f)
      (let [^longs a xs, n (alength a), r (long-array n)
            ^clojure.lang.IFn$LL g f]
        (dotimes [i n] (aset r i (.invokePrim g (aget a i))))
        r)
      ;; An unbounded Nat/Int result may promote beyond long. Preserve it rather
      ;; than narrowing it into the source's machine representation.
      (mapv f xs))
    (instance? double-array-class xs)
    (let [^doubles a xs, n (alength a), r (double-array n)]
      (if (instance? clojure.lang.IFn$DD f)
        (let [^clojure.lang.IFn$DD g f]
          (dotimes [i n] (aset r i (.invokePrim g (aget a i)))))
        (dotimes [i n] (aset r i (double (f (aget a i))))))
      r)
    ;; a LAZY seq stays LAZY (stream, don't force) — preserves laziness/infinite inputs;
    ;; an eager vector/list maps eagerly to a vector (unchanged).
    (instance? clojure.lang.LazySeq xs) (map f xs)
    :else (mapv f xs)))
(clojure.core/defn afoldl
  "foldl specialized for UNBOXED data: over a primitive `long[]` a tight primitive
   reduction — when the step carries a `long,long→long` arity (`IFn$LLL`, from induced
   `^long` hints on both params) it runs with ZERO boxing (the natural target of
   `foldl_map` fusion: a whole map→fold pipeline becomes one primitive scan). Non-array
   input falls back to `reduce`."
  [step init xs]
  (cond
    (instance? long-array-class xs)
    (let [^longs a xs, n (alength a)]
      (if (instance? clojure.lang.IFn$LLL step)
        (let [^clojure.lang.IFn$LLL g step]
          (loop [i 0, acc (long init)] (if (< i n) (recur (inc i) (.invokePrim g acc (aget a i))) acc)))
        (loop [i 0, acc init] (if (< i n) (recur (inc i) (step acc (aget a i))) acc))))
    (instance? double-array-class xs)
    (let [^doubles a xs, n (alength a)]
      (if (instance? clojure.lang.IFn$DDD step)
        (let [^clojure.lang.IFn$DDD g step]
          (loop [i 0, acc (double init)] (if (< i n) (recur (inc i) (.invokePrim g acc (aget a i))) acc)))
        (loop [i 0, acc init] (if (< i n) (recur (inc i) (step acc (aget a i))) acc))))
    :else (reduce step init xs)))
(def ^:private apfoldl-par-threshold
  "Minimum element count before a long[] fold forks (below this the single-thread
   primitive loop wins — fork/join setup isn't worth it)."
  131072)
(def ^:private apfoldl-grain
  "Target elements per chunk for the unboxed-parallel long[] fold."
  65536)
(clojure.core/defn- fold-longs-parallel
  "Unboxed PARALLEL reduce of a long[] over a proven monoid: split into contiguous
   chunks, reduce each from `init` in a primitive invokePrim loop (ZERO boxing per
   element), then merge the per-chunk partials with `op`. Sound because `op` is
   associative and `init` is its identity (gated at codegen) — each chunk starts at
   the identity, so merging slice-reductions reproduces the sequential fold."
  [op ^clojure.lang.IFn$LLL reducef init ^longs a]
  (let [n (alength a)
        cores (.availableProcessors (Runtime/getRuntime))
        nch (max 1 (min cores (quot n apfoldl-grain)))
        step (quot n nch)
        tasks (mapv (fn [c]
                      (let [lo (* c step)
                            hi (if (= c (dec nch)) n (+ lo step))]
                        (future
                          (loop [i lo, acc (long init)]
                            (if (< i hi) (recur (inc i) (.invokePrim reducef acc (aget a i))) acc)))))
                    (range nch))]
    (reduce op init (mapv deref tasks))))
(clojure.core/defn apfoldl
  "foldl over a PROVEN ASSOCIATIVE MONOID (combine op `op`, identity `init`). The
   kernel certifies `op` associative with `init` its identity (Item B), so the fold
   may be RE-ASSOCIATED and run in parallel — the associativity proof is exactly the
   soundness certificate fork-join needs. Backend by collection:
     • primitive long[] with a primitive step (IFn$LLL) and ≥ threshold elements →
       UNBOXED PARALLEL (fold-longs-parallel): zero boxing AND fork-join — the best
       of both; below threshold (or a non-primitive step) the unboxed single-thread
       loop (identical to afoldl, so the long[] path never regresses);
     • persistent vector → fork-join via clojure.core.reducers/fold: each chunk is
       reduced from `init` and chunk results merged with `op`;
     • anything else → sequential reduce.
   `reducef` is the per-element step (acc,x)→acc; `op` is the chunk-merge monoid op."
  [op reducef init xs]
  (cond
    (instance? long-array-class xs)
    (let [^longs a xs, n (alength a)]
      (cond
        (and (instance? clojure.lang.IFn$LLL reducef) (>= n apfoldl-par-threshold))
        (fold-longs-parallel op reducef init a)
        (instance? clojure.lang.IFn$LLL reducef)
        (let [^clojure.lang.IFn$LLL g reducef]
          (loop [i 0, acc (long init)] (if (< i n) (recur (inc i) (.invokePrim g acc (aget a i))) acc)))
        :else
        (loop [i 0, acc init] (if (< i n) (recur (inc i) (reducef acc (aget a i))) acc))))
    (instance? double-array-class xs)
    (let [^doubles a xs, n (alength a)]
      (if (instance? clojure.lang.IFn$DDD reducef)
        (let [^clojure.lang.IFn$DDD g reducef]
          (loop [i 0, acc (double init)] (if (< i n) (recur (inc i) (.invokePrim g acc (aget a i))) acc)))
        (loop [i 0, acc init] (if (< i n) (recur (inc i) (reducef acc (aget a i))) acc))))
    (vector? xs)
    (ccr/fold (fn ([] init) ([l r] (op l r))) reducef xs)
    :else (reduce reducef init xs)))
(clojure.core/defn unfold-take
  "Windowed observation of a coalgebra `(seed, step)` — the runtime of `Stream.unfoldTake`.
   `step : S → ([elem next-state] | nil)` (the codegen of `S → Option (elem × S)`: `some` is the
   bare [elem,state] pair, `none` is nil). Pulls up to `n` elements from `s`, stopping early when
   `step` yields nil. This is how a BOUNDED WINDOW is taken from an UNBOUNDED/LAZY source: `s` may be
   an infinite lazy seq with `step` = uncons, or any state with a productive step — `unfold-take`
   forces exactly `n` (or fewer) elements, never the whole stream. The window is a realized vector;
   the kernel-certified List pipeline then runs over it."
  [step n s]
  (loop [acc (transient []), st s, k (long n)]
    (if (<= k 0)
      (persistent! acc)
      (let [r (step st)]
        (if (nil? r)
          (persistent! acc)
          (recur (conj! acc (nth r 0)) (nth r 1) (dec k)))))))
(clojure.core/defn afilter
  "filter specialized for UNBOXED data: over a primitive `long[]` it keeps the passing
   elements into a fresh `long[]` (one allocation, trimmed to the kept count). The
   predicate is called via its primitive long→Bool arity (`IFn$LO`, from an induced `^long`
   hint) so the scan boxes nothing per element. A long[] result composes with amapl/afoldl
   (filter_filter / foldl_filter fusion stays primitive). Non-array input falls back to
   filterv."
  [pred xs]
  (cond
    (instance? long-array-class xs)
    (let [^longs a xs, n (alength a), tmp (long-array n)
          c (if (instance? clojure.lang.IFn$LO pred)
              (let [^clojure.lang.IFn$LO p pred]
                (loop [i 0, c 0]
                  (if (< i n)
                    (if (.invokePrim p (aget a i)) (do (aset tmp c (aget a i)) (recur (inc i) (inc c))) (recur (inc i) c))
                    c)))
              (loop [i 0, c 0]
                (if (< i n)
                  (if (pred (aget a i)) (do (aset tmp c (aget a i)) (recur (inc i) (inc c))) (recur (inc i) c))
                  c)))]
      (java.util.Arrays/copyOf tmp (int c)))
    (instance? double-array-class xs)
    (let [^doubles a xs, n (alength a), tmp (double-array n)
          c (if (instance? clojure.lang.IFn$DO pred)
              (let [^clojure.lang.IFn$DO p pred]
                (loop [i 0, c 0]
                  (if (< i n)
                    (if (.invokePrim p (aget a i)) (do (aset tmp c (aget a i)) (recur (inc i) (inc c))) (recur (inc i) c))
                    c)))
              (loop [i 0, c 0]
                (if (< i n)
                  (if (pred (aget a i)) (do (aset tmp c (aget a i)) (recur (inc i) (inc c))) (recur (inc i) c))
                  c)))]
      (java.util.Arrays/copyOf tmp (int c)))
    ;; lazy seq stays lazy (stream); eager input filters eagerly to a vector.
    (instance? clojure.lang.LazySeq xs) (filter pred xs)
    :else (filterv pred xs)))

;; ── codegen helpers ─────────────────────────────────────────────────────────

(clojure.core/defn- nary-op
  "Emit `(op a b)` when a binary primitive is fully applied (≥2 compiled args),
   else a `partial` — so an eta-reduced / partially-applied op (simp turns
   `(fun y => Nat.ble k y)` into the partial `(Nat.ble k)`) still lowers to a
   runnable fn rather than blowing an arity assumption."
  [op ca]
  (cond
    (>= (count ca) 2) (list op (nth ca 0) (nth ca 1))
    (= (count ca) 1)  (list 'clojure.core/partial op (nth ca 0))
    :else op))

(clojure.core/defn- prim-tag
  "JVM primitive type hint INDUCED from a binder's kernel type, or nil.
   `UInt*` → `long`, `Float`/`Real` → `double`. Unbounded Nat/Int stay boxed so
   arithmetic can promote beyond long. Hinting a (curried, 1-arg) element fn lets
   Clojure emit a primitive `invokePrim` arity, so the fn BODY does primitive arithmetic
   (no per-op boxing) — the unboxed half of the perf story, alongside Int64 literals."
  [ty]
  (when (e/const? ty)
    (case (name/->string (e/const-name ty))
      ("UInt8" "UInt16" "UInt32" "UInt64") 'long
      ("Float" "Real") 'double
      nil)))

(def ^:dynamic *parallel-fold*
  "When true (default), a foldl recognized as a proven associative monoid (Item B)
   lowers to the parallel fork-join `apfoldl` (vector path); set false to force the
   sequential `afoldl`. The long[] unboxed path is unaffected either way."
  true)

(clojure.core/defn- monoid-fold-op
  "If foldl step `f-expr` is `acc ⊕ h(x)` (a fused λacc.λx. ⊕ acc rhs with acc NOT
   free in rhs) or a bare `⊕` const, for a registered associative-monoid op ⊕, AND
   `init-clj` is ⊕'s identity, AND ⊕'s kernel laws are present in `env`, return the
   Clojure combine op symbol for apfoldl; else nil (→ sequential afoldl)."
  [env f-expr init-clj]
  (let [opn (cond
              ;; bare op const: (reduce + 0 xs) → step is the const Nat.add itself
              (e/const? f-expr) (name/->string (e/const-name f-expr))
              ;; fused step λ acc. λ x. (⊕ acc rhs); acc = bvar 1, must not occur in rhs
              (and (e/lam? f-expr) (e/lam? (e/lam-body f-expr)))
              (let [body (e/lam-body (e/lam-body f-expr))
                    [h hargs] (e/get-app-fn-args body)]
                (when (and (e/const? h) (>= (count hargs) 2))
                  (let [a   (nth hargs (- (count hargs) 2))
                        rhs (nth hargs (- (count hargs) 1))]
                    (when (and (e/bvar? a) (= 1 (e/bvar-idx a))   ; left operand IS acc
                               (<= (e/bvar-range rhs) 1))          ; acc (bvar 1) unused in rhs
                      (name/->string (e/const-name h)))))))]
    ;; the licence lives in the ONE registry (wandler.algebra): registered op + init is
    ;; its identity + the associativity/identity theorems present in the env
    (when opn (algebra/monoid-licence env opn init-clj))))

(clojure.core/defn- emit-hinted-fn
  "Codegen a kernel lambda `f-expr` as a Clojure fn with up to `arity` params, each
   ^long/^double-hinted from its binder's kernel type, AND a primitive RETURN hint
   `rtag` on the param vector — so Clojure generates the primitive IFn$LL/IFn$LLL/IFn$DD
   arity and the element/step call is invoked via invokePrim with ZERO boxing (without the
   return hint a `^long`-param fn is still Object-returning, so every call boxes). A bare
   op / eta-reduced step (not a lambda) is emitted as-is."
  [env f-expr arity rtag names]
  (if (e/lam? f-expr)
    (loop [e f-expr, ps [], ns names]
      (if (and (< (count ps) arity) (e/lam? e))
        ;; name by ABSOLUTE binder depth (count of names in scope), NOT the local param index —
        ;; otherwise nested step-fns both restart at p0/p1 and an outer reference (a deeper de
        ;; Bruijn index, correctly resolved by position) is emitted with a name the INNER binder
        ;; shadows ⇒ Clojure lexical capture (e.g. a nested-loop bucket filter comparing the order
        ;; key to ITSELF instead of the outer row key). Depth-unique names match the `v<n>` scheme.
        (let [n (str "p" (count ns))
              tag (prim-tag (e/lam-type e))
              sym (if tag (with-meta (symbol n) {:tag tag}) (symbol n))]
          (recur (e/lam-body e) (conj ps sym) (conj ns n)))
        (list 'fn (if rtag (with-meta ps {:tag rtag}) ps) (a/ansatz->clj env e ns))))
    (a/ansatz->clj env f-expr names)))

(clojure.core/defn- eta-saturate
  "Eta-expand an under-applied known op for codegen. `saturated` maps the FULL compiled-arg vector
   to a Clojure form. If `ca` already has ≥ `arity` args, apply it directly; otherwise emit
   (fn [g…] (saturated ca++g)) supplying the missing args — handles e.g. a join that unfolds to
   `map (Prod.mk α β x) bucket` (Prod.mk applied to 3 of 4 args, used as the map fn)."
  [ca arity saturated]
  (if (>= (count ca) arity)
    (saturated ca)
    (let [gs (mapv (fn [_] (gensym "eta")) (range (- arity (count ca))))]
      (list 'clojure.core/fn gs (saturated (into ca gs))))))

;; ── loop-invariant hoisting (index builds out of element fns) ───────────────

(clojure.core/defn- form-free-syms
  "Free (unbound, unqualified) symbols of an emitted Clojure form, given the
   set `bound` of symbols already in scope. Understands the emitted grammar's
   binders (`fn` param vectors, sequential `let` bindings); everything else is
   treated as application/literal structure."
  [form bound]
  (cond
    (symbol? form)
    (if (or (contains? bound form) (namespace form) (special-symbol? form)) #{} #{form})

    (seq? form)
    (let [[op & more] form]
      (cond
        (and (contains? #{'fn 'clojure.core/fn} op) (vector? (first more)))
        (let [b (into bound (filter symbol? (first more)))]
          (reduce into #{} (map #(form-free-syms % b) (rest more))))

        (and (contains? #{'let 'clojure.core/let} op) (vector? (first more)))
        (loop [bs (partition 2 (first more)), b bound, acc #{}]
          (if-let [[[s v] & r] (seq bs)]
            (recur r (conj b s) (into acc (form-free-syms v b)))
            (reduce into acc (map #(form-free-syms % b) (rest more)))))

        :else (reduce into #{} (map #(form-free-syms % bound) form))))

    (coll? form) (reduce into #{} (map #(form-free-syms % bound) (seq form)))
    :else #{}))

(def ^:private hoistable-heads
  "Emitted heads that BUILD an index/lookup structure (O(n) work) — worth hoisting
   out of a per-element fn when they depend on none of its binders."
  #{'clojure.core/group-by 'clojure.core/into})

(clojure.core/defn- hoist-invariants
  "Loop-invariant code motion over an emitted element-fn form: any index-building
   subform (`hoistable-heads`) that references none of the fn's params nor any
   binder on its path is lifted out. Returns [let-bindings fn-form']. The semijoin
   probe `(filter (fn [x] (get (group-by kf ys) x)) xs)` is the motivating case:
   without the hoist the index is rebuilt per element — O(n·m) instead of O(n+m)."
  [fn-form]
  (if-not (and (seq? fn-form) (contains? #{'fn 'clojure.core/fn} (first fn-form))
               (vector? (second fn-form)))
    [[] fn-form]
    (let [hoisted (atom [])                                ;; [[form sym] …] in discovery order
          sym-for (fn [form]
                    (or (some (fn [[f g]] (when (= f form) g)) @hoisted)
                        (let [g (gensym "idx")] (swap! hoisted conj [form g]) g)))
          walk (fn walk [form bound]
                 (cond
                   (and (seq? form) (contains? hoistable-heads (first form))
                        (not-any? bound (form-free-syms form #{})))
                   (sym-for form)

                   (seq? form)
                   (let [[op & more] form]
                     (cond
                       (and (contains? #{'fn 'clojure.core/fn} op) (vector? (first more)))
                       (let [b (into bound (filter symbol? (first more)))]
                         (apply list op (first more) (map #(walk % b) (rest more))))

                       (and (contains? #{'let 'clojure.core/let} op) (vector? (first more)))
                       (loop [bs (partition 2 (first more)), b bound, out []]
                         (if-let [[[s v] & r] (seq bs)]
                           (recur r (conj b s) (conj out s (walk v b)))
                           (apply list op out (map #(walk % b) (rest more)))))

                       :else (apply list (map #(walk % bound) form))))

                   :else form))
          params (set (filter symbol? (second fn-form)))
          body' (map #(walk % params) (drop 2 fn-form))
          fn-form' (apply list (first fn-form) (second fn-form) body')]
      [(into [] (mapcat (fn [[f g]] [g f])) @hoisted) fn-form'])))

(clojure.core/defn- with-hoisted
  "Emit `(make fn-form')` with any invariant index builds hoisted to a wrapping let."
  [fn-form make]
  (let [[bs f'] (hoist-invariants fn-form)]
    (if (seq bs) (list 'clojure.core/let bs (make f')) (make fn-form))))

;; ── the lowering table (codegen-registry entries) ───────────────────────────

(defmacro ^:private lowerings
  "Build a {head → (fn [env ca args names] → clj-form)} map from case-style `head body` clauses, with
   env/ca/args/names ANAPHORICALLY bound in each body — ca = pre-compiled arg forms, args = raw Expr
   args, env/names for arms that recursively lower a sub-term. Keeps the built-in vocabulary readable
   as a table while making it a single extensible map (vs the old case + parallel head-list pair)."
  [& clauses]
  (into {} (for [[k body] (partition 2 clauses)]
             [k `(fn [~'env ~'ca ~'args ~'names] ~body)])))

(def ^:private base-lowerings
  "wandler's built-in runtime vocabulary (Int/Float/String/List/Map/Option/Stream/… ops) plus the few
   built-ins needed in VALUE position (Float.*, OfScientific). Heads ansatz lowers NATIVELY (dite,
   WellFounded.Nat.fix, HAdd…HPow, Nat.add/mul/div/pow/succ/blt/ble/beq, Bool.true/false, Nat.zero,
   ite, List.cons/nil/length, Subtype.val/mk, SizeOf.sizeOf) are NOT here: ansatz's builtin-app table
   fires BEFORE this codegen-registry seam, so a copy would be dead."
  (lowerings
            ;; Unbounded Int arithmetic matches Ansatz's promoting operators.
   "Int.add" (nary-op '+' ca)
   "Int.mul" (nary-op '*' ca)
   "Int.sub" (nary-op '-' ca)
   "Int.div" (list 'quot (nth ca 0) (nth ca 1))
   "Int.ofNat" (nth ca 0)
   "Int.neg" (list '-' (nth ca 0))
   "Float.ofNat" (list 'double (nth ca 0))
   "Bool.not" (list 'not (nth ca 0))
            ;; Bool.and/or : the two Bool args lower to Clojure booleans (Nat.ble/beq, Bool.true/false
            ;; are ansatz-native). Short-circuit form keeps it a boolean.
   "Bool.and" (list 'and (nth ca 0) (nth ca 1))
   "Bool.or"  (list 'or  (nth ca 0) (nth ca 1))
            ;; cond α c x y (the Bool eliminator, `bif`) → (if c x y). ca[0]=α erases. Used by the
            ;; conditional FAQ frame's guarded weight (cond (P x) (f x) 0). NB: Clojure `cond` is a macro,
            ;; so this MUST be emitted as `if`.
   "cond" (list 'if (nth ca 1) (nth ca 2) (nth ca 3))
            ;; Function.comp α β γ f g [x] → (comp f g) or (f (g x)). Produced by
            ;; map∘map fusion (List.map_map rewrites to map (f ∘ g)).
   "Function.comp" (if (>= (count ca) 6)
                     (list (nth ca 3) (list (nth ca 4) (nth ca 5)))
                     (list 'clojure.core/comp (nth ca 3) (nth ca 4)))
            ;; Float literal: OfScientific.ofScientific Float inst m s e → m × 10^±e.
            ;; (args: α inst mantissa exponentSign decimalExponent) — type/inst erase.
   "OfScientific.ofScientific"
   (let [m (nth ca 2) s (nth ca 3) ex (nth ca 4)]
     (if (and (number? m) (number? ex) (boolean? s))
       (* (double m) (Math/pow 10.0 (double (if s (- ex) ex))))   ; computed literal
       (list '* (list 'double m) (list 'Math/pow 10.0 (list 'if s (list '- ex) ex)))))
            ;; Float arithmetic → Clojure double ops (type/instance args erase).
   "Float.add" (list '+ (nth ca 0) (nth ca 1))
   "Float.mul" (list '* (nth ca 0) (nth ca 1))
   "Float.sub" (list '- (nth ca 0) (nth ca 1))
   "Float.div" (list '/ (nth ca 0) (nth ca 1))
            ;; String ops → Clojure string ops. String.append a b → concat; the
            ;; (String, ++, "") monoid: String.append IS the concat. length → count.
   "String.append" (list 'clojure.core/str (nth ca 0) (nth ca 1))
   "String.length" (list 'clojure.core/count (nth ca 0))
   "String.toUpper" (list 'clojure.string/upper-case (nth ca 0))
   "String.toLower" (list 'clojure.string/lower-case (nth ca 0))
   "String.isPrefixOf" (list 'clojure.string/starts-with? (nth ca 1) (nth ca 0))
            ;; List.elem K beq x ys → x ∈ ys (beq erases to structural =). args: K beq x ys.
   "List.elem" (list 'clojure.core/boolean
                     (list 'clojure.core/some
                           (list 'fn ['__e] (list 'clojure.core/= '__e (nth ca 2)))
                           (nth ca 3)))
            ;; List.all/any α l p → every?/some over the list (boolean). args: α l p.
   "List.all" (list 'clojure.core/boolean (list 'clojure.core/every? (nth ca 2) (nth ca 1)))
   "List.any" (list 'clojure.core/boolean (list 'clojure.core/some (nth ca 2) (nth ca 1)))
   "String.toList" (list 'clojure.core/vec (nth ca 0))     ; String → seq of chars
   "Char.toNat" (list 'clojure.core/int (nth ca 0))        ; char → code point (Nat)
   "Float.beq" (list 'clojure.core/== (nth ca 0) (nth ca 1))
            ;; Decidable.decide P inst → the Bool. P is the decided proposition (an
            ;; ordering/equality over Int/Float); read the comparison off P's head.
            ;; (args: P inst — both erase; we recompute the boolean from P's operands.)
   "Decidable.decide"
   (let [prop (nth args 0)
         [ph pa] (e/get-app-fn-args prop)
         pn (when (e/const? ph) (name/->string (e/const-name ph)))]
     (case pn
       ("Int.lt" "Float.lt" "Nat.lt") (list '< (a/ansatz->clj env (nth pa 0) names) (a/ansatz->clj env (nth pa 1) names))
       ("Int.le" "Float.le" "Nat.le") (list '<= (a/ansatz->clj env (nth pa 0) names) (a/ansatz->clj env (nth pa 1) names))
       "Eq" (list 'clojure.core/= (a/ansatz->clj env (nth pa 1) names) (a/ansatz->clj env (nth pa 2) names))
       (nth ca 1)))
            ;; Eq as a runtime condition (e.g. the `p x = true` guard in a fused
            ;; foldl_filter step): Bool equalities collapse to the bool itself.
   "Eq" (let [rhs-head (first (e/get-app-fn-args (nth args 2)))
              rhs-name (when (e/const? rhs-head) (name/->string (e/const-name rhs-head)))]
          (case rhs-name
            "Bool.true" (nth ca 1)
            "Bool.false" (list 'not (nth ca 1))
            (list 'clojure.core/= (nth ca 1) (nth ca 2))))
            ;; BEq equality: BEq.beq α inst a b → (= a b) (type/instance erased).
   "BEq.beq" (list 'clojure.core/= (nth ca 2) (nth ca 3))
            ;; Prod projections: Prod.mk compiles to a [fst snd] vector, so fst/snd
            ;; are positional. (args: α β p)
            ;; Prod is a plain pair at runtime: Prod.mk α β a b → [a b] (NOT the tagged-ctor [0 a b]),
            ;; matching Prod.fst/snd's nth 0/1. args: α β a b.
   "Prod.mk"  (eta-saturate ca 4 (fn [f] (list 'clojure.core/vector (nth f 2) (nth f 3))))
   "Prod.fst" (eta-saturate ca 3 (fn [f] (list 'clojure.core/nth (nth f 2) 0)))
   "Prod.snd" (eta-saturate ca 3 (fn [f] (list 'clojure.core/nth (nth f 2) 1)))
            ;; List.sum's Nat/Int carriers are unbounded, including intermediate sums.
   "List.sum" (list 'clojure.core/reduce '+' 0 (nth ca 3))
            ;; List SOACs (args: types…, then runtime values) → native Clojure.
            ;; A foldl step is acc→elem→acc. An inline-fn step compiles to a CURRIED
            ;; lambda, but clojure.core/reduce invokes it (f acc x) — flat. So peel a
            ;; lambda step's two binders into one flat param vector. A bare const step
            ;; (e.g. + ← Nat.add) is already a flat 2-arg fn — pass it through.
   "List.foldl"
   (let [f-expr (nth args 2)
                  ;; the step's RESULT type is the accumulator type (args[0]); a primitive
                  ;; return hint makes the step an IFn$LLL/DDD → afoldl/apfoldl invoke it
                  ;; via invokePrim (zero boxing), not the boxed fallback.
         step (emit-hinted-fn env f-expr 2 (prim-tag (nth args 0)) names)
                  ;; Item B: if this is a proven associative-monoid fold, lower to
                  ;; the parallel fork-join apfoldl (vector path); else sequential afoldl.
         mop (when *parallel-fold* (monoid-fold-op env f-expr (nth ca 3)))
         mk (fn [s lst] (if mop (list 'wandler.runtime/apfoldl mop s (nth ca 3) lst)
                            (list 'wandler.runtime/afoldl s (nth ca 3) lst)))]
     (with-hoisted step
                ;; arity-tolerant: `List.foldl … op init` as a fn VALUE (eta-reduced, e.g. fused into a
                ;; comp by `map (fn [g] (reduce op init g))`) wraps the missing list arg in a lambda.
       #(if (>= (count ca) 5)
          (mk % (nth ca 4))
          (let [l (gensym "l")] (list 'fn [l] (mk % l))))))
            ;; map fn α→β: hint param α + RETURN β so it's IFn$LL/DD (amapl invokePrim).
            ;; prefix/suffix + head/tail → Clojure runtime ops. take/take-while/drop are
            ;; LAZY (a bounded terminal makes an infinite lazy pipeline consumable).
            ;; (args: α [n|pred] coll — type erases.) head?/getLast? are Option → value-or-nil.
   "List.take" (list 'clojure.core/take (nth ca 1) (nth ca 2))
   "List.drop" (list 'clojure.core/drop (nth ca 1) (nth ca 2))
   "List.chunk" (list 'clojure.core/partition-all (nth ca 1) (nth ca 2))  ; grace-hash spill blocks (α B l)
            ;; windowed stream observation: pull ≤ n from a coalgebra (seed,step) — runs over an
            ;; infinite/lazy source, forcing only the window. (args: A S step n s — types erase.)
   "Stream.unfoldTake" (list 'wandler.runtime/unfold-take (nth ca 2) (nth ca 3) (nth ca 4))
            ;; Strm A = Nat → A (the infinite-stream surface). A stream is a Clojure fn Nat→A;
            ;; range = identity, smap = post-compose, take = materialize the window [0..n-1].
   "Strm.range" 'clojure.core/identity                                     ; λn. n
   "Strm.smap" (list 'clojure.core/comp (nth ca 2) (nth ca 3))             ; A B g s → g∘s
   "Strm.take" (list 'clojure.core/mapv (nth ca 2) (list 'clojure.core/range (nth ca 1)))  ; A n s → (mapv s (range n))
            ;; Strm.scan op init s : Strm B — the running aggregate. Certified ≡ the incremental
            ;; recurrence (Strm.scan_step), which licenses the O(n) lazy `reductions` impl: the m-th
            ;; running aggregate is `(nth (reductions op init (map s (range))) m)`.
   "Strm.scan" (let [nn (gensym "n")]                                       ; A B op init s
                 (list 'clojure.core/fn [nn]
                       (list 'clojure.core/nth
                             (list 'clojure.core/reductions (nth ca 2) (nth ca 3)
                                   (list 'clojure.core/map (nth ca 4) (list 'clojure.core/range)))
                             (list 'clojure.core/inc nn))))
            ;; LSeq A = Nat → Option A (possibly-finite). Runtime = a real lazy seq; smap = lazy map,
            ;; take = lazy take → vector (stops at seq end OR n, whichever first). A passed-in lazy seq
            ;; IS the value (no wrapping). Works on infinite lazy seqs, forcing only the window.
   "LSeq.smap" (list 'clojure.core/map (nth ca 2) (nth ca 3))              ; A B g s → (map g s)
   "LSeq.take" (list 'clojure.core/vec (list 'clojure.core/take (nth ca 1) (nth ca 2)))  ; A n s → (vec (take n s))
   "List.getD" (list 'clojure.core/nth (nth ca 1) (nth ca 2) (nth ca 3))   ; nth coll i default
   "List.range" (list 'clojure.core/range (nth ca 0))                       ; (range n)
   "List.takeWhile" (list 'clojure.core/take-while (nth ca 1) (nth ca 2))
   "List.dropWhile" (list 'clojure.core/drop-while (nth ca 1) (nth ca 2))
   "List.head?" (list 'clojure.core/first (nth ca 1))
   "List.getLast?" (list 'clojure.core/last (nth ca 1))
   "List.tail" (list 'clojure.core/rest (nth ca 1))
   "List.isEmpty" (list 'clojure.core/empty? (nth ca 1))                ; args: α l  (α erased)
            ;; headD as default → first-or-default. args: α as default → as=ca[1] default=ca[2].
   "List.headD" (list 'if (list 'clojure.core/empty? (nth ca 1))
                      (nth ca 2) (list 'clojure.core/first (nth ca 1)))
            ;; eta-saturate: map∘map fusion (e.g. an outer agg over `partition-all`, whose inner stage
            ;; is `map reverse`) can leave `List.reverse α` POINT-FREE (used as a function value), so the
            ;; coll arg is absent — emit `(fn [g] (reverse g))` then. args: α coll → coll=ca[1].
   "List.reverse" (eta-saturate ca 2 (fn [f] (list 'clojure.core/reverse (nth f 1))))
            ;; reverseAux as tail = (reverse as) ++ tail (reverse's TR helper; the optimizer can leave
            ;; it in a term). args: α as tail → as=ca[1] tail=ca[2].
   "List.reverseAux" (list 'clojure.core/concat (list 'clojure.core/reverse (nth ca 1)) (nth ca 2))
   "List.dropLast" (list 'clojure.core/drop-last (nth ca 1))             ; args: α coll (α erased)
            ;; Nat.max/Nat.min as a bare REDUCE STEP can be left POINT-FREE by fusion (e.g. a windowed
            ;; `map (reduce max 0) (partition-all …)`), so the ansatz builtin table — which only lowers
            ;; the APPLIED `Nat.max a b` — misses it. eta-saturate to `(fn [a b] (max a b))`. (args a b)
   "Nat.max" (eta-saturate ca 2 (fn [f] (list 'clojure.core/max (nth f 0) (nth f 1))))
   "Nat.min" (eta-saturate ca 2 (fn [f] (list 'clojure.core/min (nth f 0) (nth f 1))))
   "List.append" (list 'clojure.core/concat (nth ca 1) (nth ca 2))      ; args: α a b
            ;; flatten (one level): List (List α) → List α. args: α coll. The flatMap
            ;; fusion laws (map_flatMap/flatMap_map) can surface a bare flatten∘map.
   "List.flatten" (list 'clojure.core/apply 'clojure.core/concat (nth ca 1))
            ;; zip: List.zip α β xs ys → (map vector xs ys). Prod is a 2-vector at runtime
            ;; (Prod.fst↦nth0 / Prod.snd↦nth1), so `vector` builds the right pair rep. xs/ys are the
            ;; runtime args at ca[2]/ca[3] (ca[0]=α ca[1]=β are the compiled — unused — type args).
   "List.zip" (list 'clojure.core/map 'clojure.core/vector (nth ca 2) (nth ca 3))
            ;; zipWith f xs ys → (map f xs ys) — Clojure's variadic map applies f pairwise. (List.zip
            ;; elaborates THROUGH `zipWith Prod.mk`, whose f lowers to `vector` ⇒ the same pair rep.)
            ;; args: α β γ f xs ys → f=ca[3] xs=ca[4] ys=ca[5].
   "List.zipWith" (list 'clojure.core/map (nth ca 3) (nth ca 4) (nth ca 5))
   "List.intersperse" (list 'clojure.core/interpose (nth ca 1) (nth ca 2)) ; args: α sep coll
            ;; flatMap/filterMap (mapcat/keep) — args: α β f coll. filterMap's f returns
            ;; Option β (value-or-nil at runtime), exactly what clojure.core/keep wants.
   "List.flatMap" (list 'clojure.core/mapcat (nth ca 2) (nth ca 3))
   "List.filterMap" (list 'clojure.core/keep (nth ca 2) (nth ca 3))
            ;; mapIdx (map-indexed) — args: α β f coll. emit-hinted-fn flattens the curried
            ;; step to a 2-arg (fn [i x] …) (handles bare ops too); map-indexed calls (f i x).
   "List.mapIdx" (list 'clojure.core/map-indexed
                       (emit-hinted-fn env (nth args 2) 2 nil names)
                       (nth ca 3))
            ;; scanl (reductions) — args: acc elem f init coll. Same 2-arg-step flattening.
   "List.scanl" (list 'clojure.core/reductions
                      (emit-hinted-fn env (nth args 2) 2 nil names)
                      (nth ca 3) (nth ca 4))
            ;; eraseReps (dedupe) — args: α beq coll → drop consecutive dups.
   "List.eraseReps" (list 'clojure.core/dedupe (nth ca 2))
            ;; EXTRINSIC alist map: kernel denotation = List(K×V), runtime = hash-map.
            ;; empty→{}, get→(get m k d), put→(assoc m k v). args carry [K V deceq …].
   "AList.empty" {}
   "AList.get" (list 'clojure.core/get (nth ca 5) (nth ca 3) (nth ca 4))   ; k d l → (get l k d)
   "AList.put" (list 'clojure.core/assoc (nth ca 5) (nth ca 3) (nth ca 4)) ; k v l → (assoc l k v)
            ;; Option eliminators — runtime rep of Option is value-or-nil. (Caveat: a `some
            ;; nil` collapses to none — fine for non-nilable element types.)
   "Option.some" (nth ca 1)                                  ; α x → x
   "Option.none" nil                                         ; α → nil
   "Option.isSome" (list 'clojure.core/some? (nth ca 1))     ; α opt
   "Option.isNone" (list 'clojure.core/nil? (nth ca 1))      ; α opt
   "Option.getD" (let [o (gensym "o")]                       ; α opt default
                   (list 'clojure.core/let [o (nth ca 1)]
                         (list 'if (list 'clojure.core/nil? o) (nth ca 2) o)))
   "Option.elim" (let [o (gensym "o")]                       ; α β opt none somefn
                   (list 'clojure.core/let [o (nth ca 2)]
                         (list 'if (list 'clojure.core/nil? o) (nth ca 3) (list (nth ca 4) o))))
   "Option.map" (let [o (gensym "o")]                        ; α β f opt
                  (list 'clojure.core/let [o (nth ca 3)]
                        (list 'if (list 'clojure.core/nil? o) nil (list (nth ca 2) o))))
   "Option.bind" (let [o (gensym "o")]                       ; α β opt f
                   (list 'clojure.core/let [o (nth ca 2)]
                         (list 'if (list 'clojure.core/nil? o) nil (list (nth ca 3) o))))
   "List.map" (with-hoisted (emit-hinted-fn env (nth args 2) 1 (prim-tag (nth args 1)) names)
                #(list 'wandler.runtime/amapl % (nth ca 3)))
            ;; filter pred α→Bool: hint param α (return Bool stays Object → IFn$LO for afilter).
   "List.filter" (with-hoisted (emit-hinted-fn env (nth args 1) 1 nil names)
                   #(list 'wandler.runtime/afilter % (nth ca 2)))
            ;; assoc lookup: List.lookup α β (BEq α) k l → value-or-nil. The
            ;; runtime list is a seq of [k v] pairs (Prod.mk erases to a vector),
            ;; so (into {} l) is the map; Option β is modeled as value-or-nil
            ;; (some v ↔ v, none ↔ nil — idiomatic Clojure get). (args: α β beq k l)
   "List.lookup" (list 'get (list 'into {} (nth ca 4)) (nth ca 3))
            ;; Verified Map ops lower to a REAL Clojure hash-map (O(1) probe / O(n) build), NOT the
            ;; assoc-list — the kernel rep is `{List(K×V) // NodupKeys}` but the runtime is a hash-map, which
            ;; is observationally equal for the Map operations (lookup/insert/group_by/entries) and what makes
            ;; joins scale. Map.insert: [K V inst k v m]; Map.lookup: [K V inst k m].
   "Map.insert" (list 'assoc (nth ca 5) (nth ca 3) (nth ca 4))   ; (assoc m k v) — overwrites, NodupKeys
   "Map.lookup" (list 'get (nth ca 4) (nth ca 3))                ; (get m k) — O(1), value-or-nil ≈ Option
   "Map.empty" {}
            ;; group-by over a hash-map: O(n) build, buckets = items per key. (args: K V deceq f xs)
   "Map.group_by" (list 'clojure.core/group-by (nth ca 3) (nth ca 4))
            ;; ->map boundary: the Map is already a Clojure hash-map. (args: K V m)
   "Map.entries" (nth ca 2)
            ;; join: group ys by lf, pair each x with matches by kf. (args: K X Y D kf lf xs ys)
            ;; The pair multiset matches the kernel; order is join-irrelevant.
   "Map.join"
   (let [grp (gensym "g") xx (gensym "x") yy (gensym "y")
         kf (nth ca 4) lf (nth ca 5) xs (nth ca 6) ys (nth ca 7)]
     (list 'let [grp (list 'clojure.core/group-by lf ys)]
           (list 'vec (list 'clojure.core/mapcat
                            (list 'fn [xx]
                                  (list 'clojure.core/mapv (list 'fn [yy] [xx yy])
                                        (list 'get grp (list kf xx) [])))
                            xs))))
            ;; distinct: List.eraseDups α (BEq α) xs → (distinct xs). The BEq
            ;; instance is erased — Clojure's distinct uses structural =, which
            ;; agrees with BEq on the value types we admit.
   "List.eraseDups" (list 'clojure.core/vec (list 'clojure.core/distinct (nth ca 2)))
            ;; sort: List.mergeSort α xs cmp → (sort cmp3 xs) where cmp3 is a
            ;; faithful 3-way comparator built from the kernel Bool comparator
            ;; (a≤b). Flatten a lambda comparator's two binders into a flat 2-arg
            ;; fn (mergeSort calls it (cmp a b)); a bare const (Nat.ble→<=) is
            ;; already flat.
   "List.mergeSort"
   (let [c-expr (nth args 2)
         cmp (if (e/lam? c-expr)
               (loop [e c-expr, ps [], ns names]
                 (if (and (< (count ps) 2) (e/lam? e))
                   (let [n (or (e/lam-name e) (str "p" (count ps)))]
                     (recur (e/lam-body e) (conj ps (symbol n)) (conj ns n)))
                   (list 'fn ps (a/ansatz->clj env e ns))))
               (nth ca 2))
         a (gensym "a") b (gensym "b")]
     (list 'clojure.core/sort
           (list 'fn [a b]
                 (list 'if (list cmp a b)
                       (list 'if (list cmp b a) 0 -1) 1))
           (nth ca 1)))))

(def ^:private builtin-lowerings
  "base-lowerings + the @[csimp]/@[implemented_by] tail-recursive runtime variants. Lean replaces
   `List.map`/`filter`/`filterMap` with their `*TR` forms for runtime efficiency; the optimizer can leave
   a proven-equal `*TR` head in the final term. Each TR variant has its base op's EXACT signature
   (α [β] f l), so it lowers identically — without these aliases ANY List-returning pipeline whose
   map/filter/filterMap got TR-lowered dies at codegen (ClassNotFoundException: List.mapTR)."
  (merge base-lowerings
         {"List.mapTR"       (base-lowerings "List.map")
          "List.filterTR"    (base-lowerings "List.filter")
          "List.filterMapTR" (base-lowerings "List.filterMap")}))

(def lowering-table
  "The SINGLE source of truth for runtime lowerings: the built-in vocabulary plus anything
   register-lowering! adds. install! registers exactly its keys into ansatz's codegen-registry, so
   there is no separate head-list to keep in sync (the old lowered-heads/case dual-maintenance)."
  (atom builtin-lowerings))

(defn- lower
  "Lower one runtime-vocabulary application head to Clojure (consulted by ansatz codegen through the
   codegen-registry seam for heads it doesn't know natively). Dispatches through lowering-table."
  [env expr names]
  (let [[head args] (e/get-app-fn-args expr)
        h (name/->string (e/const-name head))
        ca (mapv #(a/ansatz->clj env % names) args)]
    (if-let [f (get @lowering-table h)]
      (f env ca args names)
      (throw (ex-info (str "wandler.runtime/lower: unregistered head " h) {:head h})))))

(defn register-lowering!
  "Register a Clojure lowering for a runtime-vocabulary head — Lean's @[implemented_by] for a compiled
   op. `f` = (fn [env ca args names] → clj-form): ca = pre-compiled arg forms, args = raw Expr args.
   The open extension point: a vocabulary or user adds a lowering WITHOUT editing builtin-lowerings,
   and the head is auto-installed into ansatz's codegen-registry. Idempotent per head; returns head."
  [head f]
  (swap! lowering-table assoc head f)
  (swap! a/codegen-registry assoc head lower)
  head)

(defn install!
  "Point ansatz's codegen-registry at `lower` for every head in lowering-table (idempotent)."
  []
  (doseq [h (keys @lowering-table)]
    (swap! a/codegen-registry assoc h lower)))

(install!)
