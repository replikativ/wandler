;; A verified SOAC planner for Clojure reducer pipelines.
;;
;; This is the "query planner for transducers" vertical: a pipeline is captured
;; as a logical IR — a producer, a chain of transforms, and a consumer — exactly
;; the shape datahike/stratum use for queries and Futhark/raster use for array
;; SOACs (second-order array combinators). We then run plan→plan rewrite passes.
;;
;; The difference from those systems: every rewrite emits a kernel-checked proof
;; that the rewritten plan is denotationally equal to the original. Datahike,
;; stratum, GHC, and Futhark *trust* their fusion rules; ours are machine-checked
;; against Lean-core list lemmas (no Mathlib).
;;
;; This first vertical implements **map-into-fold (SOAC) fusion**: a `map g`
;; feeding a `foldl f` collapses to `foldl (fun acc x => f acc (g x))`, removing
;; the intermediate mapped list. The justification is `List.foldl_map`.
;;
;; Properties we extract from captured functions:
;;   - purity / totality  — FREE: a `certified-fn`'s kernel term is a CIC term.
;;   - element types       — inferred from the kernel term's type.
;;   - the fusion law      — proven per rewrite.
;;
;; The kernel `Value`/list terms are the *reasoning* representation; execution
;; runs on native Clojure (`reduce` over the fused step) — never on kernel terms.

(ns wandler.reducers.plan
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [wandler.reducers :as r]
            [wandler.refine :as refine])
  (:import [ansatz.kernel Env Expr TypeChecker]))

;; ============================================================
;; IR — a plan is a producer, transforms, and a consumer
;; ============================================================

(defrecord Plan [producer transforms consumer proofs])

(defn producer
  "A source over element type `elem` (a kernel type Expr, for proofs)."
  [elem]
  {:elem elem})

(defn map-step
  "A `map` transform from a `certified-fn` (carries :kernel-term + :runtime)."
  [cfn]
  {:op :map :fn cfn})

(defn fold-consumer
  "A fold consumer: `step` is a `certified-fn` of kernel type `γ → β → γ`
   (e.g. `Nat.add`), `init`/`runtime-init` the seed."
  [step init]
  {:op :fold :step step :init init})

(defn plan
  "Assemble a SOAC plan: producer → transforms → consumer."
  [producer transforms consumer]
  (->Plan producer (vec transforms) consumer []))

;; ============================================================
;; Kernel helpers (type/universe extraction — mirrors wandler.reducers)
;; ============================================================

(defn- nm [s] (name/from-string s))

(defn- cert-term
  "The kernel term of a certified-fn (explicit :kernel-term, or a ground const
   from :name)."
  [cfn]
  (let [cert (r/certification cfn)
        kt (:kernel-term cert)]
    (cond
      (instance? Expr kt) kt
      (and kt (or (symbol? kt) (string? kt))) (e/const' (nm (str kt)) [])
      (:name cert) (e/const' (nm (str (:name cert))) [])
      :else (throw (ex-info "certified-fn has no resolvable kernel term" {:cfn cfn})))))

(defn- sort-level-of [^TypeChecker tc t] (e/sort-level (.inferType tc t)))
(defn- type-universe [^TypeChecker tc t] (lvl/succ-pred (sort-level-of tc t)))
(defn- arrow-dom [t] (e/forall-type t))
(defn- arrow-cod [t] (e/forall-body t))

;; ============================================================
;; Property extraction (the `annotate` pass)
;; ============================================================

(defn- analyze-fn
  "Static properties of a captured function. Purity/totality are guaranteed by
   construction (a certified-fn's kernel side is a CIC term)."
  [^TypeChecker tc cfn]
  (let [term (cert-term cfn)
        ty (.inferType tc term)]
    {:pure? true :total? true
     :kernel-term term
     :type ty}))

(defn analyze
  "Annotate a plan with static properties of its captured functions."
  [^Env kernel-env ^Plan p]
  (let [tc (TypeChecker. kernel-env)]
    (assoc p :analysis
           {:transforms (mapv (fn [t]
                                (cond-> {:op (:op t)}
                                  (:fn t) (assoc :fn (analyze-fn tc (:fn t)))))
                              (:transforms p))
            :consumer (cond-> {:op (:op (:consumer p))}
                        (:step (:consumer p)) (assoc :step (analyze-fn tc (:step (:consumer p)))))})))

;; ============================================================
;; map-into-fold (SOAC) fusion — the verified rewrite
;; ============================================================

(defn- foldl-map-proof
  "Kernel-checked `List.foldl_map` instance: proof that
   `foldl f init (map g l) = foldl (fun acc x => f acc (g x)) init l`,
   plus the fused step term and runtime.  `g` is the map fn (α→β); `f` the fold
   step (γ→β→γ)."
  [^TypeChecker tc g-cfn f-cfn]
  (let [g (cert-term g-cfn)
        f (cert-term f-cfn)
        gt (.inferType tc g)
        ft (.inferType tc f)
        a (arrow-dom gt) b (arrow-cod gt)            ; g : α → β
        c (arrow-dom ft)                              ; f : γ → β → γ
        ua (type-universe tc a) ub (type-universe tc b) uc (type-universe tc c)
        proof (e/app* (e/const' (nm "List.foldl_map") [ua ub uc]) a b c g f)
        thm-type (.check tc proof)                   ; STRICT: re-checks every app arg
        ;; fused step kernel: λ (acc:γ)(x:α). f acc (g x)
        fused (e/lam "acc" c
                     (e/lam "x" a
                            (e/app* f (e/bvar 1) (e/app g (e/bvar 0)))
                            :default)
                     :default)
        g-rt (:runtime (r/certification g-cfn))
        f-rt (:runtime (r/certification f-cfn))]
    {:theorem "List.foldl_map"
     :proof proof
     :theorem-type thm-type
     :fused-step fused
     :fused-runtime (fn [acc x] (f-rt acc (g-rt x)))}))

(defn fuse
  "Fuse trailing `map` transforms into the fold consumer, one at a time, each
   justified by a kernel-checked `List.foldl_map` proof. Returns a Plan whose
   consumer carries the fused step (and runtime) and whose `:proofs` records each
   checked fusion. Only `map`/`fold` are fused; a non-map transform stops fusion."
  ([^Env kernel-env p] (fuse kernel-env p {}))
  ([^Env kernel-env p {:keys [fuel] :or {fuel 50000000}}]
   (let [tc (doto (TypeChecker. kernel-env) (.setFuel (long fuel)))]
     (when-not (= :fold (:op (:consumer p)))
       (throw (ex-info "fuse currently supports a fold consumer" {:consumer (:consumer p)})))
     (loop [transforms (:transforms p)
            step-cfn (:step (:consumer p))
            proofs []]
       (let [last-t (peek transforms)]
         (if (and last-t (= :map (:op last-t)))
           (let [{:keys [proof theorem theorem-type fused-step fused-runtime]}
                 (foldl-map-proof tc (:fn last-t) step-cfn)
                 ;; the fused step becomes a new certified-fn (kernel term + runtime)
                 fused-cfn (r/certified-fn {:name 'fused-fold-step
                                            :kernel-term fused-step
                                            :runtime fused-runtime})]
             (recur (pop transforms)
                    fused-cfn
                    (conj proofs {:rule :map-fold-fusion
                                  :theorem theorem
                                  :proof proof
                                  :theorem-type theorem-type
                                  :kernel-checked? true})))
           (-> p
               (assoc :transforms transforms)
               (assoc-in [:consumer :step] step-cfn)
               (assoc :proofs proofs))))))))

;; ============================================================
;; Dependent-type filter elimination — the verified rewrite
;; ============================================================

(defn eliminate-filters
  "Drop `filter` transforms whose predicate is provably CONSTANT over the current
   element type (`ansatz.reducers.predicate`). An always-true filter is removed
   (its check is redundant — proven); an always-false filter marks the plan
   `:empty?` (the pipeline can yield nothing). The element type is tracked through
   preceding `map`s (each map's codomain). Each elimination records a kernel-checked
   proof in `:proofs`."
  [^Env kernel-env ^Plan p]
  (let [tc (TypeChecker. kernel-env)]
    (loop [in (:transforms p)
           elem (:elem (:producer p))
           out []
           proofs (:proofs p)
           emptied? false]
      (if (or emptied? (empty? in))
        (-> p (assoc :transforms out) (assoc :proofs proofs) (assoc :empty? emptied?))
        (let [t (first in)]
          (case (:op t)
            :map (recur (rest in) (arrow-cod (.inferType tc (cert-term (:fn t))))
                        (conj out t) proofs false)
            :filter (if-let [res (refine/prove-const kernel-env (cert-term (:fn t)) elem)]
                      (recur (rest in) elem out
                             (conj proofs {:rule (if (:value res)
                                                   :filter-elim-always-true
                                                   :filter-elim-always-false)
                                           :theorem "predicate-constant"
                                           :proof (:proof res)
                                           :theorem-type (:theorem-type res)
                                           :kernel-checked? true})
                             (not (:value res)))           ; always-false ⇒ empty
                      (recur (rest in) elem (conj out t) proofs false))
            (recur (rest in) elem (conj out t) proofs false)))))))

;; ============================================================
;; Lowering + execution (native Clojure — never the kernel terms)
;; ============================================================

(defn run
  "Execute a (fused) plan over a native Clojure collection. Remaining transforms
   compile to an ordinary transducer; the fold consumer's step runs as a native
   `reduce`."
  [^Plan p coll]
  (let [step (:runtime (r/certification (:step (:consumer p))))
        init (:init (:consumer p))]
    (if (:empty? p)
      init                                          ; an always-false filter was proven away
      (let [xf (apply comp (map (fn [t]
                                  (case (:op t)
                                    :map (clojure.core/map (:runtime (r/certification (:fn t))))
                                    :filter (clojure.core/filter (:runtime (r/certification (:fn t))))))
                                (:transforms p)))]
        (transduce xf (completing step) init coll)))))

(defn explain
  "A data summary: the transforms before/after, the consumer, and the
   kernel-checked fusion proofs."
  [^Plan p]
  {:transforms (mapv :op (:transforms p))
   :consumer (:op (:consumer p))
   :proofs (mapv (fn [pr]
                   {:rule (:rule pr)
                    :theorem (:theorem pr)
                    :kernel-checked? (:kernel-checked? pr)
                    :theorem-type (some-> (:theorem-type pr) e/->string)})
                 (:proofs p))})
