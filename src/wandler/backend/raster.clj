(ns wandler.backend.raster
  "OPTIONAL chunked-array backend (#76, docs/PHYSICAL_PLANNER.md) — lowers recognized NUMERICAL pipeline
   shapes over Float arrays to raster's unboxed SIMD kernels (raster.par). Loads ONLY when raster is on
   the classpath (the :raster alias); `register!` plugs it into wandler.exec.physical's :array seam. An
   unrecognized shape DECLINES (nil) → the eager Clojure realization runs (result-equal). The kernel
   proof (the verified fold/map term) is the certificate; raster just executes it faster.

   Two recognition tiers:
     v1 ready-made ops (cheap reductions, memory-bound — correct but no SIMD win over C2):
       foldl(+,0, xs)               → (par/sum (double-array xs))
       foldl(+,0, map(λx.x*x, xs))  → (par/dot-product da da)   [= Σ x², L2-norm²]
     GENERAL deftm path (the real win — COMPUTE-bound custom kernels):
       foldl(+,0, map(λx. <Float poly/expr>, xs)) → a raster `deftm`+`compile-aot` SIMD/parallel kernel
       that INLINES the per-element λ body into a `reduce!` over a double[]. Beats single-thread C2 by
       ~4× on a compute-heavy kernel (e.g. Σ x^16 over 2M: clojure 10.4ms vs raster 2.6ms)."
  (:require [ansatz.codegen :as cg]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [raster.core :refer [deftm broadcast reduce!]]
            [raster.compiler.pipeline :as rp]
            [raster.par]
            [wandler.exec.physical :as phys]))

(defn- mentions? [t s]
  (cond (nil? t)      false
        (e/const? t)  (= s (name/->string (e/const-name t)))
        (e/app? t)    (or (mentions? (e/app-fn t) s) (mentions? (e/app-arg t) s))
        (e/lam? t)    (mentions? (e/lam-body t) s)
        :else false))

(defn- add-step?
  "Does the foldl step ADD over Float? — a bare Float.add const or a fused λ mentioning Float.add/HAdd."
  [fn-term]
  (or (mentions? fn-term "Float.add") (mentions? fn-term "HAdd.hAdd")))

(defn- square-map?
  "Is the map fn `(λx. Float.mul x x)` — squaring its argument?"
  [fn-term]
  (and (e/lam? fn-term)
       (let [[h args] (e/get-app-fn-args (e/lam-body fn-term))]
         (and (e/const? h) (= "Float.mul" (name/->string (e/const-name h)))
              (= 2 (count args))
              (every? #(and (e/bvar? %) (zero? (e/bvar-idx %))) args)))))

(def ^:private float-ops
  "The Float ops raster's deftm body can compile (→ binary * + - /)."
  #{"Float.mul" "Float.add" "Float.sub" "Float.div"})

(defn- mentions-any-float-op? [t]
  (cond (e/const? t) (contains? float-ops (name/->string (e/const-name t)))
        (e/app? t)   (or (mentions-any-float-op? (e/app-fn t)) (mentions-any-float-op? (e/app-arg t)))
        (e/lam? t)   (mentions-any-float-op? (e/lam-body t))
        :else        false))

(defn- float-kernel?
  "Is `fn-term` a CLOSED `(λx. <body>)` whose body uses only Float arithmetic (float-ops) and its
   argument — i.e. inlinable into a raster deftm reduce! body? Such a λ lowers to a SIMD kernel."
  [fn-term]
  (and (e/lam? fn-term)
       (letfn [(ok? [t]
                 (cond
                   (e/bvar? t)  true
                   (e/const? t) (contains? float-ops (name/->string (e/const-name t)))
                   (e/app? t)   (and (ok? (e/app-fn t)) (ok? (e/app-arg t)))
                   :else        false))]
         (let [b (e/lam-body fn-term)]
           ;; require at least one Float op (else it's identity/constant — not worth a kernel)
           (and (ok? b) (mentions-any-float-op? b))))))

(defn compile-sum-kernel
  "Compile a per-element Clojure form `elem-form` (in terms of the symbol `a`) into an AOT raster kernel
   `(fn [^doubles da] Double)` computing `Σ elem-form` over the array. The form is inlined into a `deftm`
   `reduce!` body and compiled via raster's pipeline (SOAC-fused SIMD + morsel parallelism). Compiled
   once per plan at routing time — the heavy step that the per-call execution then amortizes."
  [elem-form]
  (let [g    (gensym "wkernel")
        form (list 'deftm g ['a :- '(Array double)] :- 'Double
                   (list 'reduce! ['acc 0.0] ['a] (list '+ 'acc elem-form)))]
    (binding [*ns* (the-ns 'wandler.backend.raster)] (eval form))
    (rp/compile-aot (ns-resolve 'wandler.backend.raster g))))

(defn raster-array-form
  "The :array backend fn (env plan names) → a Clojure form running the plan via raster, or nil to
   decline (→ eager fallback). Matches Float reductions: the canonical ready-made ops, then the GENERAL
   compute-kernel path (any inlinable Float λ → deftm+compile-aot SIMD kernel)."
  [env plan names]
  (when (= :foldl (:op plan))
    (let [inp (:input plan)]
      (cond
        ;; Σ xs  (Float sum over the source list)
        (and (add-step? (:fn plan)) (= :source (:op inp)))
        (list 'raster.par/sum (list 'clojure.core/double-array (cg/ansatz->clj env (:term inp) names)))

        ;; Σ x²  →  dot-product(da, da)  (ready-made op)
        (and (add-step? (:fn plan)) (= :map (:op inp)) (square-map? (:fn inp)) (= :source (:op (:input inp))))
        (let [da (gensym "da")]
          (list 'clojure.core/let
                [da (list 'clojure.core/double-array (cg/ansatz->clj env (:term (:input inp)) names))]
                (list 'raster.par/dot-product da da)))

        ;; GENERAL: Σ (g x) over the source, g an inlinable Float kernel → a compiled raster deftm kernel.
        ;; Inline g's body (bvar 0 → `a`) into a reduce!, AOT-compile, and call the kernel over double[].
        (and (add-step? (:fn plan)) (= :map (:op inp)) (float-kernel? (:fn inp)) (= :source (:op (:input inp))))
        (let [elem (cg/ansatz->clj env (e/lam-body (:fn inp)) ["a"])  ; per-element body in `a`
              kf   (compile-sum-kernel elem)
              vsym (gensym "rk")
              _    (intern 'wandler.backend.raster vsym kf)
              src  (cg/ansatz->clj env (:term (:input inp)) names)]
          (list (symbol "wandler.backend.raster" (str vsym))
                (list 'clojure.core/double-array src)))

        :else nil))))

;; raster's advertised cost for a recognized Float reduction: a SIMD/parallel kernel over a double[].
;; A FIXED setup (box→double[] copy + thread fork + kernel dispatch) PLUS a low per-element term
;; (measured ~4× over single-thread C2 on compute-heavy kernels). So cost = setup + eager/speedup —
;; which makes the decision WORKLOAD-SIZE-SENSITIVE: choose-cost-form picks raster only when the eager
;; cost (∝ input size) is large enough to amortize the setup, i.e. above a crossover size. A tiny /
;; bounded source stays in Clojure; a large one goes to raster. (The eager cost is size-aware exactly
;; when batch-run-array is given the real source size — a measured size for a stream is the JIT path.)
(def ^:private raster-speedup 3.5)
(def ^:private raster-setup 3000.0)   ; ~element-equivalents of fixed overhead; the crossover knob
(defn- raster-cost [_plan eager-cost] (+ raster-setup (/ (double eager-cost) raster-speedup)))

(defn register!
  "Register the raster backend as a COST-BASED execution backend (#76 / COST_MODEL_REDESIGN B2): it
   recognizes Float reductions and ADVERTISES its cost, so the planner's choose-cost-form pushes down
   iff raster is actually cheaper than the eager Clojure realization. Idempotent (clears first)."
  []
  (phys/clear-cost-backends!)
  (phys/register-cost-backend! {:name :raster :lower raster-array-form :cost raster-cost})
  :registered)
