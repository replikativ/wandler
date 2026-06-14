(ns wandler.backend.raster
  "OPTIONAL chunked-array backend (#76, docs/PHYSICAL_PLANNER.md) — lowers recognized NUMERICAL pipeline
   shapes over Float arrays to raster's unboxed SIMD kernels (raster.par). Loads ONLY when raster is on
   the classpath (the :raster alias); `register!` plugs it into wandler.exec.physical's :array seam. An
   unrecognized shape DECLINES (nil) → the eager Clojure realization runs (result-equal). The kernel
   proof (the verified fold/map term) is the certificate; raster just executes it faster.

   v1 shapes (the canonical reductions, demonstrating the SIMD win):
     foldl(+,0, xs)               → (par/sum (double-array xs))
     foldl(+,0, map(λx.x*x, xs))  → (par/dot-product da da)   [= Σ x², L2-norm²]
   General λ kernels via raster deftm + compile-aot are the follow-up."
  (:require [ansatz.codegen :as cg]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
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

(defn raster-array-form
  "The :array backend fn (env plan names) → a Clojure form running the plan via raster, or nil to
   decline (→ eager fallback). Matches the canonical Float reductions."
  [env plan names]
  (when (= :foldl (:op plan))
    (let [inp (:input plan)]
      (cond
        ;; Σ xs  (Float sum over the source list)
        (and (add-step? (:fn plan)) (= :source (:op inp)))
        (list 'raster.par/sum (list 'clojure.core/double-array (cg/ansatz->clj env (:term inp) names)))

        ;; Σ x²  →  dot-product(da, da)
        (and (add-step? (:fn plan)) (= :map (:op inp)) (square-map? (:fn inp)) (= :source (:op (:input inp))))
        (let [da (gensym "da")]
          (list 'clojure.core/let
                [da (list 'clojure.core/double-array (cg/ansatz->clj env (:term (:input inp)) names))]
                (list 'raster.par/dot-product da da)))

        :else nil))))

(defn register!
  "Register the raster array backend into the :array physical seam. Clears first so re-registration is
   idempotent. After this, `(mode/execute … :physical :array)` over a recognized Float reduction runs
   on raster's SIMD kernel; other shapes fall back to the eager realization."
  []
  (phys/clear-array-backends!)
  (phys/register-array-backend! raster-array-form)
  :registered)
