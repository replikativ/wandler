(ns ansatz.float-literal-test
  "Item E — Float-literal codegen. A Clojure double in a verified body now elaborates to
   `OfScientific.ofScientific Float inst m s e` (m × 10^±e — Float is COMPUTABLE, native
   double; Real is non-computable, for proofs only), and lowers back to a double in codegen.
   This unlocks Float map/FOLD pipelines (the fold init `0.0` previously failed with
   \"Cannot compile: 0.0\") and makes the unboxed double[] fold/map backend reachable.
   (Float comparison PREDICATES for filter remain open — Float.lt is Prop, not Bool.)
   See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [ansatz.collections :as coll]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- kernel-checks?
  "AUTHORITATIVE: re-typecheck the registered declaration's value against its type via
   check-constant, under a fresh name (not the lenient inferType)."
  [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (try
      (env/check-constant
       (a/env)
       (env/mk-def (name/from-string (str "__chk_" nm))
                   (env/ci-level-params ci) (env/ci-type ci) (env/ci-value ci))
       50000000)
      true (catch Throwable _ false))))

(deftest float-literals-compile-and-run
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        ;; a bare Float literal in a body
        (eval '(ansatz.core/defn f-lit [x :- Float] Float (add Float x 2.5)))
        ;; Float literal as fold init + Float map → fused; runs unboxed over double[]
        (eval '(ansatz.core/defn f-sumdbl [xs :- (List Float)] Float
                 (reduce (fn [acc x] (add Float acc x)) 0.0
                         (mapv (fn [x] (mul Float x 2.0)) xs)))))
      ;; authoritative kernel certification
      (is (true? (kernel-checks? "f-lit"))    "Float literal term certifies")
      (is (true? (kernel-checks? "f-sumdbl")) "Float fold+literal pipeline certifies")
      ;; runtime: literal value
      (is (== 4.5 ((resolve 'f-lit) 2.0)) "x + 2.5")
      ;; 2*(1+2+3) = 12.0, identical for double[] (unboxed) and vector
      (is (== 12.0 ((resolve 'f-sumdbl) (double-array [1.0 2.0 3.0]))) "fold over double[] unboxed")
      (is (== 12.0 ((resolve 'f-sumdbl) [1.0 2.0 3.0])) "vector input still works"))
    (do (println "SKIP float-literals-compile-and-run: no Init env") (is true))))
