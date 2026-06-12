(ns wandler.nested-proj-test
  "Regression for #56: a record field PROJECTION inside an `if`/`cond` within a map/reduce
   lambda. The bug was a FRONTEND one — the codomain β of a lambda whose body is an `if`
   (recursor) came back as the UN-reduced motive application `(λ_.T) cond`, which still
   mentions the lambda's bound var; placed in List.map's β type-arg position (outside the
   lambda) that bvar re-bound to the WRONG outer param, so check-constant saw a projection on
   the outer List value (\"Projection on non-structure\"). Fix: whnf-ty the extracted codomain
   so it reduces to T. See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.stdlib :as std]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- malli? [] (try (require 'malli.core) true (catch Throwable _ false)))

(defn- kernel-checks? [nm]
  (when-let [ci (kenv/lookup (a/env) (name/from-string nm))]
    (try (kenv/check-constant (a/env)
           (kenv/mk-def (name/from-string (str "__c_" nm))
                        (kenv/ci-level-params ci) (kenv/ci-type ci) (kenv/ci-value ci)) 50000000)
         true (catch Throwable _ false))))

(deftest projection-inside-if-in-map-lambda
  (if (and @test-env/init-full-env (malli?))
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (std/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record Order [:map [:id [:int {:min 0}]] [:amount :double]]))
        ;; proj in the if-CONDITION (the exact failing case)
        (eval '(ansatz.core/defn np-cond [os :- (List Order)] (List Bool)
                 (mapv (fn [o] (if (< (:amount o) 80.0) true false)) os)))
        ;; proj in BOTH condition and branch
        (eval '(ansatz.core/defn np-both [os :- (List Order)] (List Float)
                 (mapv (fn [o] (if (< (:amount o) 80.0) (:amount o) 0.0)) os)))
        ;; cond + a derived value in a branch
        (eval '(ansatz.core/defn np-cond3 [os :- (List Order)] (List Float)
                 (mapv (fn [o] (cond (< (:amount o) 80.0) (mul Float (:amount o) 0.9) :else (:amount o))) os))))
      ;; all three KERNEL-VERIFY (the bug was a check-constant failure)
      (is (true? (kernel-checks? "np-cond"))  "proj-in-if-condition certifies")
      (is (true? (kernel-checks? "np-both"))  "proj-in-condition-and-branch certifies")
      (is (true? (kernel-checks? "np-cond3")) "cond with derived branch certifies")
      ;; and run correctly
      (let [os [{:id 1 :amount 100.0} {:id 2 :amount 50.0}]]
        (is (= [false true]  ((resolve 'np-cond) os)))
        (is (= [0.0 50.0]    ((resolve 'np-both) os)))
        (is (= [100.0 45.0]  ((resolve 'np-cond3) os)))))
    (do (println "SKIP projection-inside-if-in-map-lambda: no Init env / malli") (is true))))
