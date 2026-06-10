(ns ansatz.int-faithfulness-test
  "Phase 1 faithfulness: bare arithmetic/comparison operators infer their type from the
   operands (Clojure-faithful), so Int is SIGNED — `(- x y)` is `Int.sub` (not the
   truncating `Nat.sub`) — while Nat keeps its truncating semantics. Int literals coerce
   to the type the context needs. See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [ansatz.collections :as coll]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- kernel-checks? [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (try (env/check-constant
          (a/env)
          (env/mk-def (name/from-string (str "__chk_" nm))
                      (env/ci-level-params ci) (env/ci-type ci) (env/ci-value ci))
          50000000)
         true (catch Throwable _ false))))

(deftest int-is-signed-nat-truncates
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn i-sub [x :- Int, y :- Int] Int (- x y)))     ; signed
        (eval '(ansatz.core/defn i-add [x :- Int, y :- Int] Int (+ x y)))     ; bare + infers Int
        (eval '(ansatz.core/defn n-sub [x :- Nat, y :- Nat] Nat (- x y)))     ; truncating
        (eval '(ansatz.core/defn i-lt  [x :- Int, y :- Int] Bool (< x y))))   ; Int Bool comparison
      ;; certify
      (is (true? (kernel-checks? "i-sub")) "signed Int.sub certifies")
      (is (true? (kernel-checks? "i-add")) "bare + over Int certifies")
      (is (true? (kernel-checks? "n-sub")) "Nat.sub certifies")
      (is (true? (kernel-checks? "i-lt"))  "Int comparison (decide-bridge) certifies")
      ;; runtime semantics — the faithfulness payoff (curried; resolve eval'd vars)
      (is (= -2 (((resolve 'i-sub) 3) 5)) "Int: 3 - 5 = -2 (SIGNED, not truncated)")
      (is (=  7 (((resolve 'i-add) 10) -3)) "Int: 10 + (-3) = 7")
      (is (=  0 (((resolve 'n-sub) 3) 5)) "Nat: 3 - 5 = 0 (truncates, correct for Nat)")
      (is (true?  (((resolve 'i-lt) 3) 5)) "Int: 3 < 5")
      (is (false? (((resolve 'i-lt) 5) 3)) "Int: not 5 < 3"))
    (do (println "SKIP int-is-signed-nat-truncates: no Init env") (is true))))
