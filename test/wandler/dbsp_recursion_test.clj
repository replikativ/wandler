(ns wandler.dbsp-recursion-test
  "Recursive queries / semi-naive (DBSP §8–9): the certified body-increment `Recursion.body_incr`
   (F(R⊎Δ)=F R⊎step Δ) and an executed transitive-closure fixpoint computed NAIVELY and SEMI-NAIVELY,
   agreeing — the value-level cycle rule that justifies semi-naive datalog (../datahike). See
   ansatz.dbsp-recursion."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.exec.dbsp-recursion :as dr]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]))

(defn- nm [s] (name/from-string s))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (dr/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest recursion-laws-present-and-verified
  (when (ready?)
    (testing "the cycle/semi-naive laws are admitted (kernel check-constant'd)"
      (doseq [n ["Recursion.body_incr" "Cycle.iter" "Cycle.iter_fixpoint_stable"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present"))))))

(deftest transitive-closure-naive-equals-seminaive
  (when (ready?)
    (testing "transitive closure: step(R) = R ⋈ E (linear) — naive fixpoint = semi-naive (delta-driven)"
      (let [edges #{[1 2] [2 3] [3 4] [2 5]}                ; a small DAG
            ;; step: derive [a c] for [a b]∈R and [b c]∈E (join on R.2 = E.1) — a LINEAR step
            step (fn [R] (for [[a b] R [c d] edges :when (= b c)] [a d]))
            expected #{[1 2] [2 3] [3 4] [2 5]              ; base edges
                       [1 3] [2 4] [1 5]                    ; 2-hop
                       [1 4]}                               ; 3-hop
            naive (dr/naive-fixpoint step edges)
            semi  (dr/seminaive-fixpoint step edges)]
        (is (= expected naive) "naive transitive closure")
        (is (= naive semi) "semi-naive (only new tuples each round) computes the SAME fixpoint")))))
