(ns wandler.faq-plan-test
  "The bridge from a SEMIRING query to the CERTIFIED kernel optimizer (`wandler.faq-plan`): a counting/sum
   aggregating-join lowers to a kernel term, the optimizer applies its PROVEN Nat factorization laws (the
   pre-aggregated FAQ index `Map.foldl_join_sum_factor`) to a verified physical plan that EXECUTES — and
   agrees with the runtime `wandler.semiring` FAQ engine. ONE query, TWO engines, ONE answer.
   See [[programming-model-4-structures]], docs/PROGRAMMING_MODEL.md §13 step 1."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.rel-laws :as rl]
            [wandler.semiring :as sr]
            [wandler.faq-plan :as fp]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv) (km/install!) (rl/install!) (sr/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(def ^:private CUSTS [[1 10] [2 20] [3 30]])               ; [cid tier]
(def ^:private ORDS  [[1 100] [1 200] [2 50] [3 5] [3 5]]) ; [cid amount] — Σ amount = 360 over 5 matching pairs

(deftest semiring-query-rides-the-certified-optimizer
  (when (ready?)
    (let [L (fp/sum-join-term)
          r (fp/plan sr/counting L :sizes {7001 1000 7002 1000} :ndv {7002 3.0})]
      (testing "the counting semiring's FAQ certificate is EXECUTION-level (the optimizer's proven Nat laws)"
        (is (= :execution (:level (:certificate r))))
        (is (= "Map.foldl_join_sum_factor" (:factorization (:certificate r))))
        (is (= :counting (:semiring r))))
      (testing "the optimizer lowers + factorizes the query to a VERIFIED pre-aggregated physical plan"
        (is (true? (:verified? r)) "the physical plan is kernel-certified")
        (is (contains? (set (:rewrites r)) :pre-agg-index) "the pre-aggregated FAQ index fired")
        (is (= :in-memory-hash (get-in r [:physical :strategy]))))
      (testing "the certified kernel plan and the RUNTIME semiring engine agree on the answer"
        (is (= 360 (fp/run L (:term L) CUSTS ORDS)) "naive lowered term")
        (is (= 360 (fp/run L (:term r) CUSTS ORDS)) "the optimized/factorized plan executes to the same total")
        (is (= 360 (fp/srq-total CUSTS ORDS)) "the runtime sr FAQ engine totals the same")
        (is (= (fp/run L (:term r) CUSTS ORDS) (fp/srq-total CUSTS ORDS))
            "ONE query, TWO engines (certified kernel plan vs runtime FAQ), ONE result")))))

(deftest certificate-levels-are-distinct
  (when (ready?)
    (testing "the two certificate levels: existence = algebra (runtime soundness), counting = execution (the optimizer)"
      (is (= :algebra   (:level (sr/faq-certificate sr/existence))))
      (is (= :execution (:level (sr/faq-certificate sr/counting))))
      (is (nil? (sr/faq-certificate sr/tropical)) "tropical's certificate is not yet bundled"))))
