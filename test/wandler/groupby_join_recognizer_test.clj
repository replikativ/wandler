(ns wandler.groupby-join-recognizer-test
  "#184 end-to-end: the optimizer recognizer (try-groupby-reduce-join) fires on a plain `a/defn`
   group-by-over-join analytics query, certifies the factorization (Map.groupby_reduce_join_factor),
   eliminates the Map.join, AND the compiled fn runs + matches the brute-force answer. This is the
   cross-engine GROUP BY analytics shape going from correct-but-unoptimized to OPTIMAL."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.optimize.cost :as cost]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (wc/install!) (wc/install-laws!)))   ;; install-laws! now pulls gbj
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))
(defn- malli? [] (try (require 'malli.core) true (catch Throwable _ false)))

(deftest groupby-over-join-factorizes-and-runs
  (when (and (ready?) (malli?))
    (testing "map (reduce+0 ∘ amount) (vals (group-by region (join custs orders))) factorizes"
      (eval (list (symbol "malli.core" "=>") 'revByRegion
                  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]
                             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]]
                   [:sequential :int]]))
      (eval '(ansatz.core/defn revByRegion [custs orders]
               (map (fn [g] (reduce + 0 (map (fn [[c o]] (:amount o)) g)))
                    (vals (group-by (fn [[c o]] (:region c))
                                    (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders))))))
      (let [term (wc/term 'revByRegion)
            rewrites (:rewrites (wc/explain 'revByRegion))]
        (is (contains? (set rewrites) :groupby-reduce-join)
            (str "recognizer fired; rewrites = " (vec rewrites)))
        (is (not (cost/mentions-const? term "Map.join"))
            "the Map.join node is eliminated (product never materialized)")
        (is (:verified? (wc/explain 'revByRegion)) "the factorization is kernel-certified"))
      (testing "the factored fn RUNS and matches the brute-force per-region revenue"
        (let [NC 40 NR 5 NO 600
              custs  (vec (for [i (range NC)] {:cid i :region (mod i NR)}))
              orders (vec (for [i (range NO)] {:cid (mod i NC) :amount (inc (mod i 13))}))
              cust-region (into {} (map (juxt :cid :region)) custs)
              brute (->> orders
                         (keep (fn [o] (when-let [r (cust-region (:cid o))] [r (:amount o)])))
                         (reduce (fn [m [r v]] (update m r (fnil + 0) v)) {}))
              got ((deref (resolve 'revByRegion)) custs orders)]
          (is (= (sort (map long got)) (sort (vals brute)))
              (str "factored " (sort (map long got)) " vs brute " (sort (vals brute)))))))))
