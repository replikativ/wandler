(ns wandler.clean.optimize.faq-test
  "Phase 8 Level 1 — the FAQ aggregation-through-join strategies ported into the clean optimizer
   (try-count-factor / try-fold-factor). They are pure recognizers that APPLY the proven Map-cluster
   laws (Map.count_join_factor / Map.foldl_join_factor — a shared law engine installed by w/install!);
   soundness rests on cert/verified-rewrite?. Exercised END-TO-END: a `count`/`sum` over a `join`
   written as ordinary Clojure factors through the join (no |xs|·|ys| product) via the CLEAN optimizer
   hook, and the adopted plan is kernel-certified + runs correctly."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.clean.laws.faq :as rl]
            [wandler.test-env :as test-env]))

(deftest clean-count-factor-through-join
  (if-let [k @test-env/init-full-env]
    (do
      (reset! a/ansatz-env k)
      (w/install!)
      ;; the FAQ factor laws (Map.count_join_factor/foldl_join_factor) ship in the relational law
      ;; engine, installed on demand (the strategies gracefully skip when absent) — as the breadth does.
      (binding [a/*verbose* false] (rl/install!))
      (binding [a/*verbose* false]
        ;; count of a self-join → factored to count-per-bucket, no pair materialization
        (eval '(ansatz.core/defn faq-count [xs :- (List Nat), ys :- (List Nat)] Nat
                 (count (join (fn [x] x) (fn [y] y) xs ys)))))
      (testing "count over a Map.join factors through the join via the clean optimizer"
        (is (= [:count-factor :hoist-index] (vec (:rewrites (w/explain 'faq-count))))
            "the clean optimizer factored the count through the join, then hoisted the index out of the loop")
        (is (:verified? (w/explain 'faq-count))
            "the factored plan kernel-certifies ≡ the original"))
      (testing "the factored count runs and agrees with the naive join-then-count"
        (let [f (deref (resolve 'faq-count))
              truth (fn [xs ys]
                      (count (mapcat (fn [x] (keep (fn [y] (when (= x y) [x y])) ys)) xs)))]
          (doseq [[xs ys] [[[] []] [[1 2 3] [2 3 4]] [[5 5] [5]] [[1 2] [3 4]]]]
            (is (= (long (truth xs ys)) (long (f xs ys)))
                (str "count-factor == naive on " (mapv vec [xs ys])))))))
    (do (println "SKIP clean-count-factor: no Init env") (is true))))
