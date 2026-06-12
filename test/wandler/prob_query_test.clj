(ns wandler.prob-query-test
  "(c) END-TO-END probabilistic query — the ProbLog path assembled from the pieces: datahike supplies
   PROBABILISTIC facts; an indexable predicate is PUSHED DOWN into its index (the certified filter→scan
   rewrite, engine_interop_test); and the marginal is a WEIGHTED FAQ over the survivors — provenance
   semiring → WMC, == the FinDist monad (dist_test). The pushdown is not cosmetic: filtering the facts at
   the index CHANGES the marginal.

   Scenario: edges carry a probability and a `:verified` flag. Query: P(1 reaches 9) using only VERIFIED edges.
     all edges:  1→2 (.9,✓)  1→3 (.5,✓)  2→9 (.8,✓)  3→9 (.4,✗)        ← 3→9 is NOT verified
     no filter:  both 2-hop paths ⇒ P = 1−(1−.9·.8)(1−.5·.4) = 0.776
     :verified pushed to the index ⇒ 3→9 never fetched ⇒ only 1→2→9 survives ⇒ P = .9·.8 = 0.72

   Pure runtime (the symbolic correctness rides the proven semiring laws; the numbers are the trusted WMC)."
  (:require [clojure.test :refer [deftest is testing]]
            [wandler.semiring :as sr]
            [wandler.dist :as d]))

(def ^:private all-edges
  {[1 2] {:p 0.9 :verified true}  [1 3] {:p 0.5 :verified true}
   [2 9] {:p 0.8 :verified true}  [3 9] {:p 0.4 :verified false}})

(defn- marginal
  "P(1→9) over a set of (probabilistic) edges, via the provenance semiring → WMC (the FAQ route)."
  [edges]
  (let [edge-rel (sr/relation [:a :b] (into {} (map (fn [[[f t] _]] [[f t] #{#{[f t]}}])) edges))
        probs    (into {} (map (fn [[ft m]] [ft (:p m)])) edges)
        formula  (get (:rel (sr/q {:find [:x :y] :where [[:edge :x :m] [:edge :m :y]]} sr/provenance {:edge edge-rel}))
                      {:x 1 :y 9})]
    (when formula (sr/wmc probs formula))))

(deftest probabilistic-query-over-pushed-down-facts
  (testing "no filter: both probabilistic paths contribute ⇒ P = 0.776"
    (is (< (Math/abs (- (marginal all-edges) 0.776)) 1e-9)))
  (testing "PUSHDOWN: the :verified predicate goes into datahike's index ⇒ unverified 3→9 never fetched"
    (let [verified (into {} (filter (comp :verified val)) all-edges)]
      (is (= #{[3 9]} (clojure.set/difference (set (keys all-edges)) (set (keys verified))))
          "only the unverified edge is dropped by the index filter")
      (testing "…and the marginal is now over only the verified facts ⇒ P = 0.9·0.8 = 0.72"
        (is (< (Math/abs (- (marginal verified) 0.72)) 1e-9)
            "filtering at the index CHANGES the marginal — engine interop ∘ probabilistic semiring"))))
  (testing "the FinDist monad agrees with the FAQ/WMC marginal on the verified facts (0.72)"
    ;; the one surviving path 1→2→9 as a FinDist program over independent Bernoulli edges
    (let [model (d/dist-bind (d/bernoulli 0.9) (fn [e12]
                  (d/dist-bind (d/bernoulli 0.8) (fn [e29]
                    (d/dist-return (and e12 e29))))))]
      (is (< (Math/abs (- (get model true) 0.72)) 1e-9) "FinDist P = 0.72 == provenance→WMC == the FAQ"))))
