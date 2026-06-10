(ns ansatz.correlated-query-test
  "STEP 1 — why WMC is necessary (not just a faster sum). When a fact appears in MULTIPLE derivation paths
   (a shared variable / correlation), the naïve `(prob,+,×)` product DOUBLE-COUNTS it and gives the wrong
   marginal. WMC over the provenance formula is exact because the formula records the sharing.

   Graph: 1→2→{3,4}→9. The two 3-hop paths 1-2-3-9 and 1-2-4-9 SHARE the edge 1→2.
     provenance formula = (e12 ∧ e23 ∧ e39) ∨ (e12 ∧ e24 ∧ e49)         ← e12 shared
     with every edge present w.p. 0.5:
       WMC (exact, inclusion-exclusion) = P(e12)·(1−(1−P(e23)P(e39))(1−P(e24)P(e49))) = 0.5·0.4375 = 0.21875
       naïve product (paths as independent) = 1−(1−.125)(1−.125)                     = 0.234375   ← WRONG
   The naïve number is too big precisely because it counts e12's failure twice. This is the read-once vs
   shared distinction: the product is exact ONLY when paths are disjoint (the 0.776 demo); here it is not.
   Motivates the pluggable WMC backend (ansatz.wmc): for large correlated formulas we need a real counter."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.semiring :as sr]))

(defn- close? [a b] (< (Math/abs (- (double a) (double b))) 1e-9))

(defn- naive-product
  "The WRONG way: treat each conjunction (derivation path) as an independent event and OR them as independent.
   = 1 − ∏_path (1 − ∏_lit p). Ignores shared facts ⇒ double-counts."
  [probs dnf] (- 1.0 (reduce * (map (fn [conj] (- 1.0 (reduce * (map probs conj)))) dnf))))

(deftest correlated-query-needs-wmc
  (testing "a real 3-hop sr/q query produces a provenance formula with a SHARED edge"
    (let [edges (sr/relation [:a :b] (into {} (map (fn [e] [e #{#{e}}])) [[1 2] [2 3] [2 4] [3 9] [4 9]]))
          res   (sr/q {:find [:x :y] :where [[:edge :x :a] [:edge :a :b] [:edge :b :y]]} sr/provenance {:edge edges})
          formula (get (:rel res) {:x 1 :y 9})
          probs {[1 2] 0.5 [2 3] 0.5 [3 9] 0.5 [2 4] 0.5 [4 9] 0.5}]
      (is (= #{#{[1 2] [2 3] [3 9]} #{[1 2] [2 4] [4 9]}} formula) "both paths share edge [1 2]")
      (is (every? #(contains? % [1 2]) formula) "…the shared fact is in every conjunction")
      (testing "WMC is EXACT; the naïve product double-counts the shared edge ⇒ they DIFFER"
        (is (close? (sr/wmc probs formula) 0.21875)       "WMC (exact) = 0.21875")
        (is (close? (naive-product probs formula) 0.234375) "naïve product = 0.234375 (too big)")
        (is (not (close? (sr/wmc probs formula) (naive-product probs formula)))
            "correlation makes the naïve product WRONG — this is why WMC is the load-bearing engine"))))
  (testing "sanity: when paths are DISJOINT, WMC and the naïve product AGREE (read-once ⇒ product is exact)"
    ;; 1→{2,3}→9 : paths 1-2-9 and 1-3-9 share NO edge
    (let [edges (sr/relation [:a :b] (into {} (map (fn [e] [e #{#{e}}])) [[1 2] [1 3] [2 9] [3 9]]))
          formula (get (:rel (sr/q {:find [:x :y] :where [[:edge :x :m] [:edge :m :y]]} sr/provenance {:edge edges})) {:x 1 :y 9})
          probs {[1 2] 0.9 [1 3] 0.5 [2 9] 0.8 [3 9] 0.4}]
      (is (close? (sr/wmc probs formula) (naive-product probs formula)) "disjoint paths: product = WMC = 0.776")
      (is (close? (sr/wmc probs formula) 0.776)))))
