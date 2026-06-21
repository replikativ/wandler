(ns wandler.refinement-selectivity-test
  "Step 2 — a declared malli range turns the cost model's comparator-head GUESS into a domain-aware,
   sound-at-the-ends selectivity. Pure/fast: builds predicate Exprs + a Subtype-Nat element type;
   no Init env. The win is on the SELECTION axis (Leis: cardinality is the dominant lever), with the
   0.0/1.0 ends genuinely SOUND (filter provably empty / identity)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.malli :as malli]
            [wandler.clean.optimize.cost :as cost]))

(defn- nat-c [] (e/const' (name/from-string "Nat") []))
(defn- pred
  "(fun v : Nat => CMP v k) for a comparison const name."
  [cmp k]
  (e/lam "v" (nat-c)
         (e/app* (e/const' (name/from-string cmp) []) (e/bvar 0) (e/lit-nat k))
         :default))

(def ^:private bounded (malli/schema->type-expr [:int {:min 0 :max 99}]))   ;; domain size 100
(def ^:private unbounded (malli/schema->type-expr :int))

(deftest domain-aware-rate-beats-the-guess
  (let [sel (cost/refinement-selectivity bounded)]
    (testing "a literal `< k` over [0,99] gets the exact domain fraction, not the 0.33 range guess"
      (is (== 0.10 (sel (pred "Nat.blt" 10))))    ;; |[0,9]| / 100
      (is (== 0.50 (sel (pred "Nat.ble" 49))))    ;; |[0,49]| / 100
      (is (== 0.01 (sel (pred "Nat.beq" 5)))))    ;; single value / 100
    (testing "the comparator-head guess (no refinement) is the coarse constant"
      (let [guess (cost/refinement-selectivity unbounded)]
        (is (== 0.33 (guess (pred "Nat.blt" 10))))   ;; :range default — domain-blind
        (is (not (== (guess (pred "Nat.blt" 10)) (sel (pred "Nat.blt" 10)))))))))

(deftest sound-at-the-ends
  (let [sel (cost/refinement-selectivity bounded)]
    (testing "k beyond the upper bound: the filter is provably IDENTITY → rate 1.0 (sound)"
      (is (== 1.0 (sel (pred "Nat.blt" 200))))
      (is (== 1.0 (sel (pred "Nat.ble" 99)))))
    (testing "k at/below the lower bound: the filter is provably EMPTY → rate 0.0 (sound)"
      (is (== 0.0 (sel (pred "Nat.blt" 0))))       ;; v < 0 over Nat∩[0,99] = ∅
      (is (== 0.0 (sel (pred "Nat.blt" 0)))))))

(deftest non-comparison-falls-back
  (testing "a predicate that isn't a literal comparison of the bound value falls back gracefully"
    (let [sel (cost/refinement-selectivity bounded)
          other (e/lam "v" (nat-c)
                       (e/app (e/const' (name/from-string "List.elem") []) (e/bvar 0))
                       :default)]
      (is (number? (sel other))))))
