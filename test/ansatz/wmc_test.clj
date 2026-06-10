(ns ansatz.wmc-test
  "The pluggable WMC seam (ansatz.wmc): the :enumeration reference is always present; the :logicng backend
   (knowledge compilation) is available under the :logicng alias and is cross-checked against enumeration.
   Run the LogicNG path with:  clj -M:test:logicng -n ansatz.wmc-test"
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.wmc :as wmc]
            [clojure.string :as str]))

(defn- close? [a b] (< (Math/abs (- (double a) (double b))) 1e-9))

;; the correlated formula from correlated_query_test: two 3-hop paths sharing edge [1 2]
(def ^:private formula #{#{[1 2] [2 3] [3 9]} #{[1 2] [2 4] [4 9]}})
(def ^:private probs {[1 2] 0.5 [2 3] 0.5 [3 9] 0.5 [2 4] 0.5 [4 9] 0.5})

(deftest enumeration-always-present
  (is (contains? (wmc/available) :enumeration) "the exact reference backend is always available")
  (is (close? (wmc/wmc probs formula :backend :enumeration) 0.21875) "exact WMC = 0.21875"))

(deftest serializer-for-native-counters
  (testing "DNF → MCC weighted-CNF (the format Ganak/d4 consume), via the ¬DNF-is-CNF complement"
    (let [{:keys [dimacs vars complement?]} (wmc/dnf->weighted-cnf probs formula)]
      (is (true? complement?) "result needs WMC = 1 − count(¬DNF)")
      (is (= 5 (count vars)) "5 distinct facts ⇒ 5 vars")
      (is (str/starts-with? dimacs "c t wmc") "MCC-2024 tracking-type line (Ganak/SharpSAT-TD/d4v2)")
      (is (str/includes? dimacs "p cnf 5 2") "header: 5 vars, 2 clauses (one per path)")
      (is (str/includes? dimacs "c p weight") "carries per-literal weights (both polarities)"))))

(deftest logicng-backend-when-present
  (wmc/load-backends!)
  (if (contains? (wmc/available) :logicng)
    (testing "LogicNG BDD weighted DP — EXACT, accounts for the shared edge"
      (is (close? (wmc/wmc probs formula :backend :logicng) 0.21875)
          "LogicNG = 0.21875 (NOT the naïve 0.234375 — the BDD shares [1 2] correctly)")
      (is (close? (wmc/wmc probs formula :backend :logicng :check? false)
                  (wmc/wmc probs formula :backend :enumeration))
          "LogicNG agrees with exact enumeration")
      (testing "the default seam prefers the compiled backend and auto-cross-checks it"
        (is (close? (wmc/wmc probs formula) 0.21875)))
      (testing "scales past enumeration: a 30-fact correlated formula (2^30 is hopeless to enumerate)"
        (let [big (set (for [k (range 15)] #{[:e k] [:shared 0] [:t k]}))   ; 15 paths sharing [:shared 0]
              bp  (into {[:shared 0] 0.5} (mapcat (fn [k] [[[:e k] 0.5] [[:t k] 0.5]])) (range 15))]
          (is (number? (wmc/wmc bp big :backend :logicng :check? false)) "LogicNG returns a WMC over 31 facts")
          (is (<= 0.0 (wmc/wmc bp big :backend :logicng :check? false) 1.0) "…a valid probability"))))
    (testing "LogicNG absent (plain :test run) — seam still works via enumeration"
      (is (close? (wmc/wmc probs formula) 0.21875) "falls back to the exact reference"))))
