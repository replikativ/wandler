(ns wandler.gradual-test-deferred
  "The gradual-typing → gradual-optimization front door (wandler.gradual): `gradient` shows what each
   tier of annotation unlocks, `coach` suggests what to annotate next — every plan kernel-certified.
   Over the canonical customers ⋈ orders sum-over-join."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.gradual :as g]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

;; deferred: gradual elaborate→planner path — List type mismatch in the gradual lens (tier follow-up)

(deftest standard-clojure-reaches-the-planner
  (when (ready?)
    (testing "elaborate: a typed Clojure pipeline → {:term :lctx}, optimized + certified"
      (let [{:keys [term lctx]} (g/elaborate (a/env) '[xs :- (List Nat)]
                                  '(reduce + 0 (map (fn [x :- Nat] (* 2 x)) (filter (fn [x :- Nat] (< 1 x)) xs))))
            res (g/plan (a/env) term :lctx lctx)]
        (is (= 1 (count lctx)) "the source param became a free fvar in the lctx")
        (is (:verified? res) "the elaborated Clojure pipeline optimizes + kernel-certifies")))
    (testing "report-clj: idiomatic join pipeline → gradient unlocks join-reorder via :sizes (by name)"
      (let [rpt (g/report-clj (a/env)
                  '[xs :- (List Nat), ys :- (List Nat)]
                  '(count (join (fn [x :- Nat] x) (fn [y :- Nat] y) xs ys))
                  [["untyped" {}] ["+ sizes" {:sizes {"xs" 100.0 "ys" 1000000.0}}]])]
        (is (clojure.string/includes? rpt ":join-reorder") "annotating sizes unlocks the join reorder")
        (is (clojure.string/includes? rpt "kernel-certified"))))))
