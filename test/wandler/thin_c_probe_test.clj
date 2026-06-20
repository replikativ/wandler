(ns wandler.thin-c-probe-test
  "Regression guard for the ansatz `apply` lazy-isDefEq fix: the thin C proof of
   Map.filter_join_pushdown (apply A + apply B over a Map.join whose bucket carries a stuck
   group_by over a symbolic list) must TERMINATE (it diverged before the fix on eager
   normalize-for-match). This is the proof shape `wandler.clean.laws.relational/install!` now
   ships for `Map.filter_join_pushdown`."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [wandler.clean.surface.core :as w]
            [wandler.clean.laws.relational :as rel]
            [wandler.test-env :as test-env]))

(deftest thin-c-terminates
  (if-let [k @test-env/init-full-env]
    (do (reset! a/ansatz-env k)
        (w/install!)
        (binding [a/*verbose* false]
          (rel/install!)  ;; brings List.filter_flatMap_cond (A) + List.filter_map_pair_eq_cond (B)
          (eval '(ansatz.core/theorem Map.filter_join_pushdown_THINPROBE
                   [p :- (=> Nat Bool), kf :- (=> Nat Nat), lf :- (=> Nat Nat),
                    ys :- (List Nat), xs :- (List Nat)]
                   (= (List (Prod Nat Nat))
                      (List.filter (Prod Nat Nat) (fn [pr :- (Prod Nat Nat)] (p (Prod.fst Nat Nat pr)))
                        (Map.join Nat Nat Nat instDecidableEqNat kf lf xs ys))
                      (Map.join Nat Nat Nat instDecidableEqNat kf lf (List.filter Nat p xs) ys))
                   (rw [Map.join_eq]) (rw [Map.join_eq])
                   (apply List.filter_flatMap_cond) (intro a) (apply List.filter_map_pair_eq_cond))))
        (is (some? (ansatz.kernel.env/lookup (a/env)
                     (ansatz.kernel.name/from-string "Map.filter_join_pushdown_THINPROBE")))
            "thin C proof terminated and kernel-verified"))
    (do (println "SKIP thin-c-terminates: no Init env") (is true))))
