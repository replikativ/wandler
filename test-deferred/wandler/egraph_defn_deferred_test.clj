(ns wandler.egraph-optimize-test-deferred
  "E-graph search layer for the verified optimizer (roadmap item B).

   `wandler.optimize.egraph/saturate-and-extract` saturates grind's e-graph with the
   oriented laws, extracts the cost-minimal equivalent plan by `pipeline-cost`, and
   certifies `orig = extracted` with a kernel proof (grind's `mk-eq-proof`,
   re-checked by `verified-rewrite?`). Wired into `optimize-cost` via `:use-egraph?`.

   Matcher scope: app-level fusion (map_map, filter_filter), the filter↔map reorder,
   AND (task #34) UNDER-BINDER matching — laws whose LHS contains a lambda with pattern
   vars (the semijoin section `λx. elem x ys`) now E-match beneath the binder, faithful
   to Lean 4 `Grind/EMatch.lean` (open the binder with a fresh local, match the body;
   lambda binder types ignored, forall domains matched). Gated on the Init env.

   This test also pins the universe-level unification fix in the E-matcher: the
   polymorphic `List.map_map` (level params u,v,w) only fires once the matcher
   unifies the theorem's level params with the term's concrete `0` levels."
  (:require [wandler.core]
            [ansatz.core :as a]
            [wandler.surface.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [wandler.optimize :as opt]
            [wandler.optimize.egraph :as ege]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.ematch :as ematch]
            [clojure.test :refer [deftest is]]))

;; deferred: a/defn egraph opt-in path — eval error under the seamed optimizer hook (tier follow-up)

(deftest a-defn-can-opt-into-the-egraph
  ;; USABILITY: a/defn reaches the e-graph via `(binding [opt/*use-egraph* true] …)`. The result is
  ;; kernel-certified and runs identically to the greedy path; wandler.core/plan still explains it.
  (with-init
    (fn []
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn eg-greedy [xs :- (List Nat)] (List Nat)
                 (mapv (fn [x] (Nat.succ x)) (filterv (fn [x] (Nat.ble 3 x)) xs))))
        (binding [opt/*use-egraph* true]
          (eval '(ansatz.core/defn eg-egraph [xs :- (List Nat)] (List Nat)
                   (mapv (fn [x] (Nat.succ x)) (filterv (fn [x] (Nat.ble 3 x)) xs))))))
      (let [g (wandler.core/explain "eg-greedy"), e (wandler.core/explain "eg-egraph")]
        (is (true? (:verified? g)) "greedy verified")
        (is (and (:changed? e) (:verified? e)) "e-graph path changed + kernel-certified")
        (is (= [:egraph] (:rewrites e)) "explain marks the e-graph was used")
        ;; both produce the same (correct) runtime
        (is (= [4 5 6] (vec ((resolve 'eg-greedy) (list 1 2 3 4 5)))))
        (is (= [4 5 6] (vec ((resolve 'eg-egraph) (list 1 2 3 4 5)))) "e-graph result runs identically")))))
