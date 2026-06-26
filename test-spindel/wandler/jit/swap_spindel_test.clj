(ns wandler.jit.swap-spindel-test
  "The spindel (reactive) PSwapNode adapter (wandler.jit.swap-spindel): a verified hot-swap of the
   operator at a reactive node, driven through spindel's PUBLIC dirty mechanism. One spin tracks the
   node's `version` signal and applies the current operator; `swap-op!` installs a new (certified-≡)
   operator and bumps the version, so the spin re-runs with it — same value (glitch-free), only faster.
   Scenario faithful to Path 2b: optimized = count without dedup (group-by elimination under a unique
   key), original = dedup-then-count. Runs only under the optional :spindel dep."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [wandler.jit.swap :as swap]
            [wandler.jit.swap-spindel :as sps]))

(deftest reactive-hot-swap
  (let [ctx (sp/create-execution-context)]
    (try
      (sp/with-context ctx
        (let [orig-runs (atom 0) opt-runs (atom 0)
              input     [{:k 1} {:k 2} {:k 3}]                       ; unique key
              original  (fn [rows] (swap! orig-runs inc) (count (distinct (map :k rows))))
              optimized (fn [rows] (swap! opt-runs inc) (count rows))   ; sound under unique key
              node      (sps/spindel-node ctx original)
              ver       (sps/version-signal node)
              t         (spin (let [_ (track ver)] ((swap/current node) input)))]
          (testing "the reactive spin computes via the ORIGINAL operator"
            (is (= 3 @t))
            (is (= 1 @orig-runs))
            (is (= 0 @opt-runs)))
          (testing "re-reading WITHOUT a swap does not re-run (cached) — invalidation is swap-driven"
            (is (= 3 @t))
            (is (= 1 @orig-runs)))
          (testing "swap-op! installs the optimized operator AND invalidates → spin re-runs, same value"
            (swap/swap-op! node optimized)
            (simple/await-drain-complete! ctx)               ; let the reactive re-run settle
            (is (= 3 @t) "certified ≡ : group-by-elim under a unique key yields the same count, faster")
            (is (pos? @opt-runs)  "the optimized operator ran on the reactive re-run")
            (is (= 1 @orig-runs)  "the original did NOT run again (operator was swapped)")
            (is (= 1 (swap/generation node))))))
      (finally (sp/stop-context! ctx)))))
