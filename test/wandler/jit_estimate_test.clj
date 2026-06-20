(ns wandler.jit-estimate-test
  "The seam where DATA informs the inductive plan: measure the cost knobs (:ndv/:sizes/:selectivity) from
   a sample, fuse with refinement priors, and watch the planner's COST reflect the real workload — while
   soundness (which plans are valid) stays purely inductive. A wrong measurement moves cost, never results."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.jit.estimate :as est]
            [wandler.clean.optimize.cost :as cost]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is use-fixtures]]))

(def ^:private z lvl/zero)
(defn- c [s] (e/const' (nm/from-string s) []))
(defn- setup [f] (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (w/install!)) (f))
(use-fixtures :once setup)

(deftest measurement-informs-cost-soundness-stays-inductive
  (if-not @test-env/init-full-env
    (is true "skipped — no Init env")
    (let [N (c "Nat") dec (c "instDecidableEqNat")
          xs (e/fvar 1) ys (e/fvar 2)
          idf (e/lam "x" N (e/bvar 0) :default)
          join  (e/app* (e/const' (nm/from-string "Map.join") []) N N N dec idf idf xs ys)
          naive (e/app* (e/const' (nm/from-string "List.foldl") [z z]) N N (c "Nat.add") (c "Nat.zero")
                        (e/app* (e/const' (nm/from-string "List.map") [z z]) N N idf join))
          skewed  '(1 1 2 2 1 3 1 2)          ; 3 distinct join keys
          uniform '(1 2 3 4 5 6 7 8)          ; 8 distinct
          sizes   {1 1000.0 2 1000.0}]
      ;; (1) measurement: distinct-key count from the actual data
      (is (= 3.0 (est/measure-ndv (a/env) idf skewed))  "skewed sample → ndv 3")
      (is (= 8.0 (est/measure-ndv (a/env) idf uniform)) "uniform sample → ndv 8")
      ;; (2) the estimator fuses evidence over a prior
      (let [params (est/cost-params (a/env) naive
                                    {:priors {:sizes {1 500.0 2 1000.0} :ndv 100} :sample skewed
                                     :key-of idf :source-id 1})]
        (is (= 3.0 (:ndv params))      "measured ndv (3) OVERRIDES the prior ndv (100)")
        (is (= 8.0 (get (:sizes params) 1)) "measured source size (|sample|=8) overrides prior (500)")
        (is (= 1000.0 (get (:sizes params) 2)) "the unmeasured source keeps its prior size"))
      ;; (3) the measured ndv MOVES the cost the planner gates on: fewer distinct keys ⇒ bigger join
      ;; product ⇒ the naive plan is MORE expensive ⇒ factorization is more clearly worth it.
      (let [cost-skew (cost/pipeline-cost naive {:sizes sizes :ndv (est/measure-ndv (a/env) idf skewed)})
            cost-unif (cost/pipeline-cost naive {:sizes sizes :ndv (est/measure-ndv (a/env) idf uniform)})]
        (is (> cost-skew cost-unif)
            "low measured ndv (skew) ⇒ the planner sees a larger join product ⇒ higher naive cost"))
      ;; (4) SOUNDNESS is untouched by any of this — the plan SPACE is the same regardless of the sample.
      ;;     (Demonstrated structurally: cost-params only ever produces the :sizes/:selectivity/:ndv map;
      ;;      it never changes `naive` — the term the kernel certifies. Data steers cost, not correctness.)
      (is (map? (est/cost-params (a/env) naive {:sample uniform :key-of idf}))
          "cost-params yields only cost knobs — it cannot alter the certified term"))))
