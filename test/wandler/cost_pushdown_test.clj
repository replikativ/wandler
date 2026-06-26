(ns wandler.cost-pushdown-test
  "Cost-based physical PUSH-DOWN (COST_MODEL_REDESIGN B2): among engine backends that recognize a plan
   shape, pick the cheapest lowering that beats the eager Clojure cost — instead of firing the first
   backend that recognizes. This is the decision that makes raster/stratum transparent to the planner
   (their cost is consulted, not assumed). Every backend is result-equal (the kernel proof certifies
   the optimized plan), so the choice is purely performance. Tested with fake backends — the mechanism
   is independent of which engines are on the classpath (B2b wires real raster/stratum costs)."
  (:require [wandler.exec.physical :as phys]
            [clojure.test :refer [deftest is use-fixtures]]))

(use-fixtures :each (fn [f] (phys/clear-cost-backends!) (f) (phys/clear-cost-backends!)))

(defn- backend [name lowers? cost]
  {:name name :cost (fn [_plan _eager] cost) :lower (fn [_env _plan _names] (when lowers? (list :lowered name)))})

(deftest picks-cheapest-recognizing-backend-that-beats-eager
  (phys/register-cost-backend! (backend :raster  true  250.0))
  (phys/register-cost-backend! (backend :stratum true  400.0))
  (phys/register-cost-backend! (backend :gpu     false 10.0))   ; cheapest BUT doesn't recognize → skipped
  (let [c (phys/choose-cost-form nil :plan nil 1000.0)]         ; eager cost = 1000
    (is (= :raster (:backend c)) "cheapest RECOGNIZING backend wins (not the non-recognizing gpu)")
    (is (= 250.0 (:cost c)))
    (is (= '(:lowered :raster) (:form c)))))

(deftest declines-when-no-backend-beats-eager
  (phys/register-cost-backend! (backend :raster true 250.0))
  (is (nil? (phys/choose-cost-form nil :plan nil 200.0))
      "eager (200) is cheaper than the only backend (250) → nil, run eager Clojure"))

(deftest declines-when-nothing-recognizes
  (phys/register-cost-backend! (backend :raster false 1.0))
  (is (nil? (phys/choose-cost-form nil :plan nil 1000.0)) "no recognizing backend → nil"))

(deftest push-down-is-workload-size-sensitive
  ;; an engine with a SETUP cost (raster: fixed box/fork/dispatch overhead + low per-element term):
  ;; cost = setup + eager/speedup. The decision FLIPS with workload size — declined on a small input
  ;; (setup not amortized), chosen on a large one. eager-cost is the size proxy (∝ input cardinality).
  (let [setup 3000.0 speedup 3.5
        simd {:name :raster :lower (fn [_ _ _] '(:simd))
              :cost (fn [_plan eager] (+ setup (/ (double eager) speedup)))}]
    (phys/register-cost-backend! simd)
    (is (nil? (phys/choose-cost-form nil :plan nil 2000.0))
        "SMALL workload (eager 2000): raster cost 3571 > 2000 → declined, run eager")
    (is (= :raster (:backend (phys/choose-cost-form nil :plan nil 100000.0)))
        "LARGE workload (eager 100000): raster cost 31571 < 100000 → chosen")))
