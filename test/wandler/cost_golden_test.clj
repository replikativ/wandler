(ns wandler.cost-golden-test
  "GOLDEN-COST SNAPSHOT — pins the static cost model on the gate-critical shapes so the planned
   descriptor-driven, tree/let-aware redesign (docs/COST_MODEL_REDESIGN.md) can be proven to preserve
   the load-bearing invariant: SOAC inputs and step-lambdas keep their current cost, so the
   factorization/reorder adopt decisions (physical.clj) don't shift. These values are TODAY's model
   (`pipeline-resources` + `soac-cost`). A1 of the redesign: lock them BEFORE the refactor; A2 must
   reproduce them byte-for-byte on these linear/SOAC shapes; A3 only ADDS cost to trees/lets (none of
   the shapes here is a tree or let, so they must not move)."
  (:require [ansatz.core :as a]
            [wandler.optimize.cost :as cost]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(def ^:private z lvl/zero)
(defn- c [s] (e/const' (nm/from-string s) []))

(defn- terms []
  (let [N (c "Nat") dec (c "instDecidableEqNat")
        xs (e/fvar 1) ys (e/fvar 2)
        idf (e/lam "x" N (e/bvar 0) :default)
        p   (e/lam "x" N (e/app* (c "Nat.blt") (e/lit-nat 2) (e/bvar 0)) :default)
        sq  (e/lam "x" N (e/app* (c "Nat.mul") (e/bvar 0) (e/bvar 0)) :default)
        foldl (fn [l] (e/app* (e/const' (nm/from-string "List.foldl") [z z]) N N (c "Nat.add") (c "Nat.zero") l))
        mapN  (fn [f l] (e/app* (e/const' (nm/from-string "List.map") [z z]) N N f l))
        filt  (fn [pp l] (e/app* (e/const' (nm/from-string "List.filter") [z]) N pp l))
        join  (e/app* (e/const' (nm/from-string "Map.join") []) N N N dec idf idf xs ys)]
    {:lin      (foldl (mapN sq (filt p xs)))
     :filt     (filt p xs)
     :join     join
     :joinfold (foldl (mapN idf join))
     :sort     (e/app* (e/const' (nm/from-string "List.mergeSort") [z]) N xs
                       (e/lam "a" N (e/lam "b" N (e/app* (c "Nat.ble") (e/bvar 1) (e/bvar 0)) :default) :default))
     :group    (e/app* (e/const' (nm/from-string "Map.group_by") []) N N dec idf xs)}))

;; golden snapshot: {term {:soac n :def [size time mem] :ndv [size time mem]}}
;; :def = default opts; :ndv = {:sizes {1 1000 2 1000} :ndv 8} (sized==def here since sources==base)
(def ^:private GOLDEN
  {:lin      {:soac 3 :def [1.0 1660.0 0.0]     :ndv [1.0 1660.0 0.0]}
   :filt     {:soac 1 :def [330.0 1000.0 0.0]   :ndv [330.0 1000.0 0.0]}
   :join     {:soac 1 :def [3000.0 3000.0 1000.0] :ndv [125000.0 3000.0 1000.0]}
   :joinfold {:soac 3 :def [1.0 9000.0 1000.0]  :ndv [1.0 253000.0 1000.0]}
   :sort     {:soac 1 :def [1000.0 6907.755 1000.0] :ndv [1000.0 6907.755 1000.0]}
   :group    {:soac 1 :def [1000.0 1000.0 1000.0] :ndv [1000.0 1000.0 1000.0]}})

(defn- approx= [a b] (< (Math/abs (- (double a) (double b))) 0.5))
(defn- rprofile [t opts] (let [r (cost/pipeline-resources t opts)] [(:size r) (:time r) (:memory r)]))

(deftest op-cost-registry-is-extensible
  ;; the engine-op seam: an engine declares how ITS op transforms cost via register-op-cost!, and the
  ;; planner's cost model uses it (a raster SIMD kernel registers ~base/4; stratum a fused join; etc.).
  (let [t (e/app* (e/const' (nm/from-string "Test.engineScan") []) (c "Nat") (e/fvar 1))]
    (is (= 0.0 (:time (cost/pipeline-resources t {}))) "unknown op → leaf, time 0")
    (cost/register-op-cost! "Test.engineScan"
      {:list 1 :tf (fn [_ [in cin mn] _ _ _] [in (+ cin (* 0.25 in)) mn])})
    (try
      (is (= 250.0 (:time (cost/pipeline-resources t {}))) "registered descriptor is used (base/4)")
      (finally (swap! cost/op-cost-registry dissoc "Test.engineScan")))))

(deftest cost-model-golden-snapshot
  (if-not @test-env/init-full-env
    (is true "skipped — no Init env")
    (let [ts (terms)
          ndv-opts {:sizes {1 1000.0 2 1000.0} :ndv 8}]
      (doseq [[k g] GOLDEN]
        (let [t (get ts k)]
          (is (= (:soac g) (cost/soac-cost t)) (str k " soac-cost"))
          (doseq [[tag opts] [[:def {}] [:ndv ndv-opts]]]
            (let [[s tm m] (rprofile t opts) [gs gt gm] (get g tag)]
              (is (and (approx= s gs) (approx= tm gt) (approx= m gm))
                  (str k " " tag " profile: got [" s " " tm " " m "] want " (get g tag))))))))))
