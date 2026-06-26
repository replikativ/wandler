(ns wandler.zset-test
  "The DBSP-faithful Z-set VIEW (wandler.exec.zset): a Z-set `A → Int` (order-free, weighted), so the
   differential join is an EXACT equality (funext + Int distributivity) — no permutation — and handles
   deletions as negative weights. Port of equi_join/product_bilinear from tchajed/dbsp-theory."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.exec.zset :as zs]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (zs/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest exact-bilinear-differential-join
  (when (ready?)
    (testing "the Z-set carrier + the EXACT bilinear differential — all check-constant'd"
      (doseq [n ["Zset" "Zadd" "Zproduct"
                 "Zproduct_left_linear" "Zproduct_right_linear" "Zproduct_product_rule"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present + kernel-verified"))))))

(deftest differential-join-runs-with-deletions
  (when (ready?)
    (testing "batch join == sum of the 4 cross-terms, EXACTLY — including deletions (negative weights)"
      (let [m1 {:a 1 :b 2} d1 {:a -1 :c 1}    ; delta: insert c, DELETE a (weight -1)
            m2 {1 1}        d2 {2 1}
            batch (zs/z-product (zs/z-add m1 d1) (zs/z-add m2 d2))
            diff  (reduce zs/z-add [(zs/z-product m1 m2) (zs/z-product m1 d2)
                                    (zs/z-product d1 m2) (zs/z-product d1 d2)])]
        (is (= batch diff) "differential (4-term) == batch recompute, exactly")
        (is (not (contains? batch [:a 1])) "the deleted row (a, weight 1−1=0) is absent from the view")
        (is (= 2 (get batch [:b 1])) "surviving row keeps its multiplicity")))
    (testing "equi-join on a key keeps only matching pairs (weights multiply)"
      (let [custs {{:id 1 :nm "x"} 1 {:id 2 :nm "y"} 1}
            ords  {{:cid 1 :amt 10} 1 {:cid 1 :amt 20} 1 {:cid 9 :amt 5} 1}
            j (zs/z-join :id :cid custs ords)]
        (is (= 2 (reduce + (vals j))) "two orders match customer 1; customer 9's order has no match")))))

(deftest integrated-incremental-join-engine
  (when (ready?)
    (testing "the incremental join engine (each step = the certified bilinear differential) == batch"
      (let [custs {{:id 1 :name "Ann"} 1 {:id 2 :name "Bo"} 1}
            deltas [[{{:cid 1 :amt 10} 1}                    custs]   ; orders + load customers
                    [{{:cid 2 :amt 20} 1 {:cid 1 :amt 5} 1}  {}]      ; two more orders
                    [{{:cid 9 :amt 99} 1}                    {}]      ; no matching customer
                    [{{:cid 1 :amt 10} -1}                   {}]]     ; RETRACT the first order
            inc-views (zs/incremental-join :cid :id deltas)
            bat-views (zs/batch-join       :cid :id deltas)]
        (is (= inc-views bat-views) "incremental differential view == batch recompute at EVERY step")
        (is (= [1 3 3 2] (mapv #(reduce + 0 (vals %)) inc-views)) "running |join| (= Strm.joinCount2)")
        (is (not-any? (fn [[[o _] _]] (= o {:cid 1 :amt 10})) (last inc-views)) "retraction removed the row")
        (is (= (last inc-views) (zs/z-join :cid :id {{:cid 2 :amt 20} 1 {:cid 1 :amt 5} 1 {:cid 9 :amt 99} 1} custs))
            "final view matches a from-scratch join of the surviving rows")))))

(deftest composed-incremental-pipeline
  (when (ready?)
    (testing "filter (linear) ∘ join (bilinear) ∘ sum (homomorphism) compose incrementally == batch"
      (let [custs {{:id 1 :name "Ann" :tier :premium} 1 {:id 2 :name "Bo" :tier :basic} 1}
            deltas [[{} custs]
                    [{{:cid 1 :amt 100} 1} {}]        ; Ann (premium) buys 100
                    [{{:cid 2 :amt 50}  1} {}]        ; Bo (basic) — filtered out
                    [{{:cid 1 :amt 30}  1} {}]        ; Ann +30
                    [{{:cid 1 :amt 100} -1} {}]]      ; retract Ann's first order
            premium? (fn [[_o c]] (= :premium (:tier c)))
            revenue  (fn [[o _c]] (:amt o))
            q (fn [views] (map (fn [v] (zs/z-sum revenue (zs/z-filter premium? v))) views))
            inc (q (zs/incremental-join :cid :id deltas))
            bat (q (zs/batch-join :cid :id deltas))]
        (is (= [0 100 100 130 30] (vec inc)) "premium running revenue (basic filtered out; retraction drops it)")
        (is (= (vec inc) (vec bat)) "composed incremental pipeline == batch at every step")))))

(deftest query-front-door-compile-and-explain
  (when (ready?)
    (testing "a declarative streaming query compiles to the engine + explains its certificate chain"
      (let [premium? (fn [[_o c]] (= :premium (:tier c)))
            revenue  (fn [[o _c]] (:amt o))
            q [[:join :cid :id] [:filter premium?] [:sum revenue]]
            custs {{:id 1 :name "Ann" :tier :premium} 1 {:id 2 :name "Bo" :tier :basic} 1}
            deltas [[{} custs] [{{:cid 1 :amt 100} 1} {}] [{{:cid 2 :amt 50} 1} {}]
                    [{{:cid 1 :amt 30} 1} {}] [{{:cid 1 :amt 100} -1} {}]]
            run (zs/query q)
            batch (->> (zs/batch-join :cid :id deltas) (map #(zs/z-sum revenue (zs/z-filter premium? %))))]
        (is (= [0 100 100 130 30] (vec (run deltas))) "compiled query runs incrementally")
        (is (= (vec (run deltas)) (vec batch)) "compiled incremental query == batch recompute")
        (let [ex (zs/explain q)]
          (is (clojure.string/includes? ex "Zproduct_product_rule") "explain cites the bilinear-join certificate")
          (is (clojure.string/includes? ex "LINEAR") "explain cites filter linearity"))))))
