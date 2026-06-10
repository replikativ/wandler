(ns ansatz.edn-fusion-test
  "#60 capstone — VERIFIED TRANSDUCERS over dynamic EDN. A native-Clojure pipeline over
   `List Value` (written with `:k`/`<`/`int?`/`filterv`/`mapv`) is (1) kernel type-checked,
   (2) FUSED by the optimizer with a kernel proof that `optimized ≡ naive` (parametric fusion
   laws at T=Value — `List.map_map`/`filter_filter`), and (3) runs correctly. The malli
   `conforms` predicate (see [[malli-value-refinement]]) is the kernel-checked boundary: used
   directly as a filter, it keeps only rows that provably match the schema. This is deliverable
   B: verified transducers over validated dynamic data. See [[native-clojure-over-value]]."
  (:require [ansatz.core :as a]
            [ansatz.edn :as edn]
            [ansatz.stdlib :as std]
            [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest verified-fusion-over-value
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (std/install!)
      (edn/install-core!)
      (edn/install-surface!)
      (binding [a/*verbose* false]
        ;; two-map pipeline → List.map_map fusion
        (eval '(ansatz.core/defn fz-twomap [rows :- (List Value)] (List Value)
                 (mapv (fn [v] (:b v)) (mapv (fn [r] (:a r)) rows))))
        ;; two-filter pipeline → filter_filter fusion
        (eval '(ansatz.core/defn fz-twofilt [rows :- (List Value)] (List Value)
                 (filterv (fn [v] (< 0 (:x v))) (filterv (fn [r] (int? (:x r))) rows))))
        ;; three-map pipeline → map_map applied twice
        (eval '(ansatz.core/defn fz-three [rows :- (List Value)] (List Int)
                 (mapv (fn [v] (+ v 1)) (mapv (fn [v] (* 2 (:age v))) (mapv (fn [r] r) rows)))))
        ;; map∘filter → ONE pass (filterMap): the canonical transducer fusion, now proven
        (eval '(ansatz.core/defn fz-mapfilter [rows :- (List Value)] (List Value)
                 (mapv (fn [r] (:name r)) (filterv (fn [r] (< 18 (:age r))) rows))))
        ;; the malli conforms boundary, compiled + verified, used directly as a filter predicate
        (eval (edn/schema->conforms-form 'conforms-person [:map [:name :string] [:age :int]]))
        (eval '(ansatz.core/defn fz-valid-names [rows :- (List Value)] (List Value)
                 (mapv (fn [r] (:name r)) (filterv (fn [r] (conforms-person r)) rows)))))

      ;; (1) the optimizer FUSED each pipeline AND kernel-certified orig = optimized
      (doseq [nm ["fz-twomap" "fz-twofilt" "fz-three" "fz-mapfilter"]]
        (let [ex (a/explain nm)]
          (is (true? (:changed? ex))  (str nm " was fused"))
          (is (true? (:verified? ex)) (str nm " fusion kernel-certified (optimized ≡ naive)"))))
      ;; map∘filter fused to a single filterMap pass via the proven law
      (is (= ["List.map_filter_filterMap"] (:rewrites (a/explain "fz-mapfilter")))
          "map∘filter → filterMap (one pass)")
      ;; the boundary-filtered pipeline type-checks + verifies (conforms is the boundary)
      (is (true? (:verified? (a/explain "fz-valid-names"))) "boundary pipeline verifies")

      ;; (2) and the fused runtime is correct
      (let [->v edn/edn->value]
        (is (= [1 2] (mapv edn/value->edn
                           ((resolve 'fz-twomap) (mapv ->v [{:a {:b 1}} {:a {:b 2}}])))))
        (is (= [{:x 5}] (mapv edn/value->edn
                              ((resolve 'fz-twofilt) (mapv ->v [{:x 5} {:x -1} {:x "n"}])))))
        (is (= [3 11] (vec ((resolve 'fz-three) (mapv ->v [{:age 1} {:age 5}])))))
        ;; fused map∘filter runs as one pass and is correct
        (is (= ["a" "c"] (mapv edn/value->edn
                               ((resolve 'fz-mapfilter)
                                (mapv ->v [{:name "a" :age 30} {:name "b" :age 10} {:name "c" :age 41}])))))
        ;; boundary: only rows conforming to [:map [:name :string] [:age :int]] survive
        (is (= ["ok"] (mapv edn/value->edn
                           ((resolve 'fz-valid-names)
                            (mapv ->v [{:name "ok" :age 30}     ; conforms
                                       {:name "bad" :age "x"}    ; :age not int
                                       {:name 5 :age 1}          ; :name not string
                                       {:age 9}])))))))           ; missing :name
    (do (println "SKIP verified-fusion-over-value: no Init env") (is true))))

(deftest plan-explain-api
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (std/install!)
      (edn/install-core!)
      (edn/install-surface!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn pl-twomap [rows :- (List Value)] (List Value)
                 (mapv (fn [v] (:b v)) (mapv (fn [r] (:a r)) rows))))
        (eval '(ansatz.core/defn pl-adults [rows :- (List Value)] (List Value)
                 (filterv (fn [r] (< 18 (:age r))) rows))))
      ;; static plan: the SOAC stages + pass counts before/after fusion + proof status
      (let [p (a/plan "pl-twomap")]
        (is (= ["map" "map"] (:stages-before p)) "naive = two maps")
        (is (= ["map"]       (:stages-after p))  "fused = one map")
        (is (= 2 (:passes-before p)))
        (is (= 1 (:passes-after p)))
        (is (true? (:fused? p)))
        (is (true? (:verified? p)) "optimized ≡ naive kernel-certified"))
      ;; rendered plan string
      (let [s (a/plan-str "pl-twomap")]
        (is (re-find #"map . map" s))
        (is (re-find #"kernel-certified" s)))
      ;; sample profiling: cardinality / selectivity / runtime (no boundary verification forced)
      (let [->v edn/edn->value
            data (mapv ->v (for [i (range 200)] {:age i}))
            p (a/plan "pl-adults" [data])]
        (is (= 200 (:n-in p)))
        (is (= 181 (:n-out p)) "filter age>18 keeps 181/200")
        (is (< 0.9 (:selectivity p) 0.91))
        (is (number? (:runtime-ms p)))))
    (do (println "SKIP plan-explain-api: no Init env") (is true))))
