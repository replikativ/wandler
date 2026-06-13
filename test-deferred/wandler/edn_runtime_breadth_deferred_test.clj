(ns wandler.edn-runtime-breadth-deferred-test
  "Dynamic-EDN Value tier RUNS end to end: ordinary Clojure over `List Value` (keyword
   projection, type predicates, `<`/`<=` comparisons over int fields, assoc) compiled +
   executed, differential-checked against the same Clojure over plain EDN. Exercises the
   tagged-rep `[cidx field…]` runtime (ctor + recursor codegen) and the type-directed
   keyword-access + comparison seams. The NON-fused forms are covered here; fused EDN
   pipelines (map∘filter over Value through the optimizer) are a separate open item."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.stdlib :as std]
            [wandler.surface.edn :as edn]
            [clojure.test :refer [deftest is]])
  (:import [java.io File]))

(def ^:private rows-edn [{:name "ada" :age 36} {:name "bob" :age 17} {:name "eve" :age 29}])

(def ^:private cases
  ;; [name body truth]   (over rows : List Value, returning List Value)
  [['er-kw-proj   '(mapv :age rows)                              #(mapv :age %)]
   ['er-filter-int '(filterv (fn [r] (int? (:age r))) rows)      #(filterv (fn [r] (int? (:age r))) %)]
   ['er-filter-lt '(filterv (fn [r] (< (:age r) 30)) rows)       #(filterv (fn [r] (< (:age r) 30)) %)]
   ['er-filter-le '(filterv (fn [r] (<= (:age r) 29)) rows)      #(filterv (fn [r] (<= (:age r) 29)) %)]
   ['er-filter-lit-lhs '(filterv (fn [r] (< 18 (:age r))) rows)  #(filterv (fn [r] (< 18 (:age r))) %)]
   ['er-assoc     '(mapv (fn [r] (assoc r :adult true)) rows)    #(mapv (fn [r] (assoc r :adult true)) %)]
   ['er-string    '(filterv (fn [r] (string? (:name r))) rows)   #(filterv (fn [r] (string? (:name r))) %)]])

(deftest edn-value-runs-end-to-end
  (if (.exists (File. "test-data/init-store"))
    (do
      (binding [a/*verbose* false] (a/init! "test-data/init-store" "init"))
      (w/install!)
      (binding [a/*verbose* false] (std/install!) (edn/install-core!) (edn/install-surface!))
      (let [rows (mapv edn/edn->value rows-edn)]
        (doseq [[n body truth] cases]
          (binding [a/*verbose* false]
            (eval (list 'ansatz.core/defn n '[rows :- (List Value)] '(List Value) body)))
          (let [got  (mapv edn/value->edn ((resolve n) rows))
                want (truth rows-edn)]
            (is (= (seq got) (seq want))
                (str n ": " (pr-str got) " ≠ " (pr-str want)))))
        ;; nil = vnil over Value: get-with-default, when (one-armed if), keep — over rows
        ;; where one row is MISSING :age (absence = vnil).
        (let [sparse-edn [{:name "ada" :age 36} {:name "bob"} {:name "eve" :age 29}]
              sparse (mapv edn/edn->value sparse-edn)
              nil-cases [['nr-getd '(mapv (fn [r] (get r :age 0)) rows)
                          #(mapv (fn [r] (get r :age 0)) %)]
                         ['nr-when '(mapv (fn [r] (when (vsome? (get r :age)) (:name r))) rows)
                          #(mapv (fn [r] (when (some? (:age r)) (:name r))) %)]
                         ['nr-keep '(keep (fn [r] (get r :age)) rows)
                          #(keep (fn [r] (get r :age)) %)]]]
          (doseq [[n body truth] nil-cases]
            (binding [a/*verbose* false]
              (eval (list 'ansatz.core/defn n '[rows :- (List Value)] '(List Value) body)))
            (let [got (mapv edn/value->edn ((resolve n) sparse))
                  want (truth sparse-edn)]
              (is (= (seq got) (seq want))
                  (str n ": " (pr-str got) " ≠ " (pr-str want))))))))
    (println "edn-runtime-breadth: no env, skipping")))
