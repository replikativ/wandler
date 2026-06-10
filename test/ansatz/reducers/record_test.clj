(ns ansatz.reducers.record-test
  (:require [ansatz.reducers.record :as rec]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [clojure.test :refer [deftest is]]))

(def ^:private Person
  [:map [:a [:and :int [:>= 0]]] [:b [:and :int [:>= 0]]] [:c [:and :int [:>= 0]]]])

(deftest model-from-malli-schema
  (let [m (rec/model Person)]
    (is (= [:a :b :c] (:keys m)))
    (is (= {:a 0 :b 1 :c 2} (:index m)))
    ;; RIGHT-nested Prod.{0,0}: fields are Nat : Type 0 (level 0, not the old ill-typed
    ;; {1,1}); and (a,(b,c)) not ((a,b),c) — the convention the getters navigate (#43).
    (is (= "(Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))" (e/->string (:rec-type m))))))

(deftest collapse-eliminates-dead-writes-with-proof
  ;; Integration: a chain of assocs with an overwrite collapses via overwrite
  ;; elimination, justified by a kernel proof, matching native Clojure. Skips
  ;; without an Init env.
  (if-let [kenv @test-env/init-full-env]
    (let [m (rec/model Person)
          ;; assoc :a 1 ; assoc :b 2 ; assoc :a 3  — the :a 1 write is dead
          ops [(rec/nat-assoc :a 1) (rec/nat-assoc :b 2) (rec/nat-assoc :a 3)]
          res (rec/collapse kenv m ops)
          naive #(-> % (assoc :a 1) (assoc :b 2) (assoc :a 3))
          rows [{:a 0 :b 0 :c 9} {:a 5 :b 5 :c 5}]]
      ;; op-reduction
      (is (= 3 (:ops-before res)))
      (is (= 2 (:ops-after res)))
      (is (= [:a :b] (mapv :key (:net-ops res))))
      ;; the rewrite is kernel-checked: composite = optimized, an Eq over records
      (is (re-find #"Eq\." (e/->string (:theorem-type res))))
      ;; native execution matches the naive pipeline, with fewer assocs
      (is (every? (fn [r] (= (naive r) ((:fn res) r))) rows)))
    (do
      (println "SKIP collapse-eliminates-dead-writes-with-proof: no Init env")
      (is true))))

(def ^:private Person4
  [:map [:a [:and :int [:>= 0]]] [:b [:and :int [:>= 0]]]
   [:c [:and :int [:>= 0]]] [:d [:and :int [:>= 0]]]])

(deftest projection-prunes-dead-fields-with-proof
  ;; A trailing select-keys makes writes to non-kept keys dead (column pruning),
  ;; combined with overwrite elimination — kernel-proven, matching native Clojure.
  (if-let [kenv @test-env/init-full-env]
    (let [m (rec/model Person4)
          ;; write :a :b :c, overwrite :a, project [:a :b]
          ops [(rec/nat-assoc :a 1) (rec/nat-assoc :b 2) (rec/nat-assoc :c 3)
               (rec/nat-assoc :a 4) (rec/select-keys-op [:a :b])]
          res (rec/collapse kenv m ops)
          naive #(-> % (assoc :a 1) (assoc :b 2) (assoc :c 3) (assoc :a 4) (select-keys [:a :b]))
          rows [{:a 0 :b 0 :c 0 :d 9} {:a 7 :b 7 :c 7 :d 7}]]
      (is (= 4 (:ops-before res)))
      (is (= 2 (:ops-after res)))            ; :c (projected) + :a 1 (overwritten) dropped
      (is (= [:a :b] (:projected res)))
      (is (= [[:a 4] [:b 2]] (mapv (juxt :key :runtime-value) (:net-ops res))))
      (is (re-find #"Eq\." (e/->string (:theorem-type res))))
      (is (every? (fn [r] (= (naive r) ((:fn res) r))) rows)))
    (is true)))

(deftest no-overwrite-keeps-all-writes
  (if-let [kenv @test-env/init-full-env]
    (let [m (rec/model Person)
          res (rec/collapse kenv m [(rec/nat-assoc :a 1) (rec/nat-assoc :b 2)])]
      (is (= 2 (:ops-before res)))
      (is (= 2 (:ops-after res))))   ; nothing dead
    (is true)))
