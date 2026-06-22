(ns wandler.infer-test
  "Sample-driven inference (wandler.infer): malli.provider recovers structure, our layer adds the
   value-level refinements split into the GUARDED-sound (unique-key) and ADVISORY-prior (range/ndv)
   lanes. Fixtures are malli-generated, so the test is a differential recovery check. Pure Clojure +
   malli — no kernel env needed."
  (:require [wandler.infer :as infer]
            [malli.core :as m]
            [malli.generator :as mg]
            [clojure.test :refer [deftest is testing]]))

(def order-schema
  [:map
   [:id     [:int {:min 1000 :max 9999}]]
   [:age    [:int {:min 18 :max 65}]]
   [:status [:enum "new" "paid" "shipped"]]
   [:name   [:string {:min 3 :max 12}]]])

(defn gen-rows
  "Deterministic rows whose :id is a genuine primary key (unique counter)."
  [n seed]
  (->> (mg/sample order-schema {:size n :seed seed})
       (map-indexed (fn [i r] (assoc r :id (+ 1000 i))))
       vec))

(deftest structure-and-profile
  (let [rows (gen-rows 500 99)
        p    (infer/profile rows)]
    (testing "malli.provider recovers the relational structure (and every row validates)"
      (is (every? #(m/validate (:structure p) %) rows))
      (is (= #{:id :age :status :name} (set (keys (:fields p))))))
    (testing "per-field profile: ndv, range/length priors, small-domain"
      (is (= 500 (:ndv (get-in p [:fields :id])))           "PK :id has full distinct count")
      (is (= 3   (:ndv (get-in p [:fields :status])))       "enum :status has tiny ndv")
      (is (= ["new" "paid" "shipped"] (:small-domain (get-in p [:fields :status]))))
      (let [r (:range-prior (get-in p [:fields :age]))]
        (testing "range prior is one-sidedly-too-tight: a SUBSET of the true [18,65]"
          (is (<= 18 (:min r))) (is (<= (:max r) 65)))))))

(deftest guarded-sound-lane-keys
  (let [rows (gen-rows 500 99)
        p    (infer/infer rows)]
    (testing "unique-key CANDIDATES (collision-free over the sample) → wandler.adaptive"
      (is (contains? (set (:key-candidates p)) :id) ":id (a true PK) is a candidate")
      (is (not (contains? (set (:key-candidates p)) :status))
          ":status (ndv 3) is never collision-free → not a candidate"))
    (testing "a candidate is NOT a fact: a high-cardinality non-key can look unique on a sample"
      ;; the consumer (adaptive) GUARDS the key at the boundary, so this is sound regardless
      (is (every? keyword? (:key-candidates p))))))

(deftest advisory-prior-lane-cost
  (let [rows (gen-rows 200 7)
        p    (infer/profile rows)
        pri  (infer/cost-priors p :source-id 7 :join-key :status)]
    (testing "cost-priors shape for wandler.jit.estimate/cost-params"
      (is (= {7 200.0} (:sizes pri)) "source size = sample cardinality")
      (is (= 3.0 (:ndv pri))         ":status distinct-count seeds the ndv prior"))
    (testing "no source-id / join-key → empty prior (nothing claimed)"
      (is (= {} (infer/cost-priors p))))))

(deftest refined-schema-round-trip
  (let [rows (gen-rows 300 5)
        p    (infer/infer rows)
        rs   (:refined-schema p)]
    (testing "the refined schema rides ansatz.malli unchanged and ALWAYS validates its own sample"
      (is (every? #(m/validate rs %) rows) "observed bounds contain the sample by construction"))
    (testing "inferred bounds are tagged ::source so a consumer can tell them from declared ones"
      (let [age-schema (->> (rest rs) (filter #(= :age (first %))) first second)]
        (is (= :int (first age-schema)))
        (is (= :sample-prior (:wandler.infer/source (second age-schema))))))
    (testing "refined ⊆ structural: it only TIGHTENS, never widens (the structure still validates)"
      (is (every? #(m/validate (:structure p) %) rows)))))

(deftest non-map-rows
  (testing "a scalar collection profiles structure only (no per-field refinements)"
    (let [p (infer/profile [1 2 3 4 5])]
      (is (nil? (:fields p)))
      (is (= 5 (:n p)))
      (is (= [] (infer/key-candidates p))))))
