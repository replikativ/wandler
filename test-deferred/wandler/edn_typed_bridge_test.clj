(ns wandler.edn-typed-bridge-test
  "#62 — the TYPED variant + the conforms→record bridge. A malli schema gives both a `conforms`
   predicate over the dynamic `Value` universe (#57) AND a `def-record` typed structure. Committing
   to the schema upgrades dynamic data to typed records: field access is an O(1) struct projection
   (vs vget's O(chain) walk — measured ~4.6x on a 10-field row), AND the verified fusion/relational
   laws apply (a map∘filter over records fuses to filterMap, kernel-certified, just like over
   List Value). `conforms` is the OPTIONAL boundary that performs the upgrade — gradual, not forced.
   See [[native-clojure-over-value]] (gradual path) and [[malli-value-refinement]] (conforms)."
  (:require [wandler.core]
            [ansatz.core :as a]
            [wandler.edn :as edn]
            [wandler.records :as rec]
            [wandler.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- checks? [nm]
  (when-let [ci (kenv/lookup (a/env) (name/from-string nm))]
    (try (kenv/check-constant (a/env)
           (kenv/mk-def (name/from-string (str "__c_" nm))
                        (kenv/ci-level-params ci) (kenv/ci-type ci) (kenv/ci-value ci)) 50000000)
         true (catch Throwable _ false))))

(deftest conforms-record-bridge
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (rec/install!)
      (edn/install-core!)        ; conforms + value->edn; NO install-surface! (typed path)
      (binding [a/*verbose* false]
        ;; ONE malli schema → a typed record AND a conforms predicate
        (eval '(wandler.records/def-record Person [:map [:name :string] [:age :int] [:city :string]]))
        (eval (edn/schema->conforms-form 'conforms-person [:map [:name :string] [:age :int]]))
        ;; a TYPED pipeline over records — O(1) field projection, and it fuses like any pipeline
        (eval '(ansatz.core/defn tb-adult-names [ps :- (List Person)] (List String)
                 (mapv (fn [p] (:name p)) (filterv (fn [p] (< 18 (:age p))) ps)))))
      ;; the typed pipeline kernel-verifies AND fuses map∘filter → filterMap (relational laws
      ;; apply to typed records exactly as to List Value)
      (is (true? (checks? "tb-adult-names")) "typed pipeline kernel-verifies")
      (is (= ["List.map_filter_filterMap"] (:rewrites (wandler.core/explain "tb-adult-names")))
          "map∘filter fuses to one pass over records too")
      ;; the conforms→record bridge: dynamic Values → optional conforms gate → value->record
      (let [map->Person (resolve 'map->Person)
            ->v edn/edn->value
            values (mapv ->v [{:name "a" :age 30 :city "ny"}
                              {:name "b" :age 10 :city "la"}
                              {:name "c" :age 41 :city "sf"}
                              {:name "bad" :age "x"}])          ; does NOT conform (:age not int)
            conforms (resolve 'conforms-person)
            ;; OPTIONAL boundary check (gradual — the caller chooses), then upgrade to records
            upgraded (->> values (filter conforms) (mapv #(edn/value->record map->Person %)))]
        ;; upgrade produced real typed records (defrecords)
        (is (every? record? upgraded) "value->record yields typed defrecords")
        (is (= 3 (count upgraded)) "conforms boundary dropped the non-conforming row")
        ;; the fast typed pipeline runs on the upgraded data
        (is (= ["a" "c"] (vec ((resolve 'tb-adult-names) upgraded)))
            "typed pipeline over upgraded records: adults only, names projected")
        ;; round-trip: record→value→record is identity on the schema fields
        (let [r (map->Person {:name "z" :age 22 :city "sf"})]
          (is (= {:name "z" :age 22 :city "sf"} (edn/value->edn (edn/record->value r)))
              "record→value→edn round-trips the fields"))))
    (do (println "SKIP conforms-record-bridge: no Init env") (is true))))
