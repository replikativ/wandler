(ns ansatz.edn-surface-test
  "#60 — native-Clojure-over-Value surface. Existing Clojure code is portable onto dynamic EDN
   `Value`: `(:k v)` / `(get v :k)` / `(int? v)` / `(map? v)` / … lower onto the verified `v*`
   primitives when the operand is a Value. Pipelines over `List Value` read like ordinary
   Clojure yet kernel-verify and run. See [[malli-value-refinement]] [[edn-core-formalization]]."
  (:require [ansatz.core :as a]
            [ansatz.edn :as edn]
            [ansatz.stdlib :as std]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- checks? [nm]
  (when-let [ci (kenv/lookup (a/env) (name/from-string nm))]
    (try (kenv/check-constant (a/env)
           (kenv/mk-def (name/from-string (str "__c_" nm))
                        (kenv/ci-level-params ci) (kenv/ci-type ci) (kenv/ci-value ci)) 50000000)
         true (catch Throwable _ false))))

(deftest native-clojure-over-value
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (std/install!)
      (edn/install-core!)
      (edn/install-surface!)
      (binding [a/*verbose* false]
        ;; keyword access (:k v) and (get v :k) lower to vget
        (eval '(ansatz.core/defn s-name  [r :- Value] Value (:name r)))
        (eval '(ansatz.core/defn s-get   [r :- Value] Value (get r :name)))
        ;; predicates lower to v-predicates
        (eval '(ansatz.core/defn s-ageint [r :- Value] Bool (int? (:age r))))
        (eval '(ansatz.core/defn s-ismap  [r :- Value] Bool (map? r)))
        (eval '(ansatz.core/defn s-namestr [r :- Value] Bool (string? (get r :name))))
        ;; numeric comparison on a Value field (the field coerces to Int)
        (eval '(ansatz.core/defn s-adult [r :- Value] Bool (< 18 (:age r))))
        ;; == on a Value field vs a keyword / string literal (structural veq)
        (eval '(ansatz.core/defn s-active [r :- Value] Bool (== (:status r) :active)))
        (eval '(ansatz.core/defn s-named  [r :- Value] Bool (== (:name r) "alice")))
        ;; a portable pipeline over List Value: written as ordinary Clojure
        (eval '(ansatz.core/defn s-pipe [rows :- (List Value)] (List Value)
                 (mapv (fn [r] (:name r)) (filterv (fn [r] (int? (:age r))) rows))))
        ;; arithmetic on Value fields (the field coerces to Int/Float)
        (eval '(ansatz.core/defn s-age1 [r :- Value] Int (+ (:age r) 1)))
        (eval '(ansatz.core/defn s-dbl  [r :- Value] Int (* 2 (:age r))))
        ;; a realistic filter-then-project over dynamic rows, all native Clojure
        (eval '(ansatz.core/defn s-adult-names [rows :- (List Value)] (List Value)
                 (mapv (fn [r] (:name r)) (filterv (fn [r] (< 18 (:age r))) rows))))
        ;; map computing a derived Int per row
        (eval '(ansatz.core/defn s-ages2 [rows :- (List Value)] (List Int)
                 (mapv (fn [r] (* 2 (:age r))) rows)))
        ;; (count v) over a Value → element count; over List Value → List.length
        (eval '(ansatz.core/defn s-vcount [v :- Value] Nat (count v)))
        (eval '(ansatz.core/defn s-rowcount [rows :- (List Value)] Nat (count rows)))
        ;; (assoc v :k x) over a Value → vput chain (value lifted to a Value)
        (eval '(ansatz.core/defn s-put  [r :- Value] Value (assoc r :age 30)))
        (eval '(ansatz.core/defn s-put2 [r :- Value] Value (assoc r :name "x" :on true)))
        (eval '(ansatz.core/defn s-copy [r :- Value] Value (assoc r :b (:a r))))
        ;; nested get-in / assoc-in / update-in / update over a Value
        (eval '(ansatz.core/defn s-getin    [r :- Value] Value (get-in r [:a :b])))
        (eval '(ansatz.core/defn s-associn  [r :- Value] Value (assoc-in r [:a :b] 7)))
        (eval '(ansatz.core/defn s-updatein [r :- Value] Value (update-in r [:a :b] (fn [x] (+ x 1)))))
        (eval '(ansatz.core/defn s-update   [r :- Value] Value (update r :age (fn [x] (+ x 1))))))
      ;; every surface form kernel-verifies
      (doseq [nm ["s-name" "s-get" "s-ageint" "s-ismap" "s-namestr" "s-pipe"
                  "s-adult" "s-active" "s-named" "s-adult-names" "s-age1" "s-dbl" "s-ages2"
                  "s-vcount" "s-rowcount" "s-put" "s-put2" "s-copy"
                  "s-getin" "s-associn" "s-updatein" "s-update"]]
        (is (true? (checks? nm)) (str nm " kernel-verifies")))
      ;; and runs with native Clojure semantics
      (let [->v edn/edn->value
            row (->v {:name "alice" :age 30})]
        (is (= "alice" (edn/value->edn ((resolve 's-name) row))))
        (is (= "alice" (edn/value->edn ((resolve 's-get)  row))))
        (is (true?  ((resolve 's-ageint) row)))
        (is (true?  ((resolve 's-ismap)  row)))
        (is (true?  ((resolve 's-namestr) row)))
        (is (false? ((resolve 's-ageint) (->v {:age "x"}))))
        ;; numeric + equality comparisons on Value fields
        (is (true?  ((resolve 's-adult)  (->v {:age 30}))))
        (is (false? ((resolve 's-adult)  (->v {:age 10}))))
        (is (true?  ((resolve 's-active) (->v {:status :active}))))
        (is (false? ((resolve 's-active) (->v {:status :off}))))
        (is (true?  ((resolve 's-named)  (->v {:name "alice"}))))
        (is (false? ((resolve 's-named)  (->v {:name "bob"}))))
        ;; pipeline: keep int-aged rows, project name
        (is (= ["a" "c"]
               (mapv edn/value->edn
                     ((resolve 's-pipe)
                      (mapv ->v [{:name "a" :age 30} {:name "b" :age "x"} {:name "c" :age 5}])))))
        ;; pipeline: keep adults (age > 18), project name — fully native Clojure
        (is (= ["a" "c"]
               (mapv edn/value->edn
                     ((resolve 's-adult-names)
                      (mapv ->v [{:name "a" :age 30} {:name "b" :age 10} {:name "c" :age 41}])))))
        ;; arithmetic on fields
        (is (= 31 ((resolve 's-age1) (->v {:age 30}))))
        (is (= [2 10 20] (vec ((resolve 's-ages2) (mapv ->v [{:age 1} {:age 5} {:age 10}])))))
        ;; count over Value (vector/map/set/string) and over List Value
        (is (= 3 ((resolve 's-vcount) (->v [1 2 3]))))
        (is (= 2 ((resolve 's-vcount) (->v {:a 1 :b 2}))))
        (is (= 4 ((resolve 's-vcount) (->v #{1 2 3 4}))))
        (is (= 3 ((resolve 's-vcount) (->v "abc"))))
        (is (= 2 ((resolve 's-rowcount) (mapv ->v [{:a 1} {:b 2}]))))
        ;; assoc over Value
        (is (= {:age 30 :name "z"} (edn/value->edn ((resolve 's-put) (->v {:name "z"})))))
        (is (= {:on true :name "x"} (edn/value->edn ((resolve 's-put2) (->v {})))))
        (is (= {:a 7 :b 7} (edn/value->edn ((resolve 's-copy) (->v {:a 7})))))
        ;; nested ops
        (is (= 42 (edn/value->edn ((resolve 's-getin) (->v {:a {:b 42}})))))
        (is (= {:a {:b 7 :c 1}} (edn/value->edn ((resolve 's-associn) (->v {:a {:c 1}})))))
        (is (= {:a {:b 11}} (edn/value->edn ((resolve 's-updatein) (->v {:a {:b 10}})))))
        (is (= {:age 6} (edn/value->edn ((resolve 's-update) (->v {:age 5})))))))
    (do (println "SKIP native-clojure-over-value: no Init env") (is true))))
