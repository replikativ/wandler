(ns wandler.opaque-carrier-test
  "The gradual `Opaque` carrier (ansatz.malli/ensure-opaque!): a realistic event record — timestamp
   (:any), status (:keyword), id (:uuid) — that previously THREW at the malli precise lane now models,
   carries, and keys (group-by / join) on the opaque fields, while the precise fields (:int amounts) keep
   the full certified optimizer. The opaque dec lowers to Clojure `=`, so any JVM value (Instant/UUID/
   keyword) flows through. Needs the full Init env."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env) (wc/install!) (wc/install-laws!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(defn- malli? [] (try (require 'malli.core) true (catch Throwable _ false)))

(deftest opaque-fields-model-carry-key
  (if-not (and (ready?) (malli?))
    (is true "skipped — needs full Init env + malli")
    (let [m (find-ns 'malli.core)
          => (ns-resolve m '=>)]
      (testing "an event record with :any/:keyword/:uuid fields elaborates, group-bys, is verified"
        (eval (list (symbol "malli.core" "=>") 'oc-rev
                    [:=> [:cat [:sequential [:map [:ts :any] [:status :keyword] [:id :uuid]
                                                  [:amount [:int {:min 0}]]]]] [:sequential :int]]))
        (eval '(ansatz.core/defn oc-rev [events]
                 (map (fn [g] (reduce + 0 (map (fn [e] (:amount e)) g)))
                      (vals (group-by (fn [e] (:status e)) events)))))
        (let [f (deref (resolve 'oc-rev))
              now (java.time.Instant/now)]
          (is (= [15 99] (mapv long (f [{:ts now :status :paid :id (java.util.UUID/randomUUID) :amount 10}
                                        {:ts now :status :paid :id (java.util.UUID/randomUUID) :amount 5}
                                        {:ts now :status :pending :id (java.util.UUID/randomUUID) :amount 99}])))
              "group-by an opaque keyword field, sum the precise :amount")
          (is (:verified? (wc/explain 'oc-rev)) "the optimization is kernel-certified over the mixed record")))
      (testing "join on an opaque :uuid key"
        (eval (list (symbol "malli.core" "=>") 'oc-join
                    [:=> [:cat [:sequential [:map [:id :uuid] [:region [:int {:min 0}]]]]
                               [:sequential [:map [:id :uuid] [:amount [:int {:min 0}]]]]] :int]))
        (eval '(ansatz.core/defn oc-join [users orders]
                 (reduce + 0 (map (fn [[u o]] (:amount o))
                                  (join (fn [u] (:id u)) (fn [o] (:id o)) users orders)))))
        (let [f (deref (resolve 'oc-join)) a (java.util.UUID/randomUUID) b (java.util.UUID/randomUUID)]
          (is (= 14 (long (f [{:id a :region 0} {:id b :region 0}]
                             [{:id a :amount 5} {:id b :amount 9}])))
              "join on a uuid field (dec erased → Clojure =)")))
      (testing "[:enum …] maps to its members' type — string enum sums, keyword enum group-bys"
        (eval (list (symbol "malli.core" "=>") 'oc-enum
                    [:=> [:cat [:sequential [:map [:s [:enum :a :b]] [:n [:int {:min 0}]]]]] [:sequential :int]]))
        (eval '(ansatz.core/defn oc-enum [xs]
                 (map (fn [g] (reduce + 0 (map (fn [e] (:n e)) g))) (vals (group-by (fn [e] (:s e)) xs)))))
        (let [f (deref (resolve 'oc-enum))]
          (is (= [3 5] (mapv long (f [{:s :a :n 1} {:s :a :n 2} {:s :b :n 5}]))) "keyword-enum group-by"))))))
