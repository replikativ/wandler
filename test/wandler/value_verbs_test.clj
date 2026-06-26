(ns wandler.value-verbs-test
  "Native-Clojure map verbs over the dynamic EDN Value universe (ansatz.surface.data): contains?,
   keys, vals, dissoc, merge, update, get-in. Each lowers to a kernel-VERIFIED v* op (or composes
   them) and RUNS on real Clojure data via edn->value/value->edn — so ordinary Clojure map code is
   portable onto verified dynamic EDN."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.surface.data :as data]
            [wandler.core :as w]
            [wandler.test-env :as test-env]))

(def ^:private ready (atom false))

(use-fixtures :once
  (fn [f]
    (if @test-env/init-full-env
      (do (reset! a/ansatz-env @test-env/init-full-env)
          (binding [a/*verbose* false] (w/install!) (data/install-core!) (data/install-surface!))
          (reset! ready true) (f))
      (do (println "SKIP value-verbs: init.ndjson / store absent") (f)))))

(defn- runv [form arg]
  (binding [a/*verbose* false]
    (data/value->edn ((deref (eval form)) (data/edn->value arg)))))

(deftest native-map-verbs-over-value
  (when @ready
    (is (= true  (runv '(ansatz.core/defn v-has [m :- Value] Value (Value.vbool (contains? m :a))) {:a 1 :b 2}))
        "contains?")
    (is (= #{:a :b} (set (runv '(ansatz.core/defn v-ks [m :- Value] Value (keys m)) {:a 1 :b 2})))
        "keys")
    (is (= #{1 2} (set (runv '(ansatz.core/defn v-vs [m :- Value] Value (vals m)) {:a 1 :b 2})))
        "vals")
    (is (= {:b 2} (runv '(ansatz.core/defn v-dis [m :- Value] Value (dissoc m :a)) {:a 1 :b 2}))
        "dissoc")
    (is (= {:c 9 :a 1}
           (runv '(ansatz.core/defn v-mrg [m :- Value] Value
                    (merge m (Value.vmap (Value.ventry (Value.vkw "c") (Value.vint (Int.ofNat 9)) (Value.vnil)))))
                 {:a 1}))
        "merge (b shadows a)")
    (is (= 7 (runv '(ansatz.core/defn v-gin [m :- Value] Value (get-in m [:a :b])) {:a {:b 7}}))
        "get-in")
    (is (= {:n 5 :x 1}
           (runv '(ansatz.core/defn v-upd [m :- Value] Value
                    (update m :n (fn [v :- Value] (Value.vint (Int.add (vint-val v) (Int.ofNat 1))))))
                 {:n 4 :x 1}))
        "update")))
