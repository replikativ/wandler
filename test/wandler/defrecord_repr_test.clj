(ns wandler.defrecord-repr-test
  "Malli-derived type-hinted defrecords as the internal record representation. A record's
   Int/Nat/Float fields get UNBOXED primitive defrecord storage (^long/^double), field
   access lowers to direct `.field` reads (no boxing, no reflection), and a pipeline-entry
   boundary coerces input maps to defrecords ONCE (a per-list instance? guard passes
   already-converted records through untouched). See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.collections :as coll]
            [wandler.records :as rec]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- malli-available? [] (try (require 'malli.core) true (catch Throwable _ false)))

(defn- kernel-checks? [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (try (env/check-constant
          (a/env)
          (env/mk-def (name/from-string (str "__chk_" nm))
                      (env/ci-level-params ci) (env/ci-type ci) (env/ci-value ci))
          50000000)
         true (catch Throwable _ false))))

(deftest defrecord-field-access
  (if (and @test-env/init-full-env (malli-available?))
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!) (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.records/def-record Sale [:map [:cust-id [:int {:min 0}]] [:amount :double] [:qty [:int {:min 0}]]]))
        (eval '(ansatz.core/defn amt-total [ss :- (List Sale)] Float
                 (reduce (fn [acc s] (add Float acc (:amount s))) 0.0 ss)))
        (eval '(ansatz.core/defn qty-total [ss :- (List Sale)] Int
                 (reduce (fn [acc s] (Int.add acc (:qty s))) 0 ss))))
      ;; the defrecord is type-hinted (primitive field storage)
      (let [reg (get @a/structure-registry "Sale")]
        (is (= '[Int Float Int] (:field-types reg)) "field types recorded")
        (is (some? (:record-class reg)) "record class (FQN) recorded for the .field receiver hint"))
      ;; the codegen lowers primitive fields to `.field` (direct, unboxed)
      (let [ci (env/lookup (a/env) (name/from-string "amt-total"))
            form (a/ansatz->clj (a/env) (env/ci-value ci) [])]
        (is (some #{'.amount} (flatten form)) "primitive Float field → .amount direct access"))
      ;; kernel-certifies
      (is (true? (kernel-checks? "amt-total")) "amt-total certifies")
      (is (true? (kernel-checks? "qty-total")) "qty-total certifies")
      ;; correct on MAP input (boundary converts once) AND on records (guard passes through)
      (let [maps [{:cust-id 1 :amount 100.0 :qty 3} {:cust-id 2 :amount 50.0 :qty 1}]
            recs (mapv #((resolve '->Sale) (:cust-id %) (:amount %) (:qty %)) maps)]
        (is (== 150.0 ((resolve 'amt-total) maps)) "sum of amounts (maps in)")
        (is (== 150.0 ((resolve 'amt-total) recs)) "sum of amounts (records in)")
        (is (= 4 ((resolve 'qty-total) maps))  "sum of qty (maps in)")
        (is (= 4 ((resolve 'qty-total) recs))  "sum of qty (records in)")))
    (do (println "SKIP defrecord-field-access: no Init env or malli absent") (is true))))
