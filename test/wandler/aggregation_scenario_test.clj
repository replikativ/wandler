(ns wandler.aggregation-scenario-test
  "End-to-end: aggregation over nested malli records joined across tables, mixing INT,
   FLOAT and STRING operations — the realistic customer⋈sales report. Exercises the
   Phase-1 faithfulness fixes: Int fields + Int fold-init coercion (the init `0` takes the
   accumulator's Int type, not the reverse), Float aggregation with Float literals, String
   concat codegen, group-by over a record field. Each pipeline compiles, runs, and KERNEL-
   CERTIFIES. See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.collections :as coll]
            [wandler.relational :as rel]
            [wandler.kmap :as kmap]
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

(def ^:private custs [{:id 1 :name "Acme " :region "EU"}
                      {:id 2 :name "Globex " :region "US"}
                      {:id 3 :name "Initech " :region "EU"}])
(def ^:private sales [{:cust-id 1 :amount 100.0 :qty 3}
                      {:cust-id 1 :amount 50.0 :qty 1}
                      {:cust-id 2 :amount 200.0 :qty 5}])

(deftest customer-sales-aggregation
  (if (and @test-env/init-full-env (malli-available?))
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (kmap/install!) (coll/install!) (rel/install!) (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.records/def-record Customer [:map [:id [:int {:min 0}]] [:name :string] [:region :string]]))
        (eval '(wandler.records/def-record Sale [:map [:cust-id [:int {:min 0}]] [:amount :double] [:qty [:int {:min 0}]]]))
        ;; FLOAT: total sales amount over the join
        (eval '(ansatz.core/defn total-amount [cs :- (List Customer), ss :- (List Sale)] Float
                 (reduce (fn [acc p] (add Float acc (:amount (Prod.snd p)))) 0.0
                         (join (fn [c] (:id c)) (fn [s] (:cust-id s)) cs ss))))
        ;; INT: total quantity over the join — init 0 coerces to Int (field is Int)
        (eval '(ansatz.core/defn total-qty [cs :- (List Customer), ss :- (List Sale)] Int
                 (reduce (fn [acc p] (Int.add acc (:qty (Prod.snd p)))) 0
                         (join (fn [c] (:id c)) (fn [s] (:cust-id s)) cs ss))))
        ;; STRING: concatenate customer names
        (eval '(ansatz.core/defn all-names [cs :- (List Customer)] String
                 (reduce (fn [acc c] (String.append acc (:name c))) "" cs)))
        ;; COUNT: number of matched (customer,sale) rows
        (eval '(ansatz.core/defn n-rows [cs :- (List Customer), ss :- (List Sale)] Nat
                 (count (join (fn [c] (:id c)) (fn [s] (:cust-id s)) cs ss))))
        ;; GROUP-BY a record field (String key)
        (eval '(ansatz.core/defn by-region [cs :- (List Customer)] (Map String (List Customer))
                 (group-by (fn [c] (:region c)) cs)))
        ;; WHERE + aggregate: FLOAT comparison predicate (decide-bridge → Bool), filter
        ;; FUSES into the fold (foldl_filter) — total of sales with amount > 75.0
        (eval '(ansatz.core/defn big-total [ss :- (List Sale)] Float
                 (reduce (fn [acc s] (add Float acc (:amount s))) 0.0
                         (filterv (fn [s] (> (:amount s) 75.0)) ss)))))
      ;; all five kernel-certify
      (is (true? (kernel-checks? "total-amount")) "float aggregation certifies")
      (is (true? (kernel-checks? "total-qty"))    "int aggregation certifies")
      (is (true? (kernel-checks? "all-names"))    "string concat certifies")
      (is (true? (kernel-checks? "n-rows"))       "count-of-join certifies")
      (is (true? (kernel-checks? "by-region"))    "group-by certifies")
      (is (true? (kernel-checks? "big-total"))    "float WHERE+aggregate certifies")
      ;; and compute the right thing
      (is (== 350.0 ((resolve 'total-amount) custs sales)) "100+50+200 = 350.0")
      (is (== 9     ((resolve 'total-qty)    custs sales)) "3+1+5 = 9")
      (is (= "Acme Globex Initech " ((resolve 'all-names) custs)) "names concatenated")
      (is (= 3      ((resolve 'n-rows)       custs sales)) "3 matched rows")
      (is (= 2      (count ((resolve 'by-region) custs)))  "EU + US groups")
      (is (== 300.0 ((resolve 'big-total) sales)) "WHERE amount>75: 100+200 = 300.0"))
    (do (println "SKIP customer-sales-aggregation: no Init env or malli absent") (is true))))
