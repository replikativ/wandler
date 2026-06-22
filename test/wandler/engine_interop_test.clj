(ns wandler.engine-interop-test
  "WORKED EXAMPLE — how datahike's query engine and the streaming/aggregation engine plan together as ONE
   certified plan, with predicates pushed across the seam in BOTH directions.

   The scenario: `total amount of ACTIVE orders, per customer`.
     datahike holds the facts:  [?o :order/customer ?c]  [?o :order/amount ?amt]  [?o :order/status ?s]
     we want:                   Σ amount  GROUP BY customer  WHERE status = :active

   The division of labour the planner discovers:
     • datahike (index engine) is great at PATTERN-MATCHING facts — its AVET index turns `status=:active`
       into a direct lookup. → push the `:active` predicate DOWN into datahike (streaming → query).
     • the streaming engine is great at AGGREGATES — the Σ-by-customer is a semiring sum-product (the same
       FAQ machinery as `wandler.inference.semiring/q`). datahike doesn't aggregate well; keep it in the stream.

   Direction 1 (streaming → query): a filter that sits ABOVE a datahike scan is pushed INTO the scan, so
     datahike's index does it and returns only matching datoms.  (Map.filter_join_pushdown, CERTIFIED.)
   Direction 2 (query → streaming): a filter over a PROJECTED scan is lifted BELOW the projection
     (filter_map), so we never map/aggregate over rows that will be dropped — and the lifted filter is then
     itself index-pushable.  (filterMap / filter_map, CERTIFIED.)

   Every rewrite is kernel-checked (verified? = the cross-engine plan ≡ the original), so it is SAFE to let
   datahike do part of the work: the proof is independent of which engine runs which piece."
  (:require [ansatz.core :as a]
            [wandler.bridge :as bridge]
            [wandler.bridge.datahike :as dh]
            [wandler.optimize :as opt]
            [wandler.laws.faq :as rl]
            [wandler.kmap :as kmap]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is testing]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private nat (e/const' (nm "Nat") []))
(def ^:private boolT (e/const' (nm "Bool") []))
(def ^:private prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat))
(def ^:private deceq (e/const' (nm "instDecidableEqNat") []))
(def ^:private listN (e/app (e/const' (nm "List") [z]) nat))
(def ^:private idf (e/lam "x" nat (e/bvar 0) :default))

(deftest streaming-to-query-pushdown
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv) (kmap/install!) (rl/install!)
      (testing "a predicate on the orders side is PUSHED INTO datahike's scan (its index does the filter)"
        ;; orders ⋈ customers on customer-id, with a filter `active?` on the ORDERS row (the join's left).
        (let [orders (e/fvar 3) customers (e/fvar 4) active? (e/fvar 2)
              ;; the predicate reads the order row's status field (fst of the (id,status) pair)
              pred (e/lam "o" prodNN (e/app active? (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
              query {:op :filter :pred pred
                     :in {:op :join :key-type nat :row nat :deceq deceq :kf idf :lf idf
                          :left {:op :scan :src orders} :right {:op :scan :src customers}}}
              lctx {2 {:name "active?" :type (e/forall' "_" nat boolT :default)}
                    3 {:name "orders" :type listN} 4 {:name "customers" :type listN}}
              {:keys [plan verified? rewrites]}
              (bridge/optimize-plan (a/env) (fn [ir] (dh/lift ir nat)) query :lctx lctx)]
          (is (true? verified?) "the cross-engine optimization is kernel-CERTIFIED (plan ≡ original)")
          (is (contains? (set rewrites) "Map.filter_join_pushdown") "the filter was pushed into the join")
          ;; γ-lower → datahike logical IR: the filter now lives INSIDE the orders scan ⇒ datahike's index
          ;; returns only active orders; the join stays for the cross-engine plan.
          (let [ir (dh/lower plan)]
            (is (= :entity-join (:op ir)) "γ-lowers to a datahike entity-join")
            (is (= :filter (:op (:left ir))) "…with `active?` pushed into the LEFT (orders) input")
            (is (= :scan (:op (:in (:left ir)))) "…directly over the orders scan (datahike does it)")
            (is (= :scan (:op (:right ir))) "…and customers is scanned unfiltered")))))
    (do (println "SKIP engine-interop: no Init env") (is true))))

(deftest query-to-streaming-lift
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv) (kmap/install!) (rl/install!)
      (testing "a filter over a PROJECTED scan is lifted BELOW the projection (don't map over doomed rows)"
        ;; `filter active? (map proj orders)` — naive: map EVERY order, THEN drop inactive.
        ;; the optimizer lifts the filter below the map: `map proj (filter (active?∘proj) orders)` — so the
        ;; projection only runs on survivors, and the filter is now at the source (index-pushable).
        (let [orders (e/fvar 1) proj (e/fvar 2) active? (e/fvar 3)
              mapped (e/app* (e/const' (nm "List.map") [z z]) nat nat proj orders)
              q      (e/lam "v" nat (e/app active? (e/bvar 0)) :default)
              term   (e/app* (e/const' (nm "List.filter") [z]) nat q mapped)
              lctx   {1 {:name "orders" :type listN}
                      2 {:name "proj" :type (e/forall' "_" nat nat :default)}
                      3 {:name "active?" :type (e/forall' "_" nat boolT :default)}}
              {:keys [verified? rewrites]} (opt/optimize-cost (a/env) term :lctx lctx)]
          (is (true? verified?) "the lift is kernel-CERTIFIED")
          ;; the optimizer fused/lifted: it recognized filter-over-map and produced a single pass that
          ;; doesn't materialize the projection of dropped rows (filterMap / filter_map).
          (is (some #(re-find #"filter" (str %)) rewrites) (str "a filter rewrite fired: " (vec rewrites))))))
    (do (println "SKIP engine-interop lift: no Init env") (is true))))
