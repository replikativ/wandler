(ns wandler.bridge-stratum-test
  "The stratum adapter (wandler.bridge.stratum): columnar logical IR ↔ kernel terms, including
   COMPILING stratum's structured `[col op arg]` predicates into kernel lambdas. Plus the
   CROSS-ENGINE payoff: a pipeline mixing a datahike source and a stratum source, joined and
   aggregated, optimized ONCE in the certified kernel IR and lowerable per engine."
  (:require [ansatz.core :as a]
            [wandler.bridge :as bridge]
            [wandler.bridge.stratum :as st]
            [wandler.bridge.datahike :as dh]
            [wandler.optimize :as opt]
            [wandler.rel-laws :as rl]
            [wandler.kmap :as kmap]
            [wandler.plan :as plan]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private nat (e/const' (nm "Nat") []))
(def ^:private prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat))
(def ^:private deceq (e/const' (nm "instDecidableEqNat") []))
(def ^:private listN (e/app (e/const' (nm "List") [z]) nat))
(def ^:private idf (e/lam "x" nat (e/bvar 0) :default))

(deftest stratum-structured-predicates-compile-and-lift
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (is (contains? (bridge/registered-engines) :stratum) "stratum adapter registered")
      ;; a columnar filter: keep rows where col0 > 5 AND col1 < 100  (Prod Nat Nat rows)
      (let [scan (e/fvar 7)
            q    {:op :filter :predicates [[0 :> 5] [1 :< 100]] :in {:op :scan :src scan}}
            term (st/lift q prodNN)
            pl   (plan/term->plan term)]
        ;; the structured predicates became one kernel filter over a list of Prod rows
        (is (= :filter (:op pl)) "stratum LFilter → List.filter")
        (is (= :source (:op (:input pl))))
        ;; γ-lower → stratum PSIMDFilter over the scan
        (let [lo (st/lower pl)]
          (is (= :simd-filter (:op lo)) "γ-lowers to a stratum SIMD filter")
          (is (= :scan (:op (:in lo)))))))
    (do (println "SKIP stratum test: no Init env") (is true))))

(deftest cross-engine-pipeline-optimizes-and-certifies
  ;; THE CROSS-ENGINE PAYOFF. `users` comes from datahike (q over an entity), `orders` from a
  ;; stratum columnar table; they're joined on id=user and the amounts summed:
  ;;   sum (map amount (join id user (datahike users) (stratum orders)))
  ;; Ansatz optimizes the WHOLE thing ONCE in the certified kernel IR — the aggregation-through-join
  ;; factorization fires (never materialize the users·orders product) — then each source γ-lowers to
  ;; ITS engine (users → datahike, orders → stratum). One verified plan across two engines.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (rl/install!)
      (let [users  (e/fvar 3)   ; ← datahike scan
            orders (e/fvar 4)   ; ← stratum scan
            join   (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq idf idf users orders)
            amount (e/lam "p" prodNN (e/app* (e/const' (nm "Prod.snd") [z z]) nat nat (e/bvar 0)) :default)
            mapped (e/app* (e/const' (nm "List.map") [z z]) prodNN nat amount join)
            total  (e/app* (e/const' (nm "List.foldl") [z z]) nat nat (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) mapped)
            lctx   {3 {:name "users" :type listN} 4 {:name "orders" :type listN}}
            ;; per-source cardinality from each engine's :estimate (datahike: 1e4 users; stratum: 1e6 orders)
            res    (opt/optimize-cost (a/env) total :lctx lctx :sizes {3 10000.0 4 1000000.0})
            ;; tag which source belongs to which engine, then γ-lower each through its adapter
            engine-of {3 :datahike 4 :stratum}
            lower-src (fn lower-src [pl]
                        (if (= :source (:op pl))
                          (let [fid (e/fvar-id (:term pl))]
                            {:engine (engine-of fid) :scan ((case (engine-of fid) :datahike dh/lower :stratum st/lower) pl)})
                          pl))]
        (is (contains? (set (:rewrites res)) :fold-factor) "cross-engine aggregation-through-join factorization fired")
        (is (true? (:verified? res)) "the cross-engine plan ≡ the original is kernel-certified")
        ;; both engine sources survive into the optimized plan (it references users AND orders)
        (let [s (e/->string (:term res))]
          (is (clojure.string/includes? s "fv3") "datahike users source present (the outer driver)")
          (is (clojure.string/includes? s "fv4") "stratum orders source present (under the per-key group_by)"))
        ;; and each source lowers to its own engine
        (is (= :datahike (:engine (lower-src {:op :source :term users}))))
        (is (= :stratum  (:engine (lower-src {:op :source :term orders}))))))
    (do (println "SKIP cross-engine test: no Init env") (is true))))
