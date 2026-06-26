(ns wandler.engine-surface-test
  "The SURFACE PATH for engine sources: a real `datahike.api/q` written INSIDE an `a/defn` combinator
   pipeline elaborates to a typed kernel relation-source leaf, the certified optimizer plans across the
   boundary (here: fuse a map/reduce aggregation over the engine scan), and codegen lowers the leaf to
   the real `d/q` call — coercing the engine's tuples to the kernel's positional record rep. Optional:
   needs :datahike + the full Init env; skips cleanly when either is absent.

   The richer cross-engine plan (factorize a group-by-over-join whose side is the engine scan,
   `[:groupby-reduce-join …]`, 6→4 stages) is proven at the kernel-term level in the cross_engine_*
   tests and demonstrated live in docs/ENGINES.md; this test pins the surface-elaboration mechanism."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.surface.engines :as eng]
            [wandler.test-env :as test-env]))

(defn- rr [sym] (try (requiring-resolve sym) (catch Throwable _ nil)))
(def ^:private sq-q (rr 'stratum.query/q))
(def ^:private dh-create  (rr 'datahike.api/create-database))
(def ^:private dh-delete  (rr 'datahike.api/delete-database))
(def ^:private dh-exists? (rr 'datahike.api/database-exists?))
(def ^:private dh-connect (rr 'datahike.api/connect))
(def ^:private dh-transact (rr 'datahike.api/transact))
(def ^:private dh-q       (rr 'datahike.api/q))
(defn- engines? [] (and dh-q @test-env/init-full-env))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (wc/install!) (wc/install-laws!) (eng/install!))
  (f))
(use-fixtures :once setup)

(def ^:private CCFG {:store {:backend :memory :id #uuid "00000000-0000-0000-0000-0000e0517e57"}
                     :schema-flexibility :read :keep-history? false})

;; the db is a RUNTIME value the embedded query reads at execution time — it must be reachable from the
;; codegen'd fn, i.e. a top-level var (the kernel pipeline never sees it; it lives inside the opaque source).
(def cdb nil)
(def skcol nil)   ; stratum columns (top-level vars, same reachability reason)
(def svcol nil)

(deftest embedded-datahike-query-fuses-and-runs
  (if-not (engines?)
    (is true "skipped — needs :datahike + the full Init env")
    (do
      (when (dh-exists? CCFG) (dh-delete CCFG))
      (dh-create CCFG)
      (let [cconn (dh-connect CCFG)]
        (dh-transact cconn (vec (for [i (range 40)] {:cid i :region (mod i 5)})))
        (alter-var-root #'cdb (constantly @cconn))
        ;; a real datahike query is the SOURCE (cid, region) Prods inside the a/defn aggregation pipeline
        (binding [a/*verbose* false]
          (eval '(ansatz.core/defn sum-regions-test [] Nat
                   (reduce + 0
                           (map (fn [r :- (Prod Nat Nat)] (Prod.snd Nat Nat r))
                                (datahike.api/q '[:find ?cid ?region
                                                  :where [?e :cid ?cid] [?e :region ?region]]
                                                wandler.engine-surface-test/cdb))))))
        ;; a no-arg a/defn binds its var to the EVALUATED constant (the engine query ran once, at
        ;; definition, against the live db) — so we read the value, not call it.
        (let [r    (wc/explain 'sum-regions-test)
              got  (long @(resolve 'sum-regions-test))
              want (->> (dh-q '[:find ?cid ?region :where [?e :cid ?cid] [?e :region ?region]] cdb)
                        (map (fn [[_ region]] (long region))) (reduce + 0))]
          (testing "the map/reduce aggregation fuses across the live engine source, certified"
            (is (true? (:verified? r)) "the plan over the embedded d/q is kernel-certified")
            (is (some #{"map"} (:stages-before r)) "the naive plan has the map over the engine scan")
            (is (not (some #{"map"} (:stages-after r))) "the map is fused into the fold")
            (is (= ["foldl"] (vec (:stages-after r))) "one pass over the engine rows"))
          (testing "and it runs against the live datahike DB, matching brute force"
            (is (= want got))))))))

(deftest embedded-stratum-query-fuses-and-runs
  ;; the SAME surface mechanism over a different engine: stratum.query/q (in-memory columnar) returns a
  ;; vector of maps, coerced to positional Prods by :select order. Skips without :stratum + the Init env.
  (if-not (and sq-q @test-env/init-full-env)
    (is true "skipped — needs :stratum + the full Init env")
    (do
      (alter-var-root #'skcol (constantly (long-array [1 2 1 3])))
      (alter-var-root #'svcol (constantly (long-array [10 20 30 40])))
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn strat-sum-test [] Nat
                 (reduce + 0
                         (map (fn [r :- (Prod Nat Nat)] (Prod.snd Nat Nat r))
                              (stratum.query/q {:from {:k wandler.engine-surface-test/skcol
                                                      :v wandler.engine-surface-test/svcol}
                                                :select [:k :v]}))))))
      (let [r (wc/explain 'strat-sum-test)]
        (testing "the map/reduce aggregation fuses across the live stratum source, certified"
          (is (true? (:verified? r)) "the plan over the embedded stratum.query/q is kernel-certified")
          (is (= ["foldl"] (vec (:stages-after r))) "one pass over the engine rows"))
        (testing "and it runs against stratum, summing the v column"
          (is (= 100 (long @(resolve 'strat-sum-test)))))))))
