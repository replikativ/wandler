(ns wandler.cross-engine-source-test
  "Step 2 of the cross-engine plan: a SOURCE LEAF is LOWERED to a REAL ENGINE READ.

   Customers live in a datahike database; orders live in a stratum columnar dataset. Neither engine can
   join across the OTHER engine's boundary — so the naive cross-engine path pulls both sides and
   materializes the |custs|·|orders| join in app memory. The FAQ-factored wandler plan reads each source
   ONCE (join-free) and folds — the SAME kernel-certified Σ, with no cross-engine product ever built.

   The 'lowering' is exactly this: bind the plan's source parameter to the engine query result, coerced
   to the record runtime rep. The factored kernel term is engine-agnostic at the source boundary, and the
   certificate (factored ≡ naive) does not care where the rows came from. `lower-source` below makes the
   leaf→engine-read step literal: a {:engine :datahike} leaf becomes a d/q; a {:engine :stratum} leaf
   becomes a stratum q/q.

   Optional: needs both the :datahike and :stratum engines on the classpath AND the full Init env. Skips
   (single trivial assertion) when either is absent — run it with, e.g.:
     clj -Sdeps '{:aliases {:x {:extra-paths [\"test\"]
                                 :extra-deps {org.replikativ/stratum {:local/root \"../stratum\"}
                                              org.replikativ/datahike {:local/root \"../datahike\"}}
                                 :jvm-opts [\"--add-modules=jdk.incubator.vector\"]}}}' \\
       -M:x -e \"(require 'wandler.cross-engine-source-test)(clojure.test/run-tests 'wandler.cross-engine-source-test)\""
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc] [wandler.kmap :as km] [wandler.laws.relational :as rl]
            [wandler.clean.optimize :as opt] [wandler.clean.optimize.cost :as cost]
            [wandler.reducers.record :as rec]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as name] [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)

;; ── optional engine handles (nil if the engine isn't on the classpath) ───────────────────────────────
(defn- rr [sym] (try (requiring-resolve sym) (catch Throwable _ nil)))
(def ^:private dh-create  (rr 'datahike.api/create-database))
(def ^:private dh-delete  (rr 'datahike.api/delete-database))
(def ^:private dh-exists? (rr 'datahike.api/database-exists?))
(def ^:private dh-connect (rr 'datahike.api/connect))
(def ^:private dh-transact (rr 'datahike.api/transact))
(def ^:private dh-q       (rr 'datahike.api/q))
(def ^:private st-q       (rr 'stratum.query/q))
(defn- engines? [] (and dh-q st-q @test-env/init-full-env))

;; ── the (engine-agnostic) factored plan over 2-col customers ⋈ 3-col orders, aggregating amount ──────
(def ^:private N    (delay (e/const' (nm "Nat") [])))
(defn- prod [a b]   (e/app* (e/const' (nm "Prod") [z z]) a b))
(defn- listOf [t]   (e/app (e/const' (nm "List") [z]) t))

(defn- build []
  (let [N @N
        custFt [N N]  ordFt [N N N]
        custRec (prod N N)  ordRec (prod N (prod N N))
        pairT (prod custRec ordRec)
        dec (e/const' (nm "instDecidableEqNat") [])
        kf (e/lam "c" custRec (rec/rget custFt 0 (e/bvar 0)) :default)         ; customer.cid = col 0
        lf (e/lam "o" ordRec  (rec/rget ordFt  1 (e/bvar 0)) :default)         ; order.cid    = col 1
        join (e/app* (e/const' (nm "Map.join") []) N custRec ordRec dec kf lf (e/fvar 6001) (e/fvar 6002))
        amount (e/lam "p" pairT (rec/rget ordFt 2 (e/app* (e/const' (nm "Prod.snd") [z z]) custRec ordRec (e/bvar 0))) :default)
        amts (e/app* (e/const' (nm "List.map") [z z]) pairT N amount join)
        sum  (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") [])
                     (e/const' (nm "Nat.zero") []) amts)]
    {:sum sum :custRec custRec :ordRec ordRec
     :lctx {6001 {:name "custs" :type (listOf custRec)} 6002 {:name "ords" :type (listOf ordRec)}}}))

(defn- compile2 [{:keys [custRec ordRec]} t]
  (let [t1 (e/abstract1 t 6002) l2 (e/lam "ords" (listOf ordRec) t1 :default)
        t2 (e/abstract1 l2 6001) l1 (e/lam "custs" (listOf custRec) t2 :default)]
    (eval (a/ansatz->clj (a/env) l1 []))))

;; ── lower a SOURCE LEAF to its engine read, coerced to the record runtime rep ────────────────────────
;; Customer rec rep = [cid region]; Order rec rep (right-nested Prod) = [oid [cid amount]].
(defn- lower-source [leaf]
  (case (:engine leaf)
    :datahike (let [{:keys [cfg]} leaf
                    rows (dh-q '[:find ?cid ?region :where [?e :cid ?cid] [?e :region ?region]] (deref (dh-connect cfg)))]
                (vec (sort-by first (map (fn [[cid region]] [(long cid) (long region)]) rows))))
    :stratum  (let [rows ((:reader leaf))]                ; stratum q/q already run → vector of row maps
                (vec (map (fn [{:keys [oid cid amount]}] [(long oid) [(long cid) (long amount)]]) rows)))))

(defn- fresh-datahike-customers! []
  (let [cfg {:store {:backend :memory :id #uuid "00000000-0000-0000-0000-00000000c0de"}
             :schema-flexibility :read :keep-history? false}]
    (when (dh-exists? cfg) (dh-delete cfg))
    (dh-create cfg)
    (dh-transact (dh-connect cfg) [{:cid 1 :region 100} {:cid 2 :region 200}])
    {:engine :datahike :cfg cfg}))

(defn- stratum-orders-leaf []
  {:engine :stratum
   :reader #(st-q {:from {:oid (long-array [10 11 12])
                          :cid (long-array [1 1 2])
                          :amount (long-array [50 70 30])}
                   :select [:oid :cid :amount]})})

(deftest faq-over-cross-engine-sources
  (if-not (engines?)
    (is true "skipped — needs :datahike + :stratum engines and the full Init env")
    (let [{:keys [sum lctx] :as D} (build)
          sz {6001 1000 6002 1000}
          r (opt/optimize-cost (a/env) sum :lctx lctx :sizes sz)
          ;; lower each source LEAF to its real engine read (datahike customers, stratum orders)
          custs (lower-source (fresh-datahike-customers!))
          ords  (lower-source (stratum-orders-leaf))
          run (fn [t] (long (((compile2 D t) custs) ords)))]
      (testing "sources came from two different real engines"
        (is (= [[1 100] [2 200]] custs) "customers read from datahike")
        (is (= [[10 [1 50]] [11 [1 70]] [12 [2 30]]] ords) "orders read from stratum"))
      (testing "the factored plan is certified ≡ naive and eliminates the cross-engine join"
        (is (:verified? r) "factored ≡ naive (certificate is engine-agnostic)")
        (is (contains? (set (:rewrites r)) :fold-factor) "FAQ factorization fired")
        (is (not (cost/mentions-const? (:term r) "Map.join")) "no cross-engine product materialized")
        (is (< (double (cost/pipeline-cost (:term r) {:sizes sz}))
               (double (cost/pipeline-cost sum {:sizes sz}))) "cheaper than materializing the join"))
      (testing "both plans execute over the cross-engine data to the same Σ amount"
        (is (= 150 (run sum)) "naive Σ amount over (datahike custs ⋈ stratum orders)")
        (is (= 150 (run (:term r))) "factored Σ = same answer, join-free")))))
