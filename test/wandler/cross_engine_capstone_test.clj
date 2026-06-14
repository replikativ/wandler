(ns wandler.cross-engine-capstone-test
  "Step 3 — the TIMED cross-engine capstone. A 3-way aggregating join whose relations live in DIFFERENT
   engines: customers in a datahike :memory database, orders and line-events in stratum columnar datasets.
   All three share the join key (few distinct values), so the join is many-many-many: the naive cross-DB
   path must MATERIALIZE the |custs|·|orders|·|events| product in app memory (no single engine can do this
   join — it spans two databases). The FAQ-factored wandler plan reads each source ONCE and folds — never
   building the product — and is kernel-certified to compute the SAME Σ.

   The result is the measurement behind 'more optimal without a doubt': as the data grows the naive product
   grows ~cubically while the factored plan stays flat, so the speedup WIDENS — same certified answer at
   every size. This is not a constant-factor SIMD win; it is avoiding a materialization the engines cannot
   avoid on their own.

   Optional: needs :datahike + :stratum + full Init env (see cross_engine_source_test for the invocation)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc] [wandler.kmap :as km] [wandler.laws.relational :as rl]
            [wandler.optimize :as opt] [wandler.optimize.cost :as cost]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as name] [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)

(defn- rr [sym] (try (requiring-resolve sym) (catch Throwable _ nil)))
(def ^:private dh-create  (rr 'datahike.api/create-database))
(def ^:private dh-delete  (rr 'datahike.api/delete-database))
(def ^:private dh-exists? (rr 'datahike.api/database-exists?))
(def ^:private dh-connect (rr 'datahike.api/connect))
(def ^:private dh-transact (rr 'datahike.api/transact))
(def ^:private dh-q       (rr 'datahike.api/q))
(def ^:private st-q       (rr 'stratum.query/q))
(defn- engines? [] (and dh-q st-q @test-env/init-full-env))

;; ── 3-way Σ over custs ⋈ orders ⋈ events, all keyed on Prod.fst, aggregating events' value ────────────
(defn- build3 []
  (let [N (e/const' (nm "Nat") []) NN (e/app* (e/const' (nm "Prod") [z z]) N N)
        PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN) PJ2 (e/app* (e/const' (nm "Prod") [z z]) PJ NN)
        listNN (e/app (e/const' (nm "List") [z]) NN) dec (e/const' (nm "instDecidableEqNat") [])
        cid (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)
        cidPJ (e/lam "r" PJ (e/app* (e/const' (nm "Prod.fst") [z z]) N N
                              (e/app* (e/const' (nm "Prod.fst") [z z]) NN NN (e/bvar 0))) :default)
        join (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid (e/fvar 5001) (e/fvar 5002))
        join3 (e/app* (e/const' (nm "Map.join") []) N PJ NN dec cidPJ cid join (e/fvar 5003))
        val3 (e/lam "p" PJ2 (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                              (e/app* (e/const' (nm "Prod.snd") [z z]) PJ NN (e/bvar 0))) :default)
        amts3 (e/app* (e/const' (nm "List.map") [z z]) PJ2 N val3 join3)
        sum3 (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") [])
                     (e/const' (nm "Nat.zero") []) amts3)]
    {:sum3 sum3 :listNN listNN}))

(defn- compile3 [{:keys [listNN]} t]
  (let [t1 (e/abstract1 t 5003) l3 (e/lam "cc" listNN t1 :default)
        t2 (e/abstract1 l3 5002) l2 (e/lam "ords" listNN t2 :default)
        t3 (e/abstract1 l2 5001) l1 (e/lam "custs" listNN t3 :default)]
    (eval (a/ansatz->clj (a/env) l1 []))))

;; ── engine reads, coerced to the record runtime rep ([key val] = runtime Prod Nat Nat) ───────────────
(def ^:private dh-cfg {:store {:backend :memory :id #uuid "00000000-0000-0000-0000-0000000ca5be"}
                       :schema-flexibility :read :keep-history? false})
(defn- datahike-rel! [rows]
  ;; rows = seq of [k v]; load into datahike, read back as [[k v] …]
  (when (dh-exists? dh-cfg) (dh-delete dh-cfg))
  (dh-create dh-cfg)
  (dh-transact (dh-connect dh-cfg) (mapv (fn [[k v]] {:k k :v v}) rows))
  (vec (map (fn [[k v]] [(long k) (long v)])
            (dh-q '[:find ?k ?v :where [?e :k ?k] [?e :v ?v]] (deref (dh-connect dh-cfg))))))
(defn- stratum-rel [rows]
  ;; rows = seq of [k v]; hold as stratum columns, read back as [[k v] …]
  (let [res (st-q {:from {:k (long-array (map first rows)) :v (long-array (map second rows))}
                   :select [:k :v]})]
    (vec (map (fn [{:keys [k v]}] [(long k) (long v)]) res))))

(defn- t! [f] (f) (let [s (System/nanoTime)] (dotimes [_ 3] (f)) (/ (- (System/nanoTime) s) 3e6)))

(deftest cross-engine-faq-beats-native-materialization
  (if-not (engines?)
    (is true "skipped — needs :datahike + :stratum engines and the full Init env")
    (let [{:keys [sum3 listNN] :as D} (build3)
          lctx {5001 {:name "custs" :type listNN} 5002 {:name "ords" :type listNN} 5003 {:name "cc" :type listNN}}
          R (opt/optimize-cost (a/env) sum3 :lctx lctx :sizes {5001 1000 5002 1000 5003 1000})
          naive (compile3 D sum3)
          fact  (compile3 D (:term R))
          nk 8]
      (testing "certified equal + every cross-engine join eliminated"
        (is (:verified? R) "factored plan kernel-certified ≡ naive")
        (is (contains? (set (:rewrites R)) :fold-factor) "FAQ factorization fired")
        (is (not (cost/mentions-const? (:term R) "Map.join")) "no cross-DB product materialized"))
      (testing "ASYMPTOTIC: naive materializes the cross-engine product (~cubic), factored stays flat"
        (println "  CROSS-ENGINE FAQ CAPSTONE — Σ value over (datahike custs ⋈ stratum orders ⋈ stratum events)")
        (println "    rows/rel   product      datahike+stratum→rows   naive ms   factored ms   speedup")
        (doseq [rows [120 240 480]]
          (let [gen   (fn [off] (vec (map (fn [i] [(mod i nk) (+ off i)]) (range rows))))
                custs (datahike-rel! (gen 0))        ; datahike
                ords  (stratum-rel   (gen 1000))     ; stratum
                cc    (stratum-rel   (gen 2000))     ; stratum
                run   (fn [g] (long (((g custs) ords) cc)))
                prod  (long (* nk (Math/pow (/ rows nk) 3)))
                _     (is (= (run naive) (run fact)) (str "same Σ at rows=" rows))
                tn    (t! #(run naive)) tf (t! #(run fact))]
            (println (format "    %-10d %-12s %-23s %-10.0f %-13.2f %.0f×"
                             rows (format "%,d" prod)
                             (format "%d+%d+%d" (count custs) (count ords) (count cc))
                             tn tf (/ tn (max 0.01 tf))))
            (is (< tf tn) (str "factored faster at rows=" rows))))))))
