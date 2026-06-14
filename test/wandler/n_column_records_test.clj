(ns wandler.n-column-records-test
  "N-COLUMN RECORDS: the FAQ factorization works over realistic heterogeneous records, not just the
   2-Nat demo. Customers = 2 columns [:cid :region]; Orders = 3 columns [:oid :cid :amount] — DIFFERENT
   arities, joined on a NON-zero column (orders.cid is column 1), aggregating a NON-key column
   (orders.amount is column 2). Field projection is wandler.reducers.record/rget over a right-nested Prod;
   the join/factorization laws are generic over the record types, so multi-column records 'just work'.
   This is the prerequisite for lifting real datahike/stratum tables (which have many typed columns)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc] [wandler.kmap :as km] [wandler.laws.relational :as rl]
            [wandler.optimize :as opt] [wandler.optimize.cost :as cost]
            [wandler.reducers.record :as rec]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as name] [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(def ^:private N    (delay (e/const' (nm "Nat") [])))
(defn- prod [a b]   (e/app* (e/const' (nm "Prod") [z z]) a b))
(defn- listOf [t]   (e/app (e/const' (nm "List") [z]) t))

(defn- build []
  (let [N @N
        custFt [N N]                       ; Customer: [:cid :region]   (2 columns)
        ordFt  [N N N]                      ; Order:    [:oid :cid :amount] (3 columns)
        custRec (prod N N)                  ; right-nested Prod Nat Nat
        ordRec  (prod N (prod N N))         ; right-nested Prod Nat (Prod Nat Nat)
        pairT   (prod custRec ordRec)
        dec (e/const' (nm "instDecidableEqNat") [])
        ;; join key fns via rget — customer.cid = column 0; order.cid = column 1 (NOT column 0!)
        kf (e/lam "c" custRec (rec/rget custFt 0 (e/bvar 0)) :default)
        lf (e/lam "o" ordRec  (rec/rget ordFt  1 (e/bvar 0)) :default)
        join (e/app* (e/const' (nm "Map.join") []) N custRec ordRec dec kf lf (e/fvar 6001) (e/fvar 6002))
        ;; aggregate order.amount = column 2 of the order = column 2 of (snd pair)
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

;; runtime rep of a right-nested Prod = nested pairs:  custRec [cid region];  ordRec [oid [cid amount]]
(def ^:private CUSTS [[1 100] [2 200]])
(def ^:private ORDS  [[10 [1 50]] [11 [1 70]] [12 [2 30]]])    ; Σ amount where cust matches = 50+70+30 = 150

(deftest faq-over-heterogeneous-n-column-records
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [{:keys [sum lctx] :as D} (build)
          sz {6001 1000 6002 1000}
          r (opt/optimize-cost (a/env) sum :lctx lctx :sizes sz)
          run (fn [t] (long (((compile2 D t) CUSTS) ORDS)))]
      (testing "a 2-col ⋈ 3-col join on non-zero columns factors + certifies"
        (is (:verified? r) "certified ≡ naive over N-column records")
        (is (contains? (set (:rewrites r)) :fold-factor) "FAQ factorization fired")
        (is (not (cost/mentions-const? (:term r) "Map.join")) "join eliminated"))
      (testing "field projection (rget) over heterogeneous records executes correctly"
        (is (= 150 (run sum)) "naive Σ orders.amount over custs⋈orders")
        (is (= 150 (run (:term r))) "factored Σ = same answer")))))
