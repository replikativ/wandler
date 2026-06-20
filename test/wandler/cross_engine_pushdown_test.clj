(ns wandler.cross-engine-pushdown-test
  "Step 4 — PREDICATE PUSHDOWN into the engines. The wandler plan carries a kernel filter on the order
   source (amount ≥ 50) BEFORE the join — `List.filter (λo. Nat.ble 50 (amount o)) orders`. That filter
   is the CERTIFIED SPEC. Pushing it down means lowering it into the engine's own scan: stratum runs it
   as `:where [[:>= :amount 50]]`, so only matching rows ever cross the engine boundary.

   Two things are demonstrated:
   (1) DIFFERENTIAL validation of the lowering — the engine's `:where` result is row-for-row equal to the
       kernel predicate applied to the unfiltered read. The engine is a TRUSTED oracle (we do not kernel-
       prove stratum's `:where`); the kernel filter is the spec it is validated against. This is the same
       trust boundary as datahike-as-oracle in the architecture.
   (2) The pushdown is a WIN at two layers: fewer rows cross the engine boundary (measured), AND the
       certified relational law `filter (p∘snd) (join …) = join … (filter p)` lets the optimizer move a
       join-level filter to the source in the first place (wandler.clean.optimize.cost / filter-join-test), so
       the cost model sees the reduced source size (selectivity) and prefers the pushed plan.

   Optional: needs :stratum + full Init env (datahike side reused from cross_engine_source_test)."
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

(defn- rr [sym] (try (requiring-resolve sym) (catch Throwable _ nil)))
(def ^:private st-q (rr 'stratum.query/q))
(defn- engines? [] (and st-q @test-env/init-full-env))

(def ^:private THRESHOLD 50)

;; ── the plan: Σ amount over (custs ⋈ (filter amount≥THRESHOLD orders)) ───────────────────────────────
(def ^:private N (delay (e/const' (nm "Nat") [])))
(defn- prod [a b] (e/app* (e/const' (nm "Prod") [z z]) a b))
(defn- listOf [t] (e/app (e/const' (nm "List") [z]) t))

(defn- build []
  (let [N @N
        custFt [N N]  ordFt [N N]                          ; Customer [:cid :region]  Order [:cid :amount]
        custRec (prod N N)  ordRec (prod N N)
        pairT (prod custRec ordRec)
        dec (e/const' (nm "instDecidableEqNat") [])
        kf (e/lam "c" custRec (rec/rget custFt 0 (e/bvar 0)) :default)            ; customer.cid
        lf (e/lam "o" ordRec  (rec/rget ordFt  0 (e/bvar 0)) :default)           ; order.cid
        ;; the pushed-down predicate, as a CERTIFIED kernel filter: λo. Nat.ble THRESHOLD o.amount
        pred (e/lam "o" ordRec (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat THRESHOLD)
                                       (rec/rget ordFt 1 (e/bvar 0))) :default)
        filtered (e/app* (e/const' (nm "List.filter") [z]) ordRec pred (e/fvar 8002))
        join (e/app* (e/const' (nm "Map.join") []) N custRec ordRec dec kf lf (e/fvar 8001) filtered)
        amount (e/lam "p" pairT (rec/rget ordFt 1 (e/app* (e/const' (nm "Prod.snd") [z z]) custRec ordRec (e/bvar 0))) :default)
        amts (e/app* (e/const' (nm "List.map") [z z]) pairT N amount join)
        sum  (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") [])
                     (e/const' (nm "Nat.zero") []) amts)]
    {:sum sum :custRec custRec :ordRec ordRec
     :lctx {8001 {:name "custs" :type (listOf custRec)} 8002 {:name "ords" :type (listOf ordRec)}}}))

(defn- compile2 [{:keys [custRec ordRec]} t]
  (let [t1 (e/abstract1 t 8002) l2 (e/lam "ords" (listOf ordRec) t1 :default)
        t2 (e/abstract1 l2 8001) l1 (e/lam "custs" (listOf custRec) t2 :default)]
    (eval (a/ansatz->clj (a/env) l1 []))))

;; ── stratum order source: read WITHOUT vs WITH the predicate pushed into the engine ──────────────────
(def ^:private ORDER-COLS {:cid    (long-array [1 1 2 2 1])
                           :amount (long-array [30 70 50 20 90])})   ; ≥50 ⇒ keep amounts 70,50,90 = 210
(defn- stratum-orders [where]
  (vec (map (fn [{:keys [cid amount]}] [(long cid) (long amount)])
            (st-q (cond-> {:from ORDER-COLS :select [:cid :amount]}
                    where (assoc :where where))))))

(def ^:private CUSTS [[1 100] [2 200]])

(deftest predicate-pushdown-into-stratum
  (if-not (engines?)
    (is true "skipped — needs :stratum engine and the full Init env")
    (let [{:keys [sum lctx] :as D} (build)
          plan (compile2 D sum)                              ; ONE plan, kernel filter amount≥50 inside
          full   (stratum-orders nil)                        ; engine returns ALL orders
          pushed (stratum-orders [[:>= :amount THRESHOLD]])  ; engine runs the predicate (:where)
          run (fn [ords] (long ((plan CUSTS) ords)))]
      (testing "(1) the engine :where is a faithful lowering of the kernel predicate (differential)"
        (is (= (vec (sort (filter (fn [[_ a]] (>= a THRESHOLD)) full)))
               (vec (sort pushed)))
            "stratum :where result = kernel filter (Nat.ble 50) applied to the full read"))
      (testing "(2) fewer rows cross the engine boundary when the predicate is pushed"
        (is (= 5 (count full)) "without pushdown: all 5 orders cross")
        (is (= 3 (count pushed)) "with pushdown: only the 3 matching orders cross")
        (is (< (count pushed) (count full))))
      (testing "(3) same certified Σ either way — the kernel filter is the spec, the engine pre-filter is sound"
        (is (= 210 (run full)) "Σ amount, predicate run by the kernel filter")
        (is (= 210 (run pushed)) "Σ amount, predicate run by stratum (kernel filter idempotent)"))
      (testing "(4) the cost model prefers the pushed plan: reduced source size lowers pipeline-cost"
        (let [c-full   (cost/pipeline-cost sum {:sizes {8001 1000 8002 1000}})
              c-pushed (cost/pipeline-cost sum {:sizes {8001 1000 8002 (* 1000 3/5)}})] ; 3/5 selectivity
          (is (< (double c-pushed) (double c-full))
              "pushing the predicate into the engine shrinks the source the join must probe"))))))
