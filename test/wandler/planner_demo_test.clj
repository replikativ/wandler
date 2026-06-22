(ns wandler.planner-demo-test
  "END-TO-END PLANNER DEMO — one Malli-typed dataset (customers ⋈ orders on cid), four certified
   PHYSICAL join strategies, each kernel-verified AND executed on real data via codegen. This is the
   legible 'look at the whole planner' surface: the SAME logical query, optimized under different
   resource regimes, picks a different physical plan — and `opt/explain` says why.

     query              regime                         strategy          why
     ─────────────────  ─────────────────────────────  ────────────────  ────────────────────────────
     Σ amount (sum)     generous memory                :in-memory-hash   build the group_by index once
     Σ amount (sum)     tiny memory-budget             :nested-loop      drop the index → per-row filter
     Σ amount (sum)     ndv ≪ |orders| (the oracle)    :pre-agg-index    buckets pre-summed, O(distinct)
     count (foldl-succ) memory-budget < index          :grace-hash       spill build side into blocks

   (Sum vs count split is principled: grace-hash's rfl left-commutativity holds for the p-independent
   COUNT; the separable SUM is what unlocks the pre-aggregated index — see [[pre-aggregated-faq-index]].)
   Every adopted plan is certified by `verified-rewrite?` (kernel check-constant), and here we go one
   step further: codegen each to a Clojure fn and confirm it computes the SAME answer as the naive plan.
   See docs/SPILL_AND_FAQ_PLAN.md, [[rel-laws-installer]]."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.faq :as rl]
            [wandler.surface.malli :as am]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [wandler.optimize :as opt]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (wc/install!)        ; SEAM 3: runtime codegen-registry — so the codegen'd plans execute standalone
    (km/install!)
    (rl/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; ── the Malli-typed dataset: customers {cid,tier}, orders {cid,amount} ──────────
;; malli-record gives the typed record MODEL (the schema boundary); the runnable pipeline
;; instantiates the scalar fields as Nat (cid/amount are non-negative counts), which is what makes
;; the amount SUM a Nat monoid (so the pre-aggregated index applies).
(def ^:private customer-schema [:map [:cid :int] [:tier :int]])
(def ^:private order-schema    [:map [:cid :int] [:amount :int]])

(defn- build []
  (let [N  (e/const' (nm "Nat") [])
        NN (e/app* (e/const' (nm "Prod") [z z]) N N)         ; a 2-field record, fields as Nat
        PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN)       ; a join pair (customer, order)
        listNN (e/app (e/const' (nm "List") [z]) NN)
        dec (e/const' (nm "instDecidableEqNat") [])
        cid (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)  ; join key = field 0
        custs (e/fvar 5001) ords (e/fvar 5002)
        lctx {5001 {:name "custs" :type listNN} 5002 {:name "ords" :type listNN}}
        join (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid custs ords)
        ;; Σ amount: sum field-1 of the ORDER (snd of the pair) — a SEPARABLE sum (reads only the build row)
        amount (e/lam "p" PJ (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                               (e/app* (e/const' (nm "Prod.snd") [z z]) NN NN (e/bvar 0))) :default)
        amts (e/app* (e/const' (nm "List.map") [z z]) PJ N amount join)
        sum-term (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") [])
                         (e/const' (nm "Nat.zero") []) amts)
        ;; count: foldl (λacc _. succ acc) — p-INDEPENDENT (grace-hash's rfl left-commutativity holds)
        cntOp (e/lam "acc" N (e/lam "p" PJ (e/app (e/const' (nm "Nat.succ") []) (e/bvar 1)) :default) :default)
        cnt-term (e/app* (e/const' (nm "List.foldl") [z z]) N PJ cntOp (e/const' (nm "Nat.zero") []) join)]
    {:sum-term sum-term :cnt-term cnt-term :lctx lctx :listNN listNN
     :custs-id 5001 :ords-id 5002}))

(defn- compile-fn [{:keys [listNN custs-id ords-id]} t]
  ;; abstract the two source fvars into a curried 2-arg fn, codegen, eval
  (let [t1 (e/abstract1 t ords-id)
        ly (e/lam "ords" listNN t1 :default)
        t2 (e/abstract1 ly custs-id)
        lx (e/lam "custs" listNN t2 :default)]
    (eval (a/ansatz->clj (a/env) lx []))))

;; sample data — matches: cid 1→{100,200}, 2→{50}, 3→{5,5}; Σ amount = 360, #pairs = 5
(def ^:private CUSTS [[1 10] [2 20] [3 30]])
(def ^:private ORDS  [[1 100] [1 200] [2 50] [3 5] [3 5]])

(deftest malli-boundary-parses-the-typed-records
  (when (ready?)
    (testing "the Malli schemas yield 2-field record models (the typed boundary the planner rides on)"
      (let [c (am/malli-record customer-schema)
            o (am/malli-record order-schema)]
        (is (= [:cid :tier] (:keys c)))
        (is (= {:cid 0 :tier 1} (:index c)))
        (is (= [:cid :amount] (:keys o)))
        (is (= {:cid 0 :amount 1} (:index o)))))))

(deftest four-physical-strategies-on-one-pipeline
  (when (ready?)
    (let [{:keys [sum-term cnt-term lctx] :as D} (build)
          sz {5001 1000 5002 1000}
          ;; SAME sum query, three regimes:
          r-hash (opt/optimize-cost (a/env) sum-term :lctx lctx :sizes sz)
          r-nl   (opt/optimize-cost (a/env) sum-term :lctx lctx :sizes sz :memory-budget 1.0)
          r-pa   (opt/optimize-cost (a/env) sum-term :lctx lctx :sizes sz :ndv {5002 3.0})
          ;; count query, spill regime:
          r-gh   (opt/optimize-cost (a/env) cnt-term :lctx lctx :sizes sz :memory-budget 50.0)
          run (fn [t] (long (((compile-fn D t) CUSTS) ORDS)))]

      (testing "in-memory HASH (generous memory): factorize + hoist the index out of the row loop"
        (is (true? (:verified? r-hash)))
        (is (= :in-memory-hash (get-in r-hash [:physical :strategy])))
        (is (contains? (set (:rewrites r-hash)) :hoist-index))
        (is (str/includes? (opt/explain r-hash) "IN-MEMORY HASH")))

      (testing "NESTED-LOOP (tiny budget): drop the held index → per-row filter"
        (is (true? (:verified? r-nl)))
        (is (= :nested-loop (get-in r-nl [:physical :strategy])))
        (is (str/includes? (opt/explain r-nl) "NESTED-LOOP")))

      (testing "PRE-AGGREGATED index (ndv oracle ≪ |orders|): buckets pre-summed, O(distinct keys)"
        (is (true? (:verified? r-pa)))
        (is (= :in-memory-hash (get-in r-pa [:physical :strategy])))
        (is (contains? (set (:rewrites r-pa)) :pre-agg-index))
        (is (= 3.0 (double (get-in r-pa [:physical :index-est]))) "held-index est = ndv, not |orders|"))

      (testing "GRACE-HASH (count, budget < index): spill build side into budget-sized blocks"
        (is (true? (:verified? r-gh)))
        (is (= :grace-hash (get-in r-gh [:physical :strategy])))
        (is (str/includes? (opt/explain r-gh) "GRACE-HASH")))

      (testing "every certified plan EXECUTES to the same answer as the naive plan"
        (is (= 360 (run sum-term)) "naive Σ amount")
        (is (= 360 (run (:term r-hash))) "in-memory hash Σ")
        (is (= 360 (run (:term r-nl)))   "nested-loop Σ")
        (is (= 360 (run (:term r-pa)))   "pre-aggregated Σ")
        (is (= 5 (run cnt-term))         "naive count")
        (is (= 5 (run (:term r-gh)))     "grace-hash count")))))
