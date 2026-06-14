(ns wandler.unified-plan-test
  "Integration 1, first slice: the CONSUMER-AWARE unified planner (wandler.plan/unified-plan). The SAME
   list-producing source pipeline — a customers⋈orders join (the relational/inductive source) — is planned
   for THREE different sinks, and the SINK alone determines the plan:
     :count  → order-invariant → aggregation-through-join / reorder fires (a physical strategy)
     :sum    → order-invariant → aggregation-through-join fires
     :vector → order-PRESERVING → NO order-destroying rewrite (it wouldn't certify as Eq)
   Every plan is kernel-certified ≡ the naive query and executes to the same answer. This is the
   end-to-end source→sink consumer-awareness, with the certificate doing the gating."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.plan :as plan]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (wc/install!)        ; SEAM 3: runtime codegen-registry (so optimized plans execute)
    (km/install!)
    (rl/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; the relational source: custs ⋈ orders on field 0 (a stand-in for a materialized DB table source)
(defn- build []
  (let [N  (e/const' (nm "Nat") [])
        NN (e/app* (e/const' (nm "Prod") [z z]) N N)
        PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN)
        listNN (e/app (e/const' (nm "List") [z]) NN)
        dec (e/const' (nm "instDecidableEqNat") [])
        cid (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)
        custs (e/fvar 5001) ords (e/fvar 5002)
        lctx {5001 {:name "custs" :type listNN} 5002 {:name "ords" :type listNN}}
        join (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid custs ords)
        amount (e/lam "p" PJ (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                                     (e/app* (e/const' (nm "Prod.snd") [z z]) NN NN (e/bvar 0))) :default)]
    {:join join :PJ PJ :N N :amount amount :lctx lctx :listNN listNN :custs-id 5001 :ords-id 5002}))

(defn- compile-fn [{:keys [listNN custs-id ords-id]} t]
  (let [t1 (e/abstract1 t ords-id) ly (e/lam "ords" listNN t1 :default)
        t2 (e/abstract1 ly custs-id) lx (e/lam "custs" listNN t2 :default)]
    (eval (a/ansatz->clj (a/env) lx []))))

(def ^:private CUSTS [[1 10] [2 20] [3 30]])
(def ^:private ORDS  [[1 100] [1 200] [2 50] [3 5] [3 5]])  ; Σ amount = 360, #pairs = 5

(deftest consumer-aware-unified-plan
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [{:keys [join PJ N amount] :as D} (build)
          lctx (:lctx D)
          sz {5001 1000 5002 1000}
          run (fn [t] (((compile-fn D t) CUSTS) ORDS))
          p-count (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ :sink {:kind :count} :sizes sz)
          p-sum   (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ
                                     :sink {:kind :sum :value-fn amount :value-type N} :sizes sz)
          p-vec   (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ :sink {:kind :vector} :sizes sz)]

      (testing "the SINK alone drives the plan (consumer-awareness, gated by the certificate)"
        (is (:verified? p-count) "count plan certified ≡ naive")
        (is (some? (:route p-count)) "order-invariant count sink → a join strategy fired")
        (is (:verified? p-sum) "sum plan certified ≡ naive")
        (is (some? (:route p-sum)) "order-invariant sum sink → aggregation-through-join fired")
        (is (:verified? p-vec) "vector plan certified ≡ naive")
        (is (nil? (:route p-vec)) "order-PRESERVING vector sink → NO order-destroying rewrite")
        (is (:order-invariant? p-count))
        (is (not (:order-invariant? p-vec))))

      (testing "every certified plan executes to the naive answer"
        (is (= 5   (long (run (:term p-count)))) "count = #join pairs")
        (is (= 360 (long (run (:term p-sum))))   "sum = Σ amount")
        (is (= 5   (count (run (:term p-vec))))  "vector = the 5 join pairs (order preserved)"))

      (testing "#1 order-invariance derived from a COMMUTATIVITY certificate, not a hardcoded set"
        ;; a sum whose monoid is NOT commutative (order matters) must be treated as order-preserving —
        ;; even though it's a fold. The hardcoded {count sum group set} would wrongly reorder it.
        (let [p-noncomm (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ
                                           :sink {:kind :sum :value-fn amount :value-type N
                                                  :commutative? false} :sizes sz)]
          (is (plan/order-invariant? {:kind :sum}) "default sum monoid (Nat.add) is commutative")
          (is (plan/order-invariant? {:kind :sum :monoid {:laws {:comm 'Nat.add_comm}}}) "explicit comm proof")
          (is (not (plan/order-invariant? {:kind :sum :commutative? false})) "non-comm sum → order-matters")
          (is (not (plan/order-invariant? {:kind :concat})) "concat/append → order-sensitive")
          (is (not (:order-invariant? p-noncomm)))
          (is (empty? (:rewrites p-noncomm)) "non-commutative sink → no order-destroying rewrite attempted"))))))
