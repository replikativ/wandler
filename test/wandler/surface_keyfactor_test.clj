(ns wandler.surface-keyfactor-test
  "L4: the FD scope quotient firing from the CLOJURE SURFACE. A real `a/defn` query over malli
   `def-record`s — a join plus a weight whose left factor reads a function of the join key — auto-floats
   that key-factor into the per-key pre-aggregated index (`:frame-index-keyfactor`), kernel-certified.
   The surface elaborates the field reads to `proj` nodes and the join key to a lambda; the recognizer
   abstracts the build-side read and lets verified-rewrite? gate the key match (the #73 spellings are
   absorbed by def-eq). This is the dependent-types win from real Clojure: a key-determined factor moves
   to the cheaper scope, certified by the kernel. See [[faq-variable-elimination]]."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.surface.records :as wrec]
            [wandler.test-env :as test-env]
            [wandler.optimize :as opt]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest surface-keyfactor-floats-and-certifies
  (when (ready?)
    (testing "a surface a/defn key-factor join auto-adopts :frame-index-keyfactor (FD scope quotient)"
      (wrec/def-record SkfCustomer [:map [:cid [:and :int [:>= 0]]] [:region [:and :int [:>= 0]]]])
      (wrec/def-record SkfOrder    [:map [:cid [:and :int [:>= 0]]] [:amount [:and :int [:>= 0]]]])
      ;; Σ over (custs ⋈ orders on cid):  (succ (:cid customer)) · (:amount order)
      ;; the LEFT factor reads :cid — the join key — so it floats into the per-key index.
      (a/defn skfq [custs :- (List SkfCustomer) orders :- (List SkfOrder)] Nat
        (reduce + 0 (map (fn [p] (Nat.mul (Nat.succ (:cid (first p))) (:amount (second p))))
                         (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders))))
      (let [body (.value (env/lookup (a/env) (nm "skfq")))
            custT (e/const' (nm "SkfCustomer") []) ordT (e/const' (nm "SkfOrder") [])
            cf (e/fvar 96001) of (e/fvar 96002)
            inner (-> body e/lam-body (e/instantiate1 cf) e/lam-body (e/instantiate1 of))
            lctx {96001 {:name "custs" :type (listOf custT)} 96002 {:name "orders" :type (listOf ordT)}}
            res (opt/optimize-cost (a/env) inner :lctx lctx :ndv {96002 3.0})]
        (is (:verified? res) "the surface key-factor float is kernel-certified (frame ∘ float)")
        (is (some #{:frame-index-keyfactor} (:rewrites res)) "frame-index-keyfactor adopted from the surface query")
        (is (= 3.0 (double (get-in res [:physical :index-est]))) "held-index estimate = ndv (distinct keys)")
        (testing "the floated plan runs and equals the naive Σ"
          (let [mk-fn (fn [t] (let [t1 (e/abstract1 t 96002)
                                    ly (e/lam "ys" (listOf ordT) t1 :default)
                                    t2 (e/abstract1 ly 96001)
                                    lx (e/lam "xs" (listOf custT) t2 :default)]
                                (eval (a/ansatz->clj (a/env) lx []))))
                floated (mk-fn (:term res)) naive (mk-fn inner)
                ;; custs cids [1 2], orders [{cid 1} {cid 1} {cid 2} {cid 2}] amounts all = their cid
                CUSTS [{:cid 1 :region 0} {:cid 2 :region 0}]
                ORDERS [{:cid 1 :amount 1} {:cid 1 :amount 1} {:cid 2 :amount 2} {:cid 2 :amount 2}]
                ;; cid1: succ(1)·(1+1)=4 ; cid2: succ(2)·(2+2)=12 ⇒ 16
                expect 16]
            (is (= expect (long ((naive CUSTS) ORDERS))) "naive surface query")
            (is (= expect (long ((floated CUSTS) ORDERS))) "floated plan equals naive")))))))
