(ns wandler.frame-index-test
  "FAQ FRAME RULE wired into the optimizer (Phase 3): a SEPARABLE two-sided weight over a join

     foldl (λacc p. acc + f(fst p)·g(snd p)) e (Map.join kf lf xs ys)

   auto-selects the O(distinct-keys) pre-aggregated FRAME index via the kernel-proven
   Map.foldl_join_frame — Σ_{x⋈y} f(x)·g(y) = Σ_x f(x)·(Σ_{y∈bucket(x)} g(y)). The probe-side weight
   f(x) is applied AFTER the per-key lookup into the SAME g-pre-summed index used by the f≡1 pre-agg
   path; `separable-frame-fg` recognizes the op shape directly off the elaborated term (no malli scope
   analysis needed for the separable case). ndv-gated (DuckDB-style), certified by verified-rewrite?,
   and the chosen plan EXECUTES = naive. See [[faq-variable-elimination]]."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [wandler.optimize :as opt]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- natT [] (e/const' (nm "Nat") []))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv) (wc/install!) (km/install!) (rl/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; separable TWO-SIDED weighted SUM over a join: weight = f(fst p)·g(snd p), f = g = identity
;; (so the per-pair weight is x·y), kf = lf = identity.
(defn- frame-join-term []
  (let [Nat (natT) PXY (prodT Nat Nat)
        dec (e/const' (nm "instDecidableEqNat") [])
        idf (e/lam "n" Nat (e/bvar 0) :default)
        xs (e/fvar 72001) ys (e/fvar 72002)
        fstp (e/app* (e/const' (nm "Prod.fst") [z z]) Nat Nat (e/bvar 0))
        sndp (e/app* (e/const' (nm "Prod.snd") [z z]) Nat Nat (e/bvar 0))
        op (e/lam "acc" Nat (e/lam "p" PXY
             (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1)
                     (e/app* (e/const' (nm "Nat.mul") []) (e/app idf fstp) (e/app idf sndp))) :default) :default)
        e0 (e/const' (nm "Nat.zero") [])
        join (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xs ys)
        term (e/app* (e/const' (nm "List.foldl") [z z]) Nat PXY op e0 join)
        lctx {72001 {:name "xs" :type (listOf Nat)} 72002 {:name "ys" :type (listOf Nat)}}]
    {:term term :lctx lctx}))

(deftest frame-index-auto-selected
  (when (ready?)
    (testing "optimize-cost auto-selects the FRAME index for a separable two-sided weight over a join"
      (let [{:keys [term lctx]} (frame-join-term)
            res (opt/optimize-cost (a/env) term :lctx lctx :ndv {72002 5.0})]
        (is (:verified? res) "frame rewrite kernel-certified")
        (is (some #{:frame-index} (:rewrites res)) "frame-index adopted")
        (is (= :in-memory-hash (get-in res [:physical :strategy])) "physical strategy = in-memory hash")
        (is (= 5.0 (double (get-in res [:physical :index-est]))) "held-index estimate = ndv (distinct keys)")))))

(deftest frame-index-executes-correctly
  (when (ready?)
    (testing "the auto-selected frame plan RUNS and equals the naive Σ f(x)·g(y) over the join"
      (let [{:keys [term lctx]} (frame-join-term)
            res (opt/optimize-cost (a/env) term :lctx lctx :ndv {72002 5.0})
            mk-fn (fn [t] (let [t1 (e/abstract1 t 72002)
                                ly (e/lam "ys" (listOf (natT)) t1 :default)
                                t2 (e/abstract1 ly 72001)
                                lx (e/lam "xs" (listOf (natT)) t2 :default)]
                            (eval (a/ansatz->clj (a/env) lx []))))
            frame-fn (mk-fn (:term res))
            naive-fn (mk-fn term)
            ;; 1→{1,1}: 1·1+1·1=2 ; 2→{2}: 2·2=4 ; 3→{3,3}: 3·3+3·3=18 ⇒ Σ x·y = 24
            XS [1 2 3] YS [1 1 2 3 3]]
        (is (:verified? res) "frame plan certified")
        (is (= 24 (long ((naive-fn XS) YS))) "naive Σ f(x)·g(y) over join")
        (is (= 24 (long ((frame-fn XS) YS))) "frame-indexed plan equals naive")))))

(deftest frame-index-declines-non-product
  (when (ready?)
    (testing "a bare separable SUM (no f·g product) is NOT a frame ⇒ try-frame-index declines (pre-agg owns it)"
      (let [Nat (natT) PXY (prodT Nat Nat)
            dec (e/const' (nm "instDecidableEqNat") [])
            idf (e/lam "n" Nat (e/bvar 0) :default)
            xs (e/fvar 72001) ys (e/fvar 72002)
            sndp (e/app* (e/const' (nm "Prod.snd") [z z]) Nat Nat (e/bvar 0))
            op (e/lam "acc" Nat (e/lam "p" PXY
                 (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1) (e/app idf sndp)) :default) :default)
            e0 (e/const' (nm "Nat.zero") [])
            join (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xs ys)
            term (e/app* (e/const' (nm "List.foldl") [z z]) Nat PXY op e0 join)
            lctx {72001 {:name "xs" :type (listOf Nat)} 72002 {:name "ys" :type (listOf Nat)}}
            res (opt/try-frame-index (a/env) term :lctx lctx :ndv {72002 5.0})]
        (is (nil? res) "frame correctly declines a bare (non-product) separable sum")))))

;; conditionally-weighted join: Σ (if (1≤x ∧ 1≤y) then x·y else 0), kf=lf=id, P=Q=(λn. 1≤n), f=g=id.
(defn- cond-frame-join-term []
  (let [Nat (natT) PXY (prodT Nat Nat)
        dec (e/const' (nm "instDecidableEqNat") [])
        idf (e/lam "n" Nat (e/bvar 0) :default)
        ble1 (e/lam "n" Nat (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 1) (e/bvar 0)) :default)
        xs (e/fvar 73001) ys (e/fvar 73002)
        fstp (e/app* (e/const' (nm "Prod.fst") [z z]) Nat Nat (e/bvar 0))
        sndp (e/app* (e/const' (nm "Prod.snd") [z z]) Nat Nat (e/bvar 0))
        guard (e/app* (e/const' (nm "Bool.and") []) (e/app ble1 fstp) (e/app ble1 sndp))
        wt (e/app* (e/const' (nm "Nat.mul") []) (e/app idf fstp) (e/app idf sndp))
        op (e/lam "acc" Nat (e/lam "p" PXY
             (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1)
                     (e/app* (e/const' (nm "cond") [(lvl/succ z)]) Nat guard wt (e/const' (nm "Nat.zero") []))) :default) :default)
        e0 (e/const' (nm "Nat.zero") [])
        join (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xs ys)
        term (e/app* (e/const' (nm "List.foldl") [z z]) Nat PXY op e0 join)
        lctx {73001 {:name "xs" :type (listOf Nat)} 73002 {:name "ys" :type (listOf Nat)}}]
    {:term term :lctx lctx}))

(deftest cond-frame-index-auto-selected
  (when (ready?)
    (testing "optimize-cost auto-selects the CONDITIONAL frame for a separable-guarded weighted join"
      (let [{:keys [term lctx]} (cond-frame-join-term)
            res (opt/optimize-cost (a/env) term :lctx lctx :ndv {73002 5.0})]
        (is (:verified? res) "conditional frame rewrite kernel-certified (split ∘ frame)")
        (is (some #{:frame-index-cond} (:rewrites res)) "frame-index-cond adopted")
        (is (= :in-memory-hash (get-in res [:physical :strategy])))))))

(deftest cond-frame-index-executes-correctly
  (when (ready?)
    (testing "the conditional frame plan RUNS and equals the naive guarded Σ over the join"
      (let [{:keys [term lctx]} (cond-frame-join-term)
            res (opt/optimize-cost (a/env) term :lctx lctx :ndv {73002 5.0})
            mk-fn (fn [t] (let [t1 (e/abstract1 t 73002)
                                ly (e/lam "ys" (listOf (natT)) t1 :default)
                                t2 (e/abstract1 ly 73001)
                                lx (e/lam "xs" (listOf (natT)) t2 :default)]
                            (eval (a/ansatz->clj (a/env) lx []))))
            cf (mk-fn (:term res)) nf (mk-fn term)
            ;; x=0→{0}: guard false→0 ; x=1→{1,1}: 1·1+1·1=2 ; x=2→{2,2}: 2·2+2·2=8 ⇒ 10
            XS [0 1 2] YS [0 1 1 2 2]]
        (is (:verified? res) "conditional frame certified")
        (is (= 10 (long ((nf XS) YS))) "naive guarded Σ over join")
        (is (= 10 (long ((cf XS) YS))) "conditional frame plan equals naive")))))
