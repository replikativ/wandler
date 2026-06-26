(ns wandler.sum-product-factor-test
  "Default-path (a/defn optimizer) nested SUM-OF-PRODUCTS factorization: a SEPARABLE nested sum over two
   independent collections `Σx Σy (h x · k y)` factors to `(Σx h x)·(Σy k y)` — O(N·M) → O(N+M) — via
   `wandler.optimize.faq/try-sum-product-factor` (simp with the loop-invariant pulls, certified). This is
   the no-join FAQ win on the ordinary `optimize-cost-driver` path the e-graph `nested_faq_test` exercises
   separately. The degenerate identity `Σx Σy (x·y)` eta-collapses the inner λ (faithful to lean4, whose
   simp likewise won't fire the general lemma there) — it stays fused, still correct, NOT factored."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.faq :as rl]
            [ansatz.prelude.list :as plist]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when-let [k @test-env/init-full-env]
    (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!) (plist/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest projection-nested-sum-factors-on-default-path
  (when (ready?)
    (testing "Σc Σo (succ p · succ q) factors to (Σ succ)·(Σ succ), certified, on the a/defn path"
      (eval '(ansatz.core/defn revprod_t [cs :- (List Nat) os :- (List Nat)] Nat
               (reduce + 0 (map (fn [p :- Nat]
                                  (reduce + 0 (map (fn [q :- Nat] (* (Nat.succ p) (Nat.succ q))) os))) cs))))
      (let [ex (wc/explain 'revprod_t)]
        (is (:verified? ex) "the factored plan is kernel-certified")
        (is (:changed? ex) "the optimizer rewrote the nested sum")
        (is (= [:sum-product-factor] (:rewrites ex)) "via the sum-product-factor recognizer"))
      ;; runtime agreement: (1+1 .. for succ) (succ 1 + succ 2)=(2+3)=5 ; (succ 3 + succ 4)=(4+5)=9 ; 45
      (is (= 45 ((resolve 'revprod_t) [1 2] [3 4]))))))

(deftest identity-nested-sum-factors-via-egraph-fallback
  (when (ready?)
    (testing "Σx Σy (x·y) factors via the e-graph fallback (eta-collapse blocks the simp pull; funext
              under-binder hoist on the Nat.zero-normalized term handles it), certified, runtime-correct"
      (eval '(ansatz.core/defn dotdot_t [xs :- (List Nat) ys :- (List Nat)] Nat
               (reduce + 0 (map (fn [x :- Nat]
                                  (reduce + 0 (map (fn [y :- Nat] (* x y)) ys))) xs))))
      (let [ex (wc/explain 'dotdot_t)]
        (is (:verified? ex) "the factored plan is kernel-certified")
        (is (:changed? ex) "the optimizer rewrote the nested sum")
        (is (= [:sum-product-factor] (:rewrites ex)) "via the sum-product-factor recognizer (e-graph fallback)"))
      ;; Nat is BigInteger-backed at runtime, so (= 54 54N); `==` is robust to the numeric type.
      (is (== 54 ((resolve 'dotdot_t) [1 2 3] [4 5]))))))

(deftest non-separable-nested-sum-not-factored
  (when (ready?)
    (testing "Σx Σy (x+y) (NOT a separable product) must NOT be labeled a factorization"
      (eval '(ansatz.core/defn addsum_t [xs :- (List Nat) ys :- (List Nat)] Nat
               (reduce + 0 (map (fn [x :- Nat]
                                  (reduce + 0 (map (fn [y :- Nat] (Nat.add x y)) ys))) xs))))
      (let [ex (wc/explain 'addsum_t)]
        (is (:verified? ex) "still verified (fusion only)")
        (is (= [] (:rewrites ex)) "no sum-product-factor (inseparable; de-nesting gate rejects fusion)"))
      (is (== 20 ((resolve 'addsum_t) [1 2] [3 4]))))))
