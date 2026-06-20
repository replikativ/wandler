(ns wandler.clean.optimize.physical-test
  "The clean physical strategies (wandler.clean.optimize.physical): cost-driven, kernel-CERTIFIED
   rewrites of relational join-aggregates. Pins that `try-agg-join-factor` recognizes a separable-weight
   sum over a real `Map.join`, applies the thin `Map_aggJoin_factor` law, and adopts the factored plan
   ONLY when it both lowers the cost model AND strict-certifies via `verified-rewrite?` (check-constant).
   This is the end-to-end wiring of the 5.5a aggregate laws into the optimizer (5.5b)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.prelude.algebra :as alg]
            [wandler.test-env :as test-env]
            [wandler.clean.laws.bucket :as bucket]
            [wandler.clean.optimize :as opt]
            [wandler.clean.optimize.physical :as phys]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (bucket/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))

(def ^:private z lvl/zero)
(defn- kc [s] (e/const' (nm/from-string s) []))

(defn- nat-agg-join-query
  "Build `wsum Nat m (map (λpr. mul m (id pr.fst) (id pr.snd)) (Map.join Nat Nat Nat dec id id xs ys))`
   over concrete Nat — a sum of the separable weight `id·id` over an equi-join. Returns [term lctx comm]."
  []
  (let [Nat   (kc "Nat")
        m     (alg/semiring-instance Nat alg/nat-row)
        addm  (e/app* (kc "WSemiring.toWAddMonoid") Nat m)
        comm  (e/app* (e/const' (nm/from-string "Std.Commutative.mk") [(lvl/succ z)])
                      Nat (kc "Nat.add") (kc "Nat.add_comm"))
        idf   (e/lam "x" Nat (e/bvar 0) :default)
        PNN   (e/app* (e/const' (nm/from-string "Prod") [z z]) Nat Nat)
        listNat (e/app (e/const' (nm/from-string "List") [z]) Nat)
        xs    (e/fvar 7001) ys (e/fvar 7002)
        lctx  {7001 {:name "xs" :type listNat} 7002 {:name "ys" :type listNat}}
        fstp  (e/app* (e/const' (nm/from-string "Prod.fst") [z z]) Nat Nat (e/bvar 0))
        sndp  (e/app* (e/const' (nm/from-string "Prod.snd") [z z]) Nat Nat (e/bvar 0))
        body  (e/app* (kc "WSemiring.mul") Nat m (e/app idf fstp) (e/app idf sndp))
        weight (e/lam "pr" PNN body :default)
        join  (e/app* (kc "Map.join") Nat Nat Nat (kc "instDecidableEqNat") idf idf xs ys)
        mapt  (e/app* (e/const' (nm/from-string "List.map") [z z]) PNN Nat weight join)
        term  (e/app* (kc "wsum") Nat addm mapt)]
    [term lctx comm]))

(deftest agg-join-factor-certified
  (when (ready?)
    (is (kenv/lookup (a/env) (nm/from-string "Map_aggJoin_factor")) "the factor law is installed")
    (let [[term lctx comm] (nat-agg-join-query)]
      (testing "the recognizer matches the wsum/map/Map.join separable-weight shape"
        (is (some? (phys/agg-join-factor-match term))))
      (testing "try-agg-join-factor adopts the factored plan — cost-lowered AND kernel-certified"
        (let [r (phys/try-agg-join-factor (a/env) term :lctx lctx :comm comm
                                          :sizes {7001 1000 7002 1000})]
          (is (some? r) "a rewrite is returned")
          (is (:verified? r) "it strict-certifies via verified-rewrite? (check-constant)")
          (is (:changed? r))
          (is (= :agg-join-factor (:rw r)))))
      (testing "without a join/separable-weight shape the recognizer declines (nil)"
        (is (nil? (phys/agg-join-factor-match (kc "Nat.zero"))))))))

(defn- nat-perpair-join-query
  "Build `wsum Nat m (map (λpr. f pr.fst pr.snd) (Map.join Nat Nat Nat dec id id xs ys))` with
   f = λx.λy.x — a per-pair (non-separable) sum over an equi-join, for the reorder strategy.
   Returns [term lctx comm]."
  []
  (let [Nat   (kc "Nat")
        m     (alg/semiring-instance Nat alg/nat-row)
        addm  (e/app* (kc "WSemiring.toWAddMonoid") Nat m)
        comm  (e/app* (e/const' (nm/from-string "Std.Commutative.mk") [(lvl/succ z)])
                      Nat (kc "Nat.add") (kc "Nat.add_comm"))
        idf   (e/lam "x" Nat (e/bvar 0) :default)
        ff    (e/lam "x" Nat (e/lam "y" Nat (e/bvar 1) :default) :default)
        PNN   (e/app* (e/const' (nm/from-string "Prod") [z z]) Nat Nat)
        listNat (e/app (e/const' (nm/from-string "List") [z]) Nat)
        xs (e/fvar 7001) ys (e/fvar 7002)
        lctx {7001 {:name "xs" :type listNat} 7002 {:name "ys" :type listNat}}
        fstp (e/app* (e/const' (nm/from-string "Prod.fst") [z z]) Nat Nat (e/bvar 0))
        sndp (e/app* (e/const' (nm/from-string "Prod.snd") [z z]) Nat Nat (e/bvar 0))
        weight (e/lam "pr" PNN (e/app* ff fstp sndp) :default)
        join  (e/app* (kc "Map.join") Nat Nat Nat (kc "instDecidableEqNat") idf idf xs ys)
        mapt  (e/app* (e/const' (nm/from-string "List.map") [z z]) PNN Nat weight join)
        term  (e/app* (kc "wsum") Nat addm mapt)]
    [term lctx comm]))

(deftest agg-join-reorder-certified
  (when (ready?)
    (is (kenv/lookup (a/env) (nm/from-string "Map_aggJoin_reorder")) "the reorder law is installed")
    (let [[term lctx comm] (nat-perpair-join-query)]
      (testing "the recognizer matches the per-pair wsum/map/Map.join shape"
        (is (some? (phys/agg-join-reorder-match term))))
      (testing "reorder fires + certifies ONLY when swapping lowers cost (drive the smaller side)"
        ;; xs small, ys large → driving ys after the swap is cheaper → reorder adopted.
        (let [r (phys/try-agg-join-reorder (a/env) term :lctx lctx :comm comm :sizes {7001 10 7002 1000})]
          (is (some? r))
          (is (:verified? r) "the swapped plan strict-certifies (Map_aggJoin_reorder)")
          (is (= :agg-join-reorder (:rw r))))
        ;; xs large, ys small → already driving the smaller side → no reorder.
        (is (nil? (phys/try-agg-join-reorder (a/env) term :lctx lctx :comm comm
                                             :sizes {7001 1000 7002 10}))
            "declines when the original drive direction is already optimal")))))

(deftest optimize-cost-driver
  (when (ready?)
    (testing "the cost-search driver applies the physical factor THEN fuses, composing proofs (Eq.trans)"
      (let [[term lctx comm] (nat-agg-join-query)
            r (opt/optimize-cost (a/env) term :lctx lctx :comm comm :sizes {7001 1000 7002 1000})]
        (is (:changed? r) "the driver rewrote the join-aggregate")
        (is (:verified? r) "the composed (factor ∘ fuse) proof kernel-certifies (check-constant)")
        (is (= :agg-join-factor (first (:rewrites r))) "the factorization is the first adopted step")
        (is (not (.equals ^Object term (:term r))) "the plan changed")))
    (testing "no join/separable shape → the driver falls back to plain fusion, still verified"
      ;; List.map id (List.map id xs) — a fusable streaming term, no join.
      (let [Nat (kc "Nat")
            idf (e/lam "x" Nat (e/bvar 0) :default)
            xs  (e/fvar 7003)
            lctx {7003 {:name "xs" :type (e/app (e/const' (nm/from-string "List") [z]) Nat)}}
            inner (e/app* (e/const' (nm/from-string "List.map") [z z]) Nat Nat idf xs)
            term  (e/app* (e/const' (nm/from-string "List.map") [z z]) Nat Nat idf inner)
            r (opt/optimize-cost (a/env) term :lctx lctx)]
        (is (or (nil? (:rewrites r)) (= [:fuse] (:rewrites r)))
            "no physical step — plain fusion (or no-op)")
        (when (:changed? r)
          (is (:verified? r) "fusion result certifies"))))))
