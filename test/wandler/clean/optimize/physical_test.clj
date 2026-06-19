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
