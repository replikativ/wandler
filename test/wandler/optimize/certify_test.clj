(ns wandler.optimize.certify-test
  "The certifier must fuse map∘map, carry an independently checkable proof,
   and reject forged candidates. The retired old/clean aliases named the same namespace
   and therefore did not provide an independent differential oracle."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as nm]
            [wandler.test-env :as test-env]
            [wandler.optimize.cost :as cost]
            [wandler.optimize.certify :as cert]))

(defn- setup [f]
  (when @test-env/init-full-env (reset! a/ansatz-env @test-env/init-full-env))
  (f))
(use-fixtures :once setup)

;; A naive two-stage pipeline term: List.map g (List.map f xs), with g,f : Nat→Nat and xs : List Nat
;; as free variables (an in-progress a/defn body), supplied via lctx.
(defn- map-map-term []
  (let [Nat   (e/const' (nm/from-string "Nat") [])
        NatN  (e/forall' "_" Nat Nat :default)
        ListN (e/app (e/const' (nm/from-string "List") [lvl/zero]) Nat)
        g (e/fvar 7001) f (e/fvar 7002) xs (e/fvar 7003)
        mapc (e/const' (nm/from-string "List.map") [lvl/zero lvl/zero])
        inner (e/app* mapc Nat Nat f xs)
        term  (e/app* mapc Nat Nat g inner)
        lctx  {7001 {:name "g" :type NatN} 7002 {:name "f" :type NatN} 7003 {:name "xs" :type ListN}}]
    [term lctx]))

(deftest clean-certifier-fuses-and-verifies
  (when @test-env/init-full-env
    (let [env (a/env)
          [term lctx] (map-map-term)
          clean (cert/optimize env term :lctx lctx)]
      (testing "(a) the clean rewriter FUSES map∘map (changed)"
        (is (:changed? clean) "map_map should fire"))
      (testing "(b) the clean proof independently kernel-verifies (the soundness gate)"
        (is (:verified? clean) "verified-rewrite? must accept the fusion proof"))
      (testing "the resulting term contains one map and its certificate checks separately"
        (is (= 1 (cost/soac-cost (:term clean))))
        (is (cert/verified-rewrite? env term clean :lctx lctx))))))

(deftest certifier-rejects-forged-candidates
  (when @test-env/init-full-env
    (let [env (a/env)
          [term lctx] (map-map-term)
          forged (e/lit-nat 0)
          unrelated-proof (e/const' (nm/from-string "True.intro") [])]
      (is (cert/verified-rewrite? env term {:term term :proof nil} :lctx lctx))
      (is (not (cert/verified-rewrite? env term {:term forged :proof nil} :lctx lctx)))
      (is (not (cert/verified-rewrite? env term {:term forged :proof unrelated-proof}
                                       :lctx lctx))))))
