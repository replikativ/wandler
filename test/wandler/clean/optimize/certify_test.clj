(ns wandler.clean.optimize.certify-test
  "Phase 5.1: the clean certifier (wandler.clean.optimize.certify) — the soundness core. Differential
   against the OLD optimizer's certifier (the harness oracle): on a map∘map pipeline the clean rewriter
   must (a) FUSE it (map_map → one pass), (b) the proof must independently kernel-verify
   (verified-rewrite?), and (c) produce the SAME fused term as old wandler."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as nm]
            [wandler.test-env :as test-env]
            [wandler.clean.optimize.certify :as cclean]
            [wandler.clean.optimize.certify :as cold]))

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
          clean (cclean/optimize env term :lctx lctx)
          old   (cold/optimize  env term :lctx lctx)]
      (testing "(a) the clean rewriter FUSES map∘map (changed)"
        (is (:changed? clean) "map_map should fire"))
      (testing "(b) the clean proof independently kernel-verifies (the soundness gate)"
        (is (:verified? clean) "verified-rewrite? must accept the fusion proof"))
      (testing "(c) differential: clean fused term == old wandler's fused term"
        ;; normalize the Level object-identity hashes (#object[… 0x… "0"]) that `str` prints
        (let [norm #(clojure.string/replace (str %) #"0x[0-9a-fA-F]+" "")]
          (is (= (norm (:term clean)) (norm (:term old)))))
        (is (= (boolean (:verified? clean)) (boolean (:verified? old))))))))
