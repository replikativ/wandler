(ns wandler.inference-test
  "Track 3 — INFERENCE on the verified relational substrate. The foundational identity: VARIABLE
   ELIMINATION (the core of exact inference in factor graphs / Bayesian networks) IS the
   aggregation-through-join factorization (Map.foldl_join_factor) we already proved, read at the
   sum-product semiring:
       factor              = a relation (table) over variables, carrying a weight
       factor product ⊗    = a JOIN on the shared variable, weights multiplied
       marginalize  ⊕      = a FOLD (Σ) over the result
       eliminate X         = Σ_X (∏ factors mentioning X)  =  sum over a join  →  FACTORIZES
   so the asymptotic win of VE (push the sum inside the product — don't materialize the full joint)
   is EXACTLY the factorization's win, and the kernel proof IS the variable-elimination certificate."
  (:require [ansatz.core :as a]
            [wandler.kmap :as kmap]
            [wandler.rel-laws :as rl]
            [wandler.optimize :as opt]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(defn- c' [s & ls] (e/const' (nm s) (vec ls)))

(deftest variable-elimination-is-aggregation-through-join
  ;; A factor graph with two factors φ1(B), φ2(B) sharing variable B (weights : Nat). The partition
  ;; function Z = Σ_B φ1(B)·φ2(B) "sums out B" — variable elimination. As a relational pipeline:
  ;;   Z = foldl (+) 0 (map (λ((b,w1),(b,w2)). w1·w2) (join_on_B φ1 φ2))
  ;; The aggregation-through-join factorization fires: aggregate each B's contribution per-bucket,
  ;; NEVER materializing the |φ1|·|φ2| join — the VE step, kernel-certified.
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (kmap/install!) (rl/install!)
      (let [z lvl/zero natT (c' "Nat") W natT B natT
            phi1 (e/fvar 3) phi2 (e/fvar 4) deceq (c' "instDecidableEqNat")
            BW (e/app* (c' "Prod" z z) B W)
            fstBW (e/lam "p" BW (e/app* (c' "Prod.fst" z z) B W (e/bvar 0)) :default)
            join (e/app* (c' "Map.join") B BW BW deceq fstBW fstBW phi1 phi2)
            PJ (e/app* (c' "Prod" z z) BW BW)
            ;; ⊗ : the factor product — multiply the two joined factors' weights
            wprod (e/lam "p" PJ (e/app* (c' "Nat.mul")
                                        (e/app* (c' "Prod.snd" z z) B W (e/app* (c' "Prod.fst" z z) BW BW (e/bvar 0)))
                                        (e/app* (c' "Prod.snd" z z) B W (e/app* (c' "Prod.snd" z z) BW BW (e/bvar 0)))) :default)
            weighted (e/app* (c' "List.map" z z) PJ W wprod join)
            ;; ⊕ : marginalize — Σ over the weighted join
            Z (e/app* (c' "List.foldl" z z) W W (c' "Nat.add") (c' "Nat.zero") weighted)
            lctx {3 {:name "phi1" :type (e/app (c' "List" z) BW)}
                  4 {:name "phi2" :type (e/app (c' "List" z) BW)}}
            res (opt/optimize-cost (a/env) Z :lctx lctx)]
        (is (contains? (set (:rewrites res)) :fold-factor)
            "eliminating B = the aggregation-through-join factorization (the VE step)")
        (is (true? (:verified? res)) "the variable-elimination rewrite is kernel-certified")
        (is (not (clojure.string/includes? (e/->string (:term res)) "Map.join Nat"))
            "the |φ1|·|φ2| joint is never materialized — the sum is pushed inside the product")))
    (do (println "SKIP variable-elimination test: no Init env") (is true))))
