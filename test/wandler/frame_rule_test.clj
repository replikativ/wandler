(ns wandler.frame-rule-test
  "The FAQ FRAME RULE for Map.join (Phase 1). A SEPARABLE two-sided weight over a keyed join

     foldl (λacc p. acc + f(fst p)·g(snd p)) e (Map.join kf lf xs ys)
       = foldl (λacc x. acc + f(x)·getD (lookup (kf x) PREIDX) 0) e xs

   factorizes through the SAME g-only O(distinct-keys) pre-aggregated index as
   Map.foldl_join_sum_factor — which is exactly its f≡1 instance. This is the SPN / FAQ
   `product node` expressed over Map.join: Σ_{x⋈y} f(x)·g(y) = Σ_x f(x)·(Σ_{y∈bucket(x)} g(y)).
   The x-side weight f(x) is separated from the pre-summed y-side, NEVER materializing the
   |xs|·|ys| pairs. The supporting element-polymorphic foldl-form pull law
   List.foldl_const_mul_pull is checked too. Both are authoritatively kernel-verified
   (kenv/verifies? = check-constant, not the lenient inferType). Gated on Init.
   See [[faq-variable-elimination]], [[programming-model-4-structures]]."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.laws.proofs :as rp]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]))

(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest foldl-const-mul-pull-verifies
  (when (ready?)
    (testing "List.foldl_const_mul_pull (polymorphic foldl-form const-factor pull) kernel-verifies"
      (let [[g p] (rp/prove-foldl-const-mul-pull)]
        (is (some? p) "proof extracted")
        (is (true? (kenv/verifies? (a/env) g p)) "passes check-constant")))))

(deftest foldl-join-frame-verifies
  (when (ready?)
    (testing "Map.foldl_join_frame (the FAQ frame rule) kernel-verifies"
      (let [[g p] (rp/prove-foldl-join-frame)]
        (is (some? p) "proof extracted")
        (is (true? (kenv/verifies? (a/env) g p)) "passes check-constant")
        (let [s (e/->string g)]
          (testing "the goal is the separable two-sided weight factorized through the pre-agg index"
            (is (some? (re-find #"Map.join" s)) "LHS aggregates over a Map.join")
            (is (some? (re-find #"Nat.mul" s)) "the weight is a product f·g")
            (is (some? (re-find #"Prod.fst" s)) "f is applied to the LEFT projection")
            (is (some? (re-find #"Prod.snd" s)) "g is applied to the RIGHT projection")
            (is (some? (re-find #"Option.getD" s)) "RHS probes the pre-aggregated index")
            (is (some? (re-find #"List.lookup" s)) "RHS reads via a key lookup")))))))

(deftest both-laws-installed
  (when (ready?)
    (testing "install! lands both new laws (each check-constant'd as it builds)"
      (is (boolean (kenv/lookup (a/env) (nm "List.foldl_const_mul_pull"))))
      (is (boolean (kenv/lookup (a/env) (nm "Map.foldl_join_frame"))))
      (testing "the frame GENERALIZES the f≡1 sum-factor (both present, same pre-agg foundation)"
        (is (boolean (kenv/lookup (a/env) (nm "Map.foldl_join_sum_factor"))))))))

(deftest cond-and-mul-split-verifies
  (when (ready?)
    (testing "Nat.cond_and_mul_split (conditional separation — the dependent-types win) kernel-verifies"
      (let [[g p] (rp/prove-cond-and-mul-split)]
        (is (some? p) "proof extracted")
        (is (true? (kenv/verifies? (a/env) g p)) "passes check-constant")
        (let [s (e/->string g)]
          (testing "a separable conjunctive guard P∧Q factors a weighted product"
            (is (some? (re-find #"Bool.and" s)) "the guard is a conjunction (a && b)")
            (is (some? (re-find #"cond" s)) "indicator/guard expressed via cond")
            (is (some? (re-find #"Nat.mul" s)) "factors a product u·v"))))
      (is (boolean (kenv/lookup (a/env) (nm "Nat.cond_and_mul_split"))) "installed by build-all"))))

(deftest bucket-key-subst-verifies
  (when (ready?)
    (testing "Map.bucket_key_subst (FD scope quotient foundation) kernel-verifies"
      (let [[g p] (rp/prove-bucket-key-subst)]
        (is (some? p) "proof extracted")
        (is (true? (kenv/verifies? (a/env) g p)) "passes check-constant")
        (let [s (e/->string g)]
          (testing "a key-function is constant on the bucket = keyed filter"
            (is (some? (re-find #"List.filter" s)) "the domain is the keyed filter (the bucket)")
            (is (some? (re-find #"List.map" s)) "substituting the key inside the mapped fn")
            (is (some? (re-find #"BEq.beq" s)) "the filter keys on equality k == lf y"))))
      (is (boolean (kenv/lookup (a/env) (nm "Map.bucket_key_subst"))) "installed by build-all"))))

(deftest bucket-factor-pull-verifies
  (when (ready?)
    (testing "Map.bucket_factor_pull (FD key-factor pull) kernel-verifies"
      (let [[g p] (rp/prove-bucket-factor-pull)]
        (is (some? p) "proof extracted")
        (is (true? (kenv/verifies? (a/env) g p)) "passes check-constant")
        (let [s (e/->string g)]
          (testing "a key-factor pulls out of the bucket sum: Σ w(lf y)·g y = w(k)·Σ g"
            (is (some? (re-find #"List.filter" s)) "over the bucket = keyed filter")
            (is (some? (re-find #"Nat.mul" s)) "the key-factor product")
            (is (some? (re-find #"List.foldl" s)) "summed via foldl"))))
      (is (boolean (kenv/lookup (a/env) (nm "Map.bucket_factor_pull"))) "installed by build-all"))))

(deftest lookup-reweight-verifies
  (when (ready?)
    (testing "List.lookup_reweight (float a key-factor into the index) kernel-verifies"
      (let [[g p] (rp/prove-lookup-reweight)]
        (is (some? p) "proof extracted")
        (is (true? (kenv/verifies? (a/env) g p)) "passes check-constant")
        (let [s (e/->string g)]
          (testing "w(k)·getD(lookup k idx) = getD(lookup k (reweight w idx))"
            (is (some? (re-find #"List.lookup" s)) "operates on a key lookup")
            (is (some? (re-find #"List.map" s)) "reweights the index by map")
            (is (some? (re-find #"Nat.mul" s)) "the key-factor product"))))
      (is (boolean (kenv/lookup (a/env) (nm "List.lookup_reweight"))) "installed by build-all"))))

(deftest keyfactor-float-verifies
  (when (ready?)
    (testing "Map.foldl_keyfactor_float (the optimizer float law) kernel-verifies"
      (let [[g p] (rp/prove-keyfactor-float)]
        (is (some? p) "proof extracted")
        (is (true? (kenv/verifies? (a/env) g p)) "passes check-constant")
        (let [s (e/->string g)]
          (testing "Σ_x w(kf x)·getD(lookup(kf x) idx) = Σ_x getD(lookup(kf x) reweight(idx))"
            (is (some? (re-find #"List.foldl" s)) "a fold over xs")
            (is (some? (re-find #"List.lookup" s)) "per-key index lookup")
            (is (some? (re-find #"List.map" s)) "the reweighted index"))))
      (is (boolean (kenv/lookup (a/env) (nm "Map.foldl_keyfactor_float"))) "installed by build-all"))))
