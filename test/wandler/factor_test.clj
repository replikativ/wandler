(ns wandler.factor-test
  "Semiring sum-product factorization: aggregate-THROUGH-join (FAQ / the asymptotic
   planner win). The COUNT instance — count a join WITHOUT materializing it:
       length (flatMap (λx. map (x,·) (g x)) xs)  =  sum (map (λx. length (g x)) xs)
   where `g` is the per-key bucket (Map.join's flatMap form is exactly this shape, with
   g = the group_by bucket). Proven for an ABSTRACT g (so it's the general law), on the
   flatMap form, via List.length_flatMap + List.length_map — Init-only, kernel-checked
   with the AUTHORITATIVE env/verifies? (not lenient inferType). See
   [[semiring-sum-product-planner]]."
  (:require [ansatz.core :as a]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]
            [clojure.test :refer [deftest is]]))

(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ lvl/zero))
(defn- nm [s] (name/from-string s))

(defn- count-join-factor-goal+proof
  "Build and simp-prove the count-of-join factorization. Returns [goal proof|nil]."
  []
  (let [natT (e/const' (nm "Nat") [])
        listN (e/app (e/const' (nm "List") [z]) natT)
        prodNN (e/app* (e/const' (nm "Prod") [z z]) natT natT)
        fg (e/fvar 100) fxs (e/fvar 101)              ; g : Nat → List Nat ;  xs : List Nat
        pairfn (e/lam "y" natT (e/app* (e/const' (nm "Prod.mk") [z z]) natT natT (e/bvar 1) (e/bvar 0)) :default)
        innermap (e/app* (e/const' (nm "List.map") [z z]) natT prodNN pairfn (e/app fg (e/bvar 0)))
        flatform (e/app* (e/const' (nm "List.flatMap") [z z]) natT prodNN
                         (e/lam "x" natT innermap :default) fxs)
        lhs (e/app* (e/const' (nm "List.length") [z]) prodNN flatform)
        zeroNat (e/app* (e/const' (nm "Zero.ofOfNat0") [z]) natT
                        (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 0)))
        lenfn (e/lam "x" natT (e/app* (e/const' (nm "List.length") [z]) natT (e/app fg (e/bvar 0))) :default)
        mapped (e/app* (e/const' (nm "List.map") [z z]) natT natT lenfn fxs)
        rhs (e/app* (e/const' (nm "List.sum") [z]) natT (e/const' (nm "instAddNat") []) zeroNat mapped)
        eqn (e/app* (e/const' (nm "Eq") [L1]) natT lhs rhs)
        goal (-> eqn
                 (#(e/forall' "xs" listN (e/abstract1 % 101) :default))
                 (#(e/forall' "g" (e/forall' "_" natT listN :default) (e/abstract1 % 100) :default)))
        ps (simp/simp-all (basic/intros (first (proof/start-proof (a/env) goal)) ["g" "xs"])
                          ['List.length_flatMap 'List.length_map])]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(deftest count-of-join-factorization
  ;; length(join xs ys) = sum over xs of (matching-bucket size) — the count-semiring
  ;; aggregation-through-join, kernel-checked. Counts a join in O(|xs| + buckets), never
  ;; materializing the O(|xs|·|ys|) product.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [[goal proof] (count-join-factor-goal+proof)]
        (is (some? proof) "count-of-join factorization simp-proves")
        (is (true? (env/verifies? (a/env) goal proof))
            "AUTHORITATIVE kernel check: length(flatMap …) = sum(map length …)")))
    (do (println "SKIP count-of-join-factorization: no Init env") (is true))))

(defn- projection-through-join-goal+proof
  "Build and simp-prove projection pushdown through a join: a weighted column read off a
   join equals a flatMap of per-bucket projections — NO (x,y) pairs are ever built.
   Returns [goal proof|nil]."
  []
  (let [natT (e/const' (nm "Nat") [])
        listN (e/app (e/const' (nm "List") [z]) natT)
        prodNN (e/app* (e/const' (nm "Prod") [z z]) natT natT)
        fg (e/fvar 100) fxs (e/fvar 101) fw (e/fvar 102)   ; g, xs, w : Nat→Nat
        pairfn (e/lam "y" natT (e/app* (e/const' (nm "Prod.mk") [z z]) natT natT (e/bvar 1) (e/bvar 0)) :default)
        innermap (e/app* (e/const' (nm "List.map") [z z]) natT prodNN pairfn (e/app fg (e/bvar 0)))
        flatform (e/app* (e/const' (nm "List.flatMap") [z z]) natT prodNN (e/lam "x" natT innermap :default) fxs)
        projfn (e/lam "p" prodNN (e/app fw (e/app* (e/const' (nm "Prod.snd") [z z]) natT natT (e/bvar 0))) :default)
        lhs (e/app* (e/const' (nm "List.map") [z z]) prodNN natT projfn flatform)
        rhsInner (e/app* (e/const' (nm "List.map") [z z]) natT natT fw (e/app fg (e/bvar 0)))
        rhs (e/app* (e/const' (nm "List.flatMap") [z z]) natT natT (e/lam "x" natT rhsInner :default) fxs)
        eqn (e/app* (e/const' (nm "Eq") [L1]) listN lhs rhs)
        goal (-> eqn (#(e/forall' "xs" listN (e/abstract1 % 101) :default))
                     (#(e/forall' "g" (e/forall' "_" natT listN :default) (e/abstract1 % 100) :default))
                     (#(e/forall' "w" (e/forall' "_" natT natT :default) (e/abstract1 % 102) :default)))
        ps (simp/simp-all (basic/intros (first (proof/start-proof (a/env) goal)) ["w" "g" "xs"])
                          ['List.map_flatMap 'List.map_map 'Function.comp 'Prod.snd])]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(deftest projection-through-join
  ;; map (w∘snd) (join xs ys) = flatMap (λx. map w (g x)) xs — projecting a weighted column
  ;; off a join needs NO (x,y) pair materialization. The structural half of weighted
  ;; aggregation-through-join; the SUM half additionally needs List.sum_flatMap (absent in
  ;; Init → a separate inductive lemma). See [[semiring-sum-product-planner]].
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [[goal proof] (projection-through-join-goal+proof)]
        (is (some? proof) "projection-through-join simp-proves")
        (is (true? (env/verifies? (a/env) goal proof))
            "AUTHORITATIVE kernel check: map(w∘snd)(join) = flatMap(map w ∘ bucket)")))
    (do (println "SKIP projection-through-join: no Init env") (is true))))
