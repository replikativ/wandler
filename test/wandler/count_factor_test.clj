(ns wandler.count-factor-test
  "Item C — aggregation-THROUGH-join factorization WIRED into the optimizer. The count
   instance: length (Map.join … kf lf xs ys) = sum (map (λx. length (bucket (kf x) ys)) xs)
   — count a join WITHOUT materializing the |xs|·|ys| product. The law is proven on
   Map.join's flatMap form (unfold one delta step, then List.length_flatMap + length_map,
   the factor_test method), admitted as `Map.count_join_factor`, and applied by the
   dedicated cost path `opt/try-count-factor` (same shape as try-join-reorder): adopted iff
   pipeline-cost strictly drops AND the proof certifies. See [[semiring-sum-product-planner]]."
  (:require [ansatz.core :as a]
            [wandler.clean.optimize :as opt]
            [wandler.kmap :as kmap]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))

;; ── term builders (abstract K X Y dec kf lf xs ys = fvars 1..8) ──────────────
(defn- jvars []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4)
        kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys (e/fvar 8)]
    {:K K :X X :Y Y :dec dec :kf kf :lf lf :xs xs :ys ys
     :PXY (e/app* (e/const' (nm "Prod") [z z]) X Y)
     :listX (e/app (e/const' (nm "List") [z]) X)
     :listY (e/app (e/const' (nm "List") [z]) Y)
     :deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
     :xToK (e/forall' "_" X K :default) :yToK (e/forall' "_" Y K :default)}))

(defn- jlctx [{:keys [deceqK xToK yToK listX listY]}]
  {1 {:name "K" :type type0} 2 {:name "X" :type type0} 3 {:name "Y" :type type0}
   4 {:name "dec" :type deceqK} 5 {:name "kf" :type xToK} 6 {:name "lf" :type yToK}
   7 {:name "xs" :type listX} 8 {:name "ys" :type listY}})

(defn- length-join [{:keys [K X Y dec kf lf xs ys PXY]}]
  (e/app* (e/const' (nm "List.length") [z]) PXY
          (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys)))

(defn- count-factor-goal+proof
  "Prove Map.count_join_factor on the Map.join form. Returns [goal proof|nil]."
  [v]
  (let [{:keys [K X Y dec kf lf xs ys PXY listX listY deceqK xToK yToK]} v
        NatT (e/const' (nm "Nat") [])
        lhs (length-join v)
        bucket (fn [k'] (e/app* (e/const' (nm "Option.getD") [z]) listY
                                (e/app* (e/const' (nm "Map.lookup") []) K listY dec k'
                                        (e/app* (e/const' (nm "Map.group_by") []) K Y dec lf ys))
                                (e/app (e/const' (nm "List.nil") [z]) Y)))
        lenFn (e/lam "x" X (e/app* (e/const' (nm "List.length") [z]) Y (bucket (e/app kf (e/bvar 0)))) :default)
        mapped (e/app* (e/const' (nm "List.map") [z z]) X NatT lenFn xs)
        zeroNat (e/app* (e/const' (nm "Zero.ofOfNat0") [z]) NatT
                        (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 0)))
        rhs (e/app* (e/const' (nm "List.sum") [z]) NatT (e/const' (nm "instAddNat") []) zeroNat mapped)
        eqn (e/app* (e/const' (nm "Eq") [L1]) NatT lhs rhs)
        wrap (fn [t lam?]
               (let [b (if lam? e/lam e/forall')]
                 (-> t (#(b "ys" listY (e/abstract1 % 8) :default)) (#(b "xs" listX (e/abstract1 % 7) :default))
                       (#(b "lf" yToK (e/abstract1 % 6) :default)) (#(b "kf" xToK (e/abstract1 % 5) :default))
                       (#(b "dec" deceqK (e/abstract1 % 4) :default)) (#(b "Y" type0 (e/abstract1 % 3) :default))
                       (#(b "X" type0 (e/abstract1 % 2) :default)) (#(b "K" type0 (e/abstract1 % 1) :default)))))
        goal (wrap eqn false)
        ps0 (basic/intros (first (proof/start-proof (a/env) goal)) ["K" "X" "Y" "dec" "kf" "lf" "xs" "ys"])
        fvid (fn [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
        hv (fn [n] (e/fvar (fvid ps0 n)))
        ;; STEP 1: unfold Map.join → flatMap body (direct rewrite, no dsimp flatten-expansion)
        ps1 (basic/rewrite ps0 (e/app* (e/const' (nm "Map.join.eq_unfold") [])
                                       (hv "K") (hv "X") (hv "Y") (hv "dec")
                                       (hv "kf") (hv "lf") (hv "xs") (hv "ys")))
        ;; STEP 2: length_flatMap fires on the flatMap form → clean lambda
        ps (simp/simp-all ps1 ['List.length_flatMap 'List.length_map])]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn- setup! []
  (reset! a/ansatz-env @test-env/init-full-env)
  (kmap/install!)
  ;; admit the one-delta-step Map.join unfold equation (Eq.refl proof)
  (reset! a/ansatz-env (kenv/check-constant (a/env) (#'opt/unfold-eqn-ci (a/env) "Map.join")))
  (let [[goal proof] (count-factor-goal+proof (jvars))]
    (when proof
      (reset! a/ansatz-env (kenv/check-constant (a/env) (kenv/mk-thm (nm "Map.count_join_factor") [] goal proof))))
    proof))

(deftest count-factor-law-verifies
  (if @test-env/init-full-env
    (binding [a/*verbose* false]
      (let [proof (setup!)]
        (is (some? proof) "Map.count_join_factor simp-proves on the Map.join flatMap form")
        ;; AUTHORITATIVE: the admitted law kernel-checks (it's now in the env after setup!)
        (is (some? (kenv/lookup (a/env) (nm "Map.count_join_factor"))) "law admitted")))
    (do (println "SKIP count-factor-law-verifies: no Init env") (is true))))

(deftest count-factor-auto-applied-by-optimizer
  (if @test-env/init-full-env
    (binding [a/*verbose* false]
      (setup!)
      (let [v (jvars)
            term (length-join v)
            lctx (jlctx v)
            res (opt/optimize-cost (a/env) term :lctx lctx)]
        ;; the optimizer factorizes the count-join, certified, and labels the rewrite
        (is (true? (:changed? res)) "optimizer rewrote length(join)")
        (is (true? (:verified? res)) "the factorization proof kernel-certifies")
        (is (some #{:count-factor} (:rewrites res)) "via the count-factor path")
        ;; pipeline-cost strictly dropped (the |xs|·|ys| product is gone)
        (is (< (#'opt/pipeline-cost (:term res) {:lctx lctx})
               (#'opt/pipeline-cost term {:lctx lctx}))
            "factored form is cheaper (no product materialization)")))
    (do (println "SKIP count-factor-auto-applied-by-optimizer: no Init env") (is true))))
