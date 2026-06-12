(ns wandler.pre-agg-test
  "Pre-aggregated (FAQ) join index for SEPARABLE SUM aggregates: the O(distinct-keys) in-memory
   strategy. `foldl (λacc p. acc + g (snd p)) e (Map.join xs ys)` rewrites — via the kernel-proven
   `Map.foldl_join_sum_factor` — to `foldl (λacc x. acc + getD (lookup (kf x) PREIDX) 0) e xs`, where
   each join bucket is PRE-SUMMED once so the held index is O(distinct keys), not O(|ys|). The law is
   assembled (proofs.clj §6) from Map.foldl_join_factor ∘ List.foldl_congr with a per-key identity from
   List.foldl_add_init (init-extraction) + List.lookup_map_kv (the crux) + Option.getD_map, using
   Map.lookup ≡ List.lookup ∘ Map.entries. The `:ndv` oracle (DuckDB-style) makes the small held-index
   estimate sound. Tests: the laws verify, the optimizer auto-selects it, and the plan RUNS = naive.
   See docs/SPILL_AND_FAQ_PLAN.md and [[verified-aggregation]]."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
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
    (reset! a/ansatz-env kenv)
    (km/install!)
    (rl/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; the canonical separable-SUM-over-join term + lctx (kf = lf = identity, g = identity)
(defn- sum-join-term []
  (let [Nat (natT)
        PXY (prodT Nat Nat)
        dec (e/const' (nm "instDecidableEqNat") [])
        idf (e/lam "n" Nat (e/bvar 0) :default)
        xs (e/fvar 71001) ys (e/fvar 71002)
        sndp (e/app* (e/const' (nm "Prod.snd") [z z]) Nat Nat (e/bvar 0))
        op (e/lam "acc" Nat (e/lam "p" PXY
             (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1) (e/app idf sndp)) :default) :default)
        e0 (e/const' (nm "Nat.zero") [])
        join (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xs ys)
        term (e/app* (e/const' (nm "List.foldl") [z z]) Nat PXY op e0 join)
        lctx {71001 {:name "xs" :type (listOf Nat)} 71002 {:name "ys" :type (listOf Nat)}}]
    {:term term :lctx lctx}))

(deftest pre-agg-laws-present-and-verified
  (when (ready?)
    (testing "the pre-aggregated-index foundation laws are admitted (each kernel check-constant'd)"
      (doseq [n ["List.foldl_add_init" "List.lookup_map_kv" "List.foldl_congr"
                 "Map.foldl_join_sum_factor"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present"))))))

(deftest pre-agg-auto-selected-by-optimizer
  (when (ready?)
    (testing "optimize-cost auto-selects the pre-aggregated index for a separable sum over a join"
      (let [{:keys [term lctx]} (sum-join-term)
            res (opt/optimize-cost (a/env) term :lctx lctx :ndv {71002 5.0})]
        (is (:verified? res) "pre-agg rewrite kernel-certified")
        (is (some #{:pre-agg-index} (:rewrites res)) "pre-agg-index adopted")
        (is (= :in-memory-hash (get-in res [:physical :strategy])) "physical strategy = in-memory hash")
        (is (= 5.0 (double (get-in res [:physical :index-est])))
            "held-index estimate = ndv (distinct keys), not |ys|")))))

(deftest pre-agg-executes-correctly
  (when (ready?)
    (testing "the auto-selected pre-agg plan RUNS (group_by/entries/lookup/getD) and equals the naive sum"
      (let [{:keys [term lctx]} (sum-join-term)
            res (opt/optimize-cost (a/env) term :lctx lctx :ndv {71002 5.0})
            mk-fn (fn [t] (let [t1 (e/abstract1 t 71002)
                                ly (e/lam "ys" (listOf (natT)) t1 :default)
                                t2 (e/abstract1 ly 71001)
                                lx (e/lam "xs" (listOf (natT)) t2 :default)]
                            (eval (a/ansatz->clj (a/env) lx []))))
            pre-fn   (mk-fn (:term res))
            naive-fn (mk-fn term)
            XS [1 2 3] YS [1 1 2 3 3]]   ; matches: 1→{1,1}, 2→{2}, 3→{3,3} ⇒ Σ snd = 1+1+2+3+3 = 10
        (is (:verified? res) "pre-agg certified")
        (is (= 10 (long ((naive-fn XS) YS))) "naive sum-over-join")
        (is (= 10 (long ((pre-fn XS) YS))) "pre-aggregated index sum equals naive")))))

(deftest pre-agg-detects-only-separable-sum
  (when (ready?)
    (testing "a COUNT op (acc-only, no g(snd p)) is NOT a separable sum ⇒ pre-agg does not fire"
      (let [Nat (natT) PXY (prodT Nat Nat)
            dec (e/const' (nm "instDecidableEqNat") [])
            idf (e/lam "n" Nat (e/bvar 0) :default)
            xs (e/fvar 71001) ys (e/fvar 71002)
            countOp (e/lam "acc" Nat (e/lam "p" PXY (e/app (e/const' (nm "Nat.succ") []) (e/bvar 1)) :default) :default)
            e0 (e/const' (nm "Nat.zero") [])
            join (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xs ys)
            term (e/app* (e/const' (nm "List.foldl") [z z]) Nat PXY countOp e0 join)
            lctx {71001 {:name "xs" :type (listOf Nat)} 71002 {:name "ys" :type (listOf Nat)}}
            res (opt/try-pre-agg-index (a/env) term :lctx lctx :ndv {71002 5.0})]
        (is (nil? res) "pre-agg correctly declines a non-separable (count) aggregate")))))
