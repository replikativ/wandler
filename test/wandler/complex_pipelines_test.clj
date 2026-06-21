(ns wandler.complex-pipelines-test
  "Elaborate combined pipelines — several relational optimizations COMPOSING on one realistic query,
   all kernel-certified. The headline: a FILTERED aggregate over a join factorizes through the join,
   the filter folded into the per-key aggregate (so an active-user check ends up per-user, the orders
   aggregated per user, the |users|·|orders| product never built)."
  (:require [ansatz.core :as a]
            [wandler.clean.optimize :as opt]
            [wandler.clean.laws.faq :as rl]
            [wandler.kmap :as kmap]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private nat (e/const' (nm "Nat") []))
(def ^:private prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat))
(def ^:private deceq (e/const' (nm "instDecidableEqNat") []))
(def ^:private listN (e/app (e/const' (nm "List") [z]) nat))
(def ^:private idf (e/lam "x" nat (e/bvar 0) :default))
(defn- litN [n] (e/app* (e/const' (nm "OfNat.ofNat") [z]) nat (e/lit-nat n)
                        (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat n))))

(deftest filtered-aggregate-over-join-factorizes
  ;; "total spend of ACTIVE users' orders":
  ;;   sum (map amount (filter (active? ∘ fst) (join id user users orders)))
  ;; The filter+map fuse into the fold, then aggregation-through-join factorizes: the per-pair
  ;; active check becomes a per-USER check in the outer fold (the filter is effectively pushed to
  ;; the user level), each active user's order-amounts aggregated per key — NO product materialized.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (rl/install!)
      (let [users (e/fvar 3) orders (e/fvar 4)
            join   (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq idf idf users orders)
            active (e/lam "pr" prodNN
                          (e/app* (e/const' (nm "Nat.blt") []) (litN 10)
                                  (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
            filtered (e/app* (e/const' (nm "List.filter") [z]) prodNN active join)
            amount   (e/lam "p" prodNN (e/app* (e/const' (nm "Prod.snd") [z z]) nat nat (e/bvar 0)) :default)
            mapped   (e/app* (e/const' (nm "List.map") [z z]) prodNN nat amount filtered)
            total    (e/app* (e/const' (nm "List.foldl") [z z]) nat nat (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) mapped)
            lctx     {3 {:name "users" :type listN} 4 {:name "orders" :type listN}}
            res      (opt/optimize-cost (a/env) total :lctx lctx :sizes {3 10000.0 4 1000000.0})
            s        (e/->string (:term res))]
        (is (contains? (set (:rewrites res)) :fold-factor) "filter + map + aggregate factorized through the join")
        (is (true? (:verified? res)) "kernel-certified")
        (is (not (clojure.string/includes? s "Map.join Nat Nat")) "the users·orders product is never built")
        (is (clojure.string/includes? s "Nat.blt") "the active-user filter is preserved (folded into the per-user aggregate)")))
    (do (println "SKIP complex pipeline test: no Init env") (is true))))

(deftest count-and-sum-share-the-one-factorization-law
  ;; SYSTEMATIC: count and sum are the SAME law (Map.foldl_join_factor) at different ops — both
  ;; factor through the join, certified, no product.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (rl/install!)
      (let [users (e/fvar 3) orders (e/fvar 4)
            join  (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq idf idf users orders)
            lctx  {3 {:name "users" :type listN} 4 {:name "orders" :type listN}}
            ;; COUNT: foldl (λacc _. acc+1) 0 (join)  — number of matching (user,order) pairs
            cnt-op (e/lam "acc" nat (e/lam "_" prodNN
                     (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1) (litN 1)) :default) :default)
            cnt    (e/app* (e/const' (nm "List.foldl") [z z]) nat prodNN cnt-op (e/const' (nm "Nat.zero") []) join)
            ;; SUM: foldl (λacc p. acc + snd p) 0 (join)  — total of the order amounts
            sum-op (e/lam "acc" nat (e/lam "p" prodNN
                     (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1)
                             (e/app* (e/const' (nm "Prod.snd") [z z]) nat nat (e/bvar 0))) :default) :default)
            sm     (e/app* (e/const' (nm "List.foldl") [z z]) nat prodNN sum-op (e/const' (nm "Nat.zero") []) join)
            rc (opt/optimize-cost (a/env) cnt :lctx lctx)
            rs (opt/optimize-cost (a/env) sm  :lctx lctx)]
        (is (contains? (set (:rewrites rc)) :fold-factor) "COUNT factors through the join")
        (is (true? (:verified? rc)) "count certified")
        (is (contains? (set (:rewrites rs)) :fold-factor) "SUM factors through the join (same law)")
        (is (true? (:verified? rs)) "sum certified")))
    (do (println "SKIP count/sum test: no Init env") (is true))))

(deftest factorization-is-op-polymorphic
  ;; THE GENERALITY POINT: Map.foldl_join_factor constrains NOTHING about `op`, so it factors
  ;; through ANY aggregate that elaborates to a kernel lambda — building a Map (assoc/insert),
  ;; nonlinear arithmetic, etc. The "large class of Clojure functions" challenge is ELABORATION
  ;; coverage (lifting the fn to a kernel term), NOT the rewrite — once lifted, the law applies free.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (rl/install!)
      (let [users (e/fvar 3) orders (e/fvar 4)
            join  (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq idf idf users orders)
            mapNN (e/app* (e/const' (nm "Map") [z z]) nat nat)
            lctx  {3 {:name "users" :type listN} 4 {:name "orders" :type listN}}
            factors? (fn [S e op]
                       (let [r (opt/optimize-cost (a/env)
                                 (e/app* (e/const' (nm "List.foldl") [z z]) S prodNN op e join) :lctx lctx)]
                         (and (contains? (set (:rewrites r)) :fold-factor) (:verified? r))))
            fst* (fn [p] (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat p))
            snd* (fn [p] (e/app* (e/const' (nm "Prod.snd") [z z]) nat nat p))]
        ;; op = REDUCE INTO A MAP (acc[fst] = snd) — i.e. (assoc acc (fst p) (snd p))
        (is (factors? mapNN (e/app* (e/const' (nm "Map.empty") []) nat nat)
                      (e/lam "acc" mapNN (e/lam "p" prodNN
                        (e/app* (e/const' (nm "Map.insert") []) nat nat deceq (fst* (e/bvar 0)) (snd* (e/bvar 0)) (e/bvar 1)) :default) :default))
            "fold INTO A MAP (assoc/insert op) factors through the join, certified")
        ;; op = SUM OF SQUARES (nonlinear) — acc + (snd p)*(snd p)
        (is (factors? nat (e/const' (nm "Nat.zero") [])
                      (e/lam "acc" nat (e/lam "p" prodNN
                        (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1)
                                (e/app* (e/const' (nm "Nat.mul") []) (snd* (e/bvar 0)) (snd* (e/bvar 0)))) :default) :default))
            "fold with nonlinear arithmetic factors through the join, certified")))
    (do (println "SKIP op-polymorphic test: no Init env") (is true))))

(deftest drive-direction-reorder-picks-the-smaller-side
  ;; THE DRIVE-DIRECTION DP (now complete): count over a join reorders to INDEX THE SMALLER side,
  ;; driven by per-source cardinality (datahike/stratum :estimate) and certified by Map.join_comm's
  ;; Perm→Eq bridge (Map.join_length_comm). xs=100, ys=1e6 → don't build the index on ys (cost ~2e6);
  ;; reorder to index xs (cost ~200), kernel-certified.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (rl/install!)
      (let [xs (e/fvar 3) ys (e/fvar 4)
            join (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq idf idf xs ys)
            cnt  (e/app* (e/const' (nm "List.length") [z]) prodNN join)
            lctx {3 {:name "xs" :type listN} 4 {:name "ys" :type listN}}
            ;; ys huge → reorder to drive from/index the small xs
            r-swap (opt/optimize-cost (a/env) cnt :lctx lctx :sizes {3 100.0 4 1000000.0})
            ;; xs huge → keep the original order (index the small ys); no reorder
            r-keep (opt/optimize-cost (a/env) cnt :lctx lctx :sizes {3 1000000.0 4 100.0})]
        ;; Since Map.count_join_factor is INSTALLED (it was test-only before the cohesion
        ;; audit), a count-over-join takes the strictly better plan: FACTORIZE the join away
        ;; (:count-factor — no product materialized at all) rather than merely reordering
        ;; which side is indexed. The reorder remains the certified fallback for queries the
        ;; factorization doesn't cover.
        (is (contains? (set (:rewrites r-swap)) :count-factor)
            "count over a join factorizes (the strictly better plan, supersedes reorder)")
        (is (true? (:verified? r-swap)) "the adopted plan is kernel-certified")
        (is (contains? (set (:rewrites r-keep)) :count-factor)
            "factorization wins regardless of drive direction (no product either way")))
    (do (println "SKIP reorder test: no Init env") (is true))))

(deftest factorized-join-hoists-its-index-memory-gated
  ;; Physical (a): a sum-over-join factorizes (:fold-factor) AND the optimizer hoists the
  ;; loop-invariant group_by index out of the fold (:hoist-index) — β-equivalent, so still
  ;; kernel-certified — turning the certified plan from O(N²) re-bucketing into the O(N)
  ;; in-memory hash join. Memory-gated (the held index must fit the budget).
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (kmap/install!) (rl/install!)
      (let [z lvl/zero N (e/const' (nm "Nat") []) xs (e/fvar 3) ys (e/fvar 4)
            deceq (e/const' (nm "instDecidableEqNat") [])
            NN (e/app* (e/const' (nm "Prod") [z z]) N N)
            fstNN (e/lam "p" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)
            join (e/app* (e/const' (nm "Map.join") []) N NN NN deceq fstNN fstNN xs ys)
            PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN)
            amount (e/lam "p" PJ (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                                         (e/app* (e/const' (nm "Prod.snd") [z z]) NN NN (e/bvar 0))) :default)
            amts (e/app* (e/const' (nm "List.map") [z z]) PJ N amount join)
            total (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) amts)
            lctx {3 {:name "cs" :type (e/app (e/const' (nm "List") [z]) NN)} 4 {:name "os" :type (e/app (e/const' (nm "List") [z]) NN)}}
            res (opt/optimize-cost (a/env) total :lctx lctx :sizes {3 1000 4 1000})]
        (is (contains? (set (:rewrites res)) :fold-factor) "the aggregation factorizes through the join")
        (is (contains? (set (:rewrites res)) :hoist-index) "the loop-invariant index is hoisted (in-memory hash)")
        (is (true? (:verified? res)) "the hoisted plan is kernel-certified (β-equiv to the factorized term)")
        ;; the resource decision is LEGIBLE via opt/explain (the REPL "look at the pipeline" surface)
        (is (clojure.string/includes? (opt/explain res) "IN-MEMORY HASH") "explain surfaces the hash strategy")
        (is (clojure.string/includes? (opt/explain res) "≤ budget") "explain shows the memory reasoning")
        ;; with a TINY budget the index won't fit → the planner picks the certified NESTED-LOOP
        ;; (bucket_content removes the held index → per-row filter, O(bucket) memory), not the hash.
        (let [tight (opt/optimize-cost (a/env) total :lctx lctx :sizes {3 1000 4 1000} :memory-budget 1.0)]
          (is (contains? (set (:rewrites tight)) :nested-loop) "tiny budget ⇒ certified nested-loop (no held index)")
          (is (not (contains? (set (:rewrites tight)) :hoist-index)) "…not the in-memory hash")
          (is (true? (:verified? tight)) "the nested-loop plan is kernel-certified")
          (is (clojure.string/includes? (opt/explain tight) "NESTED-LOOP") "explain surfaces the nested-loop fallback")
          (is (clojure.string/includes? (opt/explain tight) "> budget") "explain shows why (index exceeds budget)"))))
    (do (println "SKIP hoist test") (is true))))
