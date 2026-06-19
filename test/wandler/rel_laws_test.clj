(ns wandler.rel-laws-test
  "The packaged relational-law installer (wandler.laws.relational): one `install!` admits the proven laws
   into the env, after which optimize-cost AUTO-ADOPTS them — the Layer-2 jump that makes
   relational optimizations (filter→join pushdown) available like the filterMap law, not just in
   bespoke per-test setups."
  (:require [wandler.core]
            [ansatz.core :as a]
            [wandler.laws.relational :as rl]
            [wandler.kmap :as kmap]
            [wandler.surface.collections :as coll]
            [wandler.surface.relational :as rel]
            [wandler.optimize :as opt]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.matchers :as matchers]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))

(deftest install-makes-filter-join-pushdown-auto-adopt
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      ;; one call admits the proven laws (idempotent)
      (rl/install!)
      (is (some? (kenv/lookup (a/env) (nm "Map.filter_join_pushdown"))) "pushdown law admitted")
      (is (some? (kenv/lookup (a/env) (nm "List.filter_flatMap_cond")))   "supporting lemma A admitted")
      (is (some? (kenv/lookup (a/env) (nm "List.filter_map_pair_eq_cond"))) "supporting lemma B admitted")
      ;; filter (p∘fst) (Map.join … xs ys)  — the cost optimizer auto-adopts the pushdown,
      ;; pre-filtering xs BEFORE the join, and the adopted rewrite is kernel-certified.
      (let [z lvl/zero
            nat (e/const' (nm "Nat") [])
            prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat)
            listN (e/app (e/const' (nm "List") [z]) nat)
            boolT (e/const' (nm "Bool") [])
            deceq (e/const' (nm "instDecidableEqNat") [])
            pp (e/fvar 62001) kf (e/fvar 62002) lf (e/fvar 62003) ys (e/fvar 62004) xs (e/fvar 62005)
            predPair (e/lam "pr" prodNN (e/app pp (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
            joinXs (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq kf lf xs ys)
            term (e/app* (e/const' (nm "List.filter") [z]) prodNN predPair joinXs)
            lctx {62001 {:name "p" :type (e/forall' "_" nat boolT :default)}
                  62002 {:name "kf" :type (e/forall' "_" nat nat :default)}
                  62003 {:name "lf" :type (e/forall' "_" nat nat :default)}
                  62004 {:name "ys" :type listN}
                  62005 {:name "xs" :type listN}}
            r (opt/optimize-cost (a/env) term :lctx lctx)]
        (is (contains? (set (:rewrites r)) "Map.filter_join_pushdown")
            "cost search auto-adopts the filter→join pushdown from the installed law")
        (is (true? (:verified? r)) "the adopted rewrite is kernel-certified")))
    (do (println "SKIP rel-laws install test: no Init env") (is true))))

(deftest install-makes-semijoin-foundation-and-surface-pipeline-work
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!) (kmap/install!) (rel/install!) (rl/install!)
      ;; the whole lookup/group_by foundation + the semijoin/anti-join laws are admitted
      (doseq [n ["List.lookup_filter_ne" "List.lookup_insert" "Map.gbStepId" "Map.lookup_insert"
                 "Map.isSome_lookup_insert" "Map.lookup_group_by_gen" "Map.lookup_group_by"
                 "List.elem_filter_eq_index_probe" "List.elem_not_filter_eq_index_probe"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " admitted")))
      ;; SURFACE semijoin pipeline: keep xs whose element is in ys → build-once index probe,
      ;; auto-adopted by the cost optimizer (predicate-aware pre-check), kernel-certified, runs.
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn rlt-semi [xs :- (List Nat), ys :- (List Nat)] (List Nat)
                 (filterv (fn [x] (member x ys)) xs))))
      (let [ex (wandler.core/explain "rlt-semi")]
        (is (true? (:changed? ex)) "semijoin pipeline was optimized")
        (is (true? (:verified? ex)) "kernel-certified")
        (is (= ["List.elem_filter_eq_index_probe"] (:rewrites ex)) "the semijoin law fired"))
      (is (= [2 4] (vec ((resolve 'rlt-semi) (list 1 2 3 4) (list 2 4 6))))
          "surface semijoin runs correctly (build-once index probe)"))
    (do (println "SKIP semijoin install test: no Init env") (is true))))

(deftest grace-hash-partition-lemma-installed
  ;; Physical (b) middle: the GRACE-HASH partition lemma — a join's build side distributes over
  ;; append (filter form), so it can be processed in budget-sized blocks. install! proves +
  ;; check-constants it; here we confirm it lands in the env (verified by construction).
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (kmap/install!) (rl/install!)
    (is (some? (kenv/lookup (a/env) (name/from-string "Map.join_filter_append_perm")))
        "Map.join_filter_append_perm is proven + installed")))

(deftest lookup-insert-thin-via-split
  ;; #146 (real BYCASES cluster): the THIN prove-lookup-insert (faithful `split` tactic) must
  ;; kernel-check the SAME goal the legacy hand-built by-cases proof targets (differential).
  ;; `simp [lookup_cons]` unfolds the LHS to a `List.filter.match_1` MATCHER, so `split` uses the
  ;; faithful matcher splitter (ansatz Split.lean applyMatchSplitter port, S5) — which needs
  ;; MatcherInfo loaded (the raw-replay test env doesn't go through init!, so load it explicitly).
  (if-let [kenv-init @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv-init)
      (matchers/load-bundled-matchers!)            ;; inherit Lean MatcherInfo for the `split` matcher path
      (kmap/install!) (rl/install!)
      (let [legacy-goal (.type (kenv/lookup (a/env) (nm "List.lookup_insert")))
            [g-new p-new] (rl/prove-lookup-insert-thin)
            checks (fn [g p] (and g p (try (kenv/check-constant (a/env) (kenv/mk-thm (nm "__chk") [] g p)) true
                                           (catch Throwable _ false))))]
        (is (some? p-new) "thin split proof produced")
        (is (= (str legacy-goal) (str g-new)) "thin goal byte-identical to legacy")
        (is (true? (checks g-new p-new)) "thin split proof kernel-checks its own goal")
        (is (true? (checks legacy-goal p-new))
            "thin `(split)` proof ALSO proves the legacy lookup_insert goal (differential) — faithful matcher splitter")))
    (is true "SKIP: no Init env")))

(deftest lookup-filter-ne-thin
  ;; #146 BYCASES cluster CLOSED: the THIN prove-lookup-filter-ne (~6-line tactic block) must
  ;; kernel-check the SAME goal the legacy ~88-LOC hand-built by-cases/focus/rewrite proof targets.
  ;; Exercises all three ansatz simp fixes: disc-tree beq_iff_eq keying, level-resolved polymorphic
  ;; LawfulBEq discharge, and faithful matcher-discriminant congruence (so the `List.filter.match_1`
  ;; discriminant `beq k fst` rewrites to a literal via the branch hyp + `hne` and the matcher reduces).
  (if-let [kenv-init @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv-init)
      (matchers/load-bundled-matchers!)
      (kmap/install!) (rl/install!)
      (let [[g-leg _]   ((requiring-resolve 'wandler.laws.relational/prove-lookup-filter-ne))
            [g-new p-new] (rl/prove-lookup-filter-ne-thin)
            checks (fn [g p] (and g p (try (kenv/check-constant (a/env) (kenv/mk-thm (nm "__chk_fne") [] g p)) true
                                           (catch Throwable _ false))))]
        (is (some? p-new) "thin filter-ne proof produced")
        (is (= (str g-leg) (str g-new)) "thin goal byte-identical to legacy hand-built goal")
        (is (true? (checks g-new p-new)) "thin proof kernel-checks its own goal (check-constant)")
        (is (true? (checks g-leg p-new))
            "thin proof ALSO proves the legacy lookup_filter_ne goal (differential)")))
    (is true "SKIP: no Init env")))
