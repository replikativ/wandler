(ns wandler.egraph-optimize-test
  "E-graph search layer for the verified optimizer (roadmap item B).

   `wandler.optimize.egraph/saturate-and-extract` saturates grind's e-graph with the
   oriented laws, extracts the cost-minimal equivalent plan by `pipeline-cost`, and
   certifies `orig = extracted` with a kernel proof (grind's `mk-eq-proof`,
   re-checked by `verified-rewrite?`). Wired into `optimize-cost` via `:use-egraph?`.

   Matcher scope: app-level fusion (map_map, filter_filter), the filter↔map reorder,
   AND (task #34) UNDER-BINDER matching — laws whose LHS contains a lambda with pattern
   vars (the semijoin section `λx. elem x ys`) now E-match beneath the binder, faithful
   to Lean 4 `Grind/EMatch.lean` (open the binder with a fresh local, match the body;
   lambda binder types ignored, forall domains matched). Gated on the Init env.

   This test also pins the universe-level unification fix in the E-matcher: the
   polymorphic `List.map_map` (level params u,v,w) only fires once the matcher
   unifies the theorem's level params with the term's concrete `0` levels."
  (:require [wandler.core]
            [ansatz.core :as a]
            [wandler.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [wandler.optimize :as opt]
            [wandler.optimize.egraph :as ege]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.ematch :as ematch]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private natT (e/const' (nm "Nat") []))
(def ^:private boolT (e/const' (nm "Bool") []))
(def ^:private listNat (e/app (e/const' (nm "List") [z]) natT))
(def ^:private natBool (e/forall' "_" natT boolT :default))
(def ^:private natNat (e/forall' "_" natT natT :default))
;; fvars: p,q : Nat→Bool ; g : Nat→Nat ; l : List Nat
(def ^:private fp (e/fvar 1)) (def ^:private fq (e/fvar 2))
(def ^:private fl (e/fvar 3)) (def ^:private fg (e/fvar 4))
(def ^:private lctx {1 {:name "p" :type natBool} 2 {:name "q" :type natBool}
                     3 {:name "l" :type listNat} 4 {:name "g" :type natNat}})
(defn- filt [pred l] (e/app* (e/const' (nm "List.filter") [z]) natT pred l))
(defn- mp [f l] (e/app* (e/const' (nm "List.map") [z z]) natT natT f l))

(defn- with-init [f]
  (if-let [kenv @test-env/init-full-env]
    (do (reset! a/ansatz-env kenv) (f))
    (is true "SKIP: no Init env")))

(deftest saturate-and-extract-fuses-and-certifies
  (with-init
    (fn []
      (let [env (a/env)
            cases [["filter_filter" (filt fp (filt fq fl))                1000.0]
                   ["map_map"       (mp fg (mp fg fl))                    1000.0]
                   ["filter-map-filter" (filt fp (mp fg (filt fq fl)))    1500.0]]]
        (doseq [[label term expect] cases]
          (let [r (ege/saturate-and-extract env term :lctx lctx)]
            (is (:changed? r) (str label ": e-graph changed the term"))
            (is (:verified? r) (str label ": composed proof kernel-certifies"))
            (is (< (:cost r) (opt/pipeline-cost term))
                (str label ": cost strictly lower"))
            (is (== (:cost r) expect)
                (str label ": reaches the expected optimum " expect))))))))

(deftest optimize-cost-use-egraph-matches-or-beats-greedy
  (with-init
    (fn []
      (let [env (a/env)
            terms [(filt fp (filt fq fl))
                   (filt fp (mp fg (filt fq fl)))
                   (filt fp (mp fg (mp fg fl)))]]
        (doseq [term terms]
          (let [g (opt/optimize-cost env term :lctx lctx)
                e (opt/optimize-cost env term :lctx lctx :use-egraph? true)]
            (is (:verified? e) "e-graph optimize-cost result is kernel-certified")
            (is (:changed? e) "e-graph optimize-cost rewrote the pipeline")
            ;; Either saturation improved past base ([:egraph]) or base fusion was
            ;; already optimal so the path soundly fell back ([]).
            (is (contains? #{[] [:egraph]} (:rewrites e)) "valid rewrites marker")
            ;; saturation must never do WORSE than greedy (same or lower cardinality)
            (is (<= (opt/pipeline-cost (:term e)) (opt/pipeline-cost (:term g)))
                "e-graph cost ≤ greedy cost")))))))

(deftest optimize-cost-egraph-adopts-reorder
  ;; The terms that genuinely need a non-confluent reorder (filter↔map) — here the
  ;; e-graph search adopts it and is credited as the source.
  (with-init
    (fn []
      (let [env (a/env)]
        (doseq [term [(filt fp (mp fg (filt fq fl)))
                      (filt fp (mp fg (mp fg fl)))]]
          (let [e (opt/optimize-cost env term :lctx lctx :use-egraph? true)]
            (is (= [:egraph] (:rewrites e)) "reorder sourced from e-graph saturation")
            (is (:verified? e) "kernel-certified")
            (is (< (opt/pipeline-cost (:term e)) (opt/pipeline-cost term))
                "strictly cheaper than the input")))))))

(deftest extract-min-cost-picks-cheapest-member
  (with-init
    (fn []
      (let [env (a/env)
            term (filt fp (filt fq fl))
            thms (ematch/prepare-theorems env ["List.filter_filter"])
            gs (-> (eg/mk-grind-state env) (eg/internalize term 0)
                   (#(:gs (ematch/run-ematch % thms #{}))))
            best (eg/extract-min-cost gs term opt/pipeline-cost)]
        ;; saturation materialized the fused single-filter form in the eqclass
        (is (>= (:members best) 2) "filter_filter fired (eqclass grew)")
        (is (== (:cost best) 1000.0) "cheapest member is the single fused filter")))))

(deftest ematch-unifies-universe-levels
  ;; Regression: the polymorphic List.map_map (level params u_1,u_2,u_3) must fire
  ;; against a concrete `.{0,0}` term. Before the level-unification fix the
  ;; instantiated LHS carried symbolic `u_i`, landing in a separate eqclass, so the
  ;; eqclass never grew. Asserting growth pins the fix.
  (with-init
    (fn []
      (let [env (a/env)
            term (mp fg (mp fg fl))
            thms (ematch/prepare-theorems env ["List.map_map"])
            gs (-> (eg/mk-grind-state env) (eg/internalize term 0)
                   (#(:gs (ematch/run-ematch % thms #{}))))
            members (eg/collect-eqc gs (eg/get-root gs term))]
        (is (>= (count members) 2)
            "map_map fired across universe-level params (eqclass grew to ≥2)")))))

(deftest under-binder-matching
  ;; #34: the E-matcher matches a LAMBDA-pattern law BENEATH the binder — the case the
  ;; semijoin section `λx. elem x ys` needs. Pattern `filter (λx. elem x ys) xs` (ys, xs
  ;; pattern vars; ys lives under the λ) matches the concrete `filter (λa. elem a L) X`
  ;; with ys←L, xs←X. The old structural `(= pat term)` on the lambda gave 0 matches.
  ;; Init-only (no Map needed). Soundness is unaffected — a capturing match would yield a
  ;; dangling fvar the downstream kernel check rejects; this only finds MORE valid matches.
  (if-let [kenv @test-env/init-full-env]
    (do (reset! a/ansatz-env kenv)
        (let [beqN (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) natT
                           (e/const' (nm "instDecidableEqNat") []))
              elem (fn [x ys] (e/app* (e/const' (nm "List.elem") [z]) natT beqN x ys))
              filt (fn [pred l] (e/app* (e/const' (nm "List.filter") [z]) natT pred l))
              ;; pattern, telescope [ys xs]: ys = bvar 1 (→ bvar 2 under the λ), xs = bvar 0
              pat  (filt (e/lam "x" natT (elem (e/bvar 0) (e/bvar 2)) :default) (e/bvar 0))
              term (filt (e/lam "a" natT (elem (e/bvar 0) (e/fvar 71001)) :default) (e/fvar 71002))
              gs   (-> (eg/mk-grind-state (a/env)) (eg/internalize term 0))
              matches (ematch/match-in-eqclass gs #{} pat term)]
          (is (= 1 (count matches)) "lambda-pattern law matches under the binder")
          (let [vars (:vars (:assignment (first matches)))]
            (is (= (e/fvar 71001) (get vars 1)) "ys (under the λ) ← L")
            (is (= (e/fvar 71002) (get vars 0)) "xs ← X"))))
    (is true "SKIP under-binder-matching: no Init env")))

(deftest a-defn-can-opt-into-the-egraph
  ;; USABILITY: a/defn reaches the e-graph via `(binding [opt/*use-egraph* true] …)`. The result is
  ;; kernel-certified and runs identically to the greedy path; wandler.core/plan still explains it.
  (with-init
    (fn []
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn eg-greedy [xs :- (List Nat)] (List Nat)
                 (mapv (fn [x] (Nat.succ x)) (filterv (fn [x] (Nat.ble 3 x)) xs))))
        (binding [opt/*use-egraph* true]
          (eval '(ansatz.core/defn eg-egraph [xs :- (List Nat)] (List Nat)
                   (mapv (fn [x] (Nat.succ x)) (filterv (fn [x] (Nat.ble 3 x)) xs))))))
      (let [g (wandler.core/explain "eg-greedy"), e (wandler.core/explain "eg-egraph")]
        (is (true? (:verified? g)) "greedy verified")
        (is (and (:changed? e) (:verified? e)) "e-graph path changed + kernel-certified")
        (is (= [:egraph] (:rewrites e)) "explain marks the e-graph was used")
        ;; both produce the same (correct) runtime
        (is (= [4 5 6] (vec ((resolve 'eg-greedy) (list 1 2 3 4 5)))))
        (is (= [4 5 6] (vec ((resolve 'eg-egraph) (list 1 2 3 4 5)))) "e-graph result runs identically")))))
