(ns ansatz.semijoin-test
  "Verified relational SEMIJOIN / hash-join rewrite:

     filter (fun x => List.elem x ys) xs
       = filter (fun x => isSome (Map.lookup x (Map.group_by id ys))) xs

   The left side is the O(|xs|·|ys|) nested-loop membership filter; the right builds the
   index `group_by id ys` once (O(|ys|)) and probes it O(1) per element. Certified by
   `List.filter_congr` + `Eq.symm (Map.lookup_group_by …)` — a one-shot `exact`, no
   tactic search. Builds on the full lookup/group_by foundation. Gated on Init."
  (:require [ansatz.core :as a]
            [ansatz.kmap :as kmap]
            [ansatz.kmap-lookup-test :as klt]
            [ansatz.kmap-group-by-test :as gbt]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.optimize :as opt]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- gf [ps n] (e/fvar (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps)))))
;; AUTHORITATIVE: full kernel check-constant, not the lenient TypeChecker.inferType.
(defn- checks? [term goal] (kenv/verifies? (a/env) goal term))
(defn- reg! [n g p] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) [] g p))))

;; Register the full lookup/group_by foundation (proved in the sibling test nss).
(defn- register-foundation! []
  (binding [a/*verbose* false]
    (let [[g p] (#'klt/prove-lookup-filter-ne)] (reg! "List.lookup_filter_ne" g p))
    (let [[g p] (#'klt/prove-lookup-insert)] (reg! "List.lookup_insert" g p))
    (#'gbt/register-gbstepid!)
    (let [[g p] (#'gbt/prove-map-lookup-insert)] (reg! "Map.lookup_insert" g p))
    (let [[g p] (#'gbt/prove-issome-lookup-insert)] (reg! "Map.isSome_lookup_insert" g p))
    (let [[g p] (#'gbt/prove-gen)] (reg! "Map.lookup_group_by_gen" g p))
    (let [[_ proof] (#'gbt/prove-foldl-final)
          gbg (#'gbt/group-by-goal)]
      ;; the foldl-form proof inhabits the group_by statement by def-eq
      (reset! a/ansatz-env (kenv/check-constant (a/env) (kenv/mk-thm (nm "Map.lookup_group_by") [] gbg proof))))))

(defn- prove-semijoin []
  (let [fK (e/fvar 87001) fd (e/fvar 87003) fxs (e/fvar 87005) fys (e/fvar 87007)
        listK (e/app (e/const' (nm "List") [z]) fK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        idf (e/lam "x" fK (e/bvar 0) :default)
        gbys (e/app* (e/const' (nm "Map.group_by") []) fK fK fd idf fys)
        pf (e/lam "x" fK (e/app* (e/const' (nm "List.elem") [z]) fK beqI (e/bvar 0) fys) :default)
        qf (e/lam "x" fK (e/app* (e/const' (nm "Option.isSome") [z]) listK
                                 (e/app* (e/const' (nm "Map.lookup") []) fK listK fd (e/bvar 0) gbys)) :default)
        filt (fn [f l] (e/app* (e/const' (nm "List.filter") [z]) fK f l))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listK (filt pf fxs) (filt qf fxs))
                 (#(e/forall' "ys" listK (e/abstract1 % 87007) :default))
                 (#(e/forall' "xs" listK (e/abstract1 % 87005) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 87003) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 87001) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "dec" "xs" "ys"])
        gK (gf ps "K") gd (gf ps "dec") gxs (gf ps "xs") gys (gf ps "ys")
        glistK (e/app (e/const' (nm "List") [z]) gK)
        gbeqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) gK gd)
        gp (e/lam "x" gK (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 0) gys) :default)
        ggbys (e/app* (e/const' (nm "Map.group_by") []) gK gK gd (e/lam "x" gK (e/bvar 0) :default) gys)
        gq (e/lam "x" gK (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                                 (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 0) ggbys)) :default)
        ;; x ∈ xs  — Membership.mem is collection-first, element-second
        memty (e/app* (e/const' (nm "Membership.mem") [z z]) gK glistK
                      (e/app (e/const' (nm "List.instMembership") [z]) gK) gxs (e/bvar 0))
        isS-x (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                      (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 1) ggbys))
        elem-x (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 1) gys)
        lgb (e/app* (e/const' (nm "Map.lookup_group_by") []) gK gd (e/bvar 1) gys)
        ;; h : ∀ x ∈ xs, (elem x ys) = (isSome (lookup x (group_by id ys)))  = Eq.symm lookup_group_by
        hterm (e/lam "x" gK (e/lam "hx" memty
                              (e/app* (e/const' (nm "Eq.symm") [L1]) (e/const' (nm "Bool") []) isS-x elem-x lgb) :default) :default)
        pf-term (e/app* (e/const' (nm "List.filter_congr") [z]) gK gp gq gxs hterm)
        ps (basic/exact ps pf-term)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn- prove-anti-join []
  ;; The NOT-IN / set-difference variant: same as the semijoin with Bool.not wrapped
  ;; on both predicates and h = congrArg Bool.not (Eq.symm lookup_group_by).
  (let [fK (e/fvar 87001) fd (e/fvar 87003) fxs (e/fvar 87005) fys (e/fvar 87007)
        listK (e/app (e/const' (nm "List") [z]) fK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        gbys (e/app* (e/const' (nm "Map.group_by") []) fK fK fd (e/lam "x" fK (e/bvar 0) :default) fys)
        notb (fn [b] (e/app (e/const' (nm "Bool.not") []) b))
        pf (e/lam "x" fK (notb (e/app* (e/const' (nm "List.elem") [z]) fK beqI (e/bvar 0) fys)) :default)
        qf (e/lam "x" fK (notb (e/app* (e/const' (nm "Option.isSome") [z]) listK
                                       (e/app* (e/const' (nm "Map.lookup") []) fK listK fd (e/bvar 0) gbys))) :default)
        filt (fn [f l] (e/app* (e/const' (nm "List.filter") [z]) fK f l))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listK (filt pf fxs) (filt qf fxs))
                 (#(e/forall' "ys" listK (e/abstract1 % 87007) :default))
                 (#(e/forall' "xs" listK (e/abstract1 % 87005) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 87003) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 87001) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "dec" "xs" "ys"])
        gK (gf ps "K") gd (gf ps "dec") gxs (gf ps "xs") gys (gf ps "ys")
        glistK (e/app (e/const' (nm "List") [z]) gK)
        gbeqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) gK gd)
        ggbys (e/app* (e/const' (nm "Map.group_by") []) gK gK gd (e/lam "x" gK (e/bvar 0) :default) gys)
        gp (e/lam "x" gK (notb (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 0) gys)) :default)
        gq (e/lam "x" gK (notb (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                                       (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 0) ggbys))) :default)
        memty (e/app* (e/const' (nm "Membership.mem") [z z]) gK glistK
                      (e/app (e/const' (nm "List.instMembership") [z]) gK) gxs (e/bvar 0))
        isS-x (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                      (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 1) ggbys))
        elem-x (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 1) gys)
        lgb (e/app* (e/const' (nm "Map.lookup_group_by") []) gK gd (e/bvar 1) gys)
        sym (e/app* (e/const' (nm "Eq.symm") [L1]) (e/const' (nm "Bool") []) isS-x elem-x lgb)
        ca (e/app* (e/const' (nm "congrArg") [L1 L1]) (e/const' (nm "Bool") []) (e/const' (nm "Bool") [])
                   elem-x isS-x (e/const' (nm "Bool.not") []) sym)
        hterm (e/lam "x" gK (e/lam "hx" memty ca :default) :default)
        pf-term (e/app* (e/const' (nm "List.filter_congr") [z]) gK gp gq gxs hterm)
        ps (basic/exact ps pf-term)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(deftest semijoin-rewrite
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (register-foundation!)
      (let [[g p] (prove-semijoin)]
        (is (some? p) "semijoin rewrite proved")
        (is (true? (checks? p g))
            "filter(elem ·ys)xs = filter(isSome(lookup · (group_by id ys)))xs — kernel-checks")
        ;; Register the law and confirm the COST-DIRECTED optimizer auto-adopts it:
        ;; predicate-extra-cost charges the O(|ys|) elem scan, so the build-once index
        ;; probe wins — and the adopted step is kernel-certified (verified?).
        (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm "List.elem_filter_eq_index_probe") [] g p)))
        (let [natT (e/const' (nm "Nat") [])
              listN (e/app (e/const' (nm "List") [z]) natT)
              beqN (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) natT (e/const' (nm "instDecidableEqNat") []))
              pred (e/lam "x" natT (e/app* (e/const' (nm "List.elem") [z]) natT beqN (e/bvar 0) (e/fvar 70002)) :default)
              term (e/app* (e/const' (nm "List.filter") [z]) natT pred (e/fvar 70001))
              lctx {70001 {:name "xs" :type listN} 70002 {:name "ys" :type listN}}
              rc (opt/optimize-cost (a/env) term :lctx lctx
                                    :pool (conj opt/cost-rewrites "List.elem_filter_eq_index_probe"))]
          (is (some #{"List.elem_filter_eq_index_probe"} (:rewrites rc))
              "optimizer auto-adopts the semijoin (cost-directed)")
          (is (true? (:verified? rc)) "the adopted semijoin step is kernel-certified")
          (is (clojure.string/includes? (e/->string (:term rc)) "Map.group_by")
              "result is the build-once index-probe form")))
      ;; ── anti-join (NOT IN / set difference) ──
      (let [[g p] (prove-anti-join)]
        (is (some? p) "anti-join rewrite proved")
        (is (true? (checks? p g))
            "filter(¬elem ·ys)xs = filter(¬isSome(lookup ·(group_by id ys)))xs — kernel-checks")
        (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm "List.elem_not_filter_eq_index_probe") [] g p)))
        (let [natT (e/const' (nm "Nat") [])
              listN (e/app (e/const' (nm "List") [z]) natT)
              beqN (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) natT (e/const' (nm "instDecidableEqNat") []))
              pred (e/lam "x" natT (e/app (e/const' (nm "Bool.not") [])
                                          (e/app* (e/const' (nm "List.elem") [z]) natT beqN (e/bvar 0) (e/fvar 70002))) :default)
              term (e/app* (e/const' (nm "List.filter") [z]) natT pred (e/fvar 70001))
              lctx {70001 {:name "xs" :type listN} 70002 {:name "ys" :type listN}}
              rc (opt/optimize-cost (a/env) term :lctx lctx
                                    :pool (conj opt/cost-rewrites "List.elem_not_filter_eq_index_probe"))]
          (is (some #{"List.elem_not_filter_eq_index_probe"} (:rewrites rc))
              "optimizer auto-adopts the anti-join (cost-directed)")
          (is (true? (:verified? rc)) "the adopted anti-join step is kernel-certified"))))
    (is true "SKIP semijoin-rewrite: no Init env")))
