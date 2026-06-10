(ns ansatz.filter-join-test
  "Verified relational pushdown: `filter (p∘fst) (Map.join … xs ys) =
   Map.join … (filter p xs) ys`. Built from two Init-only kernel-checked lemmas
   and composed at the term level:

     A  List.filter_flatMap_cond     (∀x, filter q (g x) = cond (p x) (g x) [])
                                      → filter q (flatMap g xs) = flatMap g (filter p xs)
     B  List.filter_map_pair_eq_cond filter (p∘fst) (map (x,·) L) = cond (p x) (map (x,·) L) []
     C  Map.filter_join_pushdown     = A instantiated with B as the per-row premise.

   These exercise the Lean-faithful simp reductions (reduceProjFn/simpMatchDiscrs/
   reduceRecMatcher) — B's proof needs all three. Gated on an Init env."
  (:require [ansatz.core :as a]
            [ansatz.kmap :as kmap]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]
            [ansatz.optimize :as opt]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- nm [s] (name/from-string s))
(defn- fv [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
;; AUTHORITATIVE: full kernel check-constant, not the lenient TypeChecker.inferType.
(defn- checks? [term goal] (kenv/verifies? (a/env) goal term))

;; ── stack driver: isolate each goal so per-goal `solved?` is meaningful ──
(defn- solve-all [ps step]
  (loop [ps ps n 0]
    (if (or (empty? (:goals ps)) (> n 100)) ps
      (let [g (:goals ps), gid (first g), rest-g (vec (rest g))
            ps2 (try (step (assoc ps :goals [gid])) (catch Throwable _ (assoc ps :goals [])))
            ps3 (assoc ps2 :goals (vec (concat (:goals ps2) rest-g)))]
        (recur ps3 (inc n))))))

(defn- beta-spine [f args]
  (loop [f f args args]
    (if (and (e/lam? f) (seq args))
      (recur (e/instantiate1 (e/lam-body f) (first args)) (rest args))
      (if (seq args) (apply e/app* f args) f))))

;; ── Lemma B : filter (p∘fst) (map (x,·) L) = cond (p x) (map (x,·) L) [] ──
(defn- prove-B []
  (let [z lvl/zero L1 (lvl/succ z) type0 (e/sort' L1)
        boolT (e/const' (nm "Bool") [])
        fX (e/fvar 64001) fY (e/fvar 64002) fp (e/fvar 64003) fx (e/fvar 64004) fL (e/fvar 64005)
        prodXY (e/app* (e/const' (nm "Prod") [z z]) fX fY)
        listP (e/app (e/const' (nm "List") [z]) prodXY)
        mk (e/lam "y" fY (e/app* (e/const' (nm "Prod.mk") [z z]) fX fY fx (e/bvar 0)) :default)
        fstpred (e/lam "pr" prodXY (e/app fp (e/app* (e/const' (nm "Prod.fst") [z z]) fX fY (e/bvar 0))) :default)
        mapmk (fn [l] (e/app* (e/const' (nm "List.map") [z z]) fY prodXY mk l))
        filt (fn [l] (e/app* (e/const' (nm "List.filter") [z]) prodXY fstpred l))
        condR (e/app* (e/const' (nm "cond") [L1]) listP (e/app fp fx) (mapmk fL) (e/app (e/const' (nm "List.nil") [z]) prodXY))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listP (filt (mapmk fL)) condR)
                 (#(e/forall' "L" (e/app (e/const' (nm "List") [z]) fY) (e/abstract1 % 64005) :default))
                 (#(e/forall' "x" fX (e/abstract1 % 64004) :default))
                 (#(e/forall' "p" (e/forall' "_" fX boolT :default) (e/abstract1 % 64003) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 64002) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 64001) :default)))
        LEM ['List.filter_nil 'cond_true 'cond_false 'cond 'List.map_cons 'List.map_nil
             'List.filter_cons_of_pos 'List.filter_cons_of_neg]
        step (fn [ps]
               (cond
                 (fv ps "hc")
                 (let [q1 (basic/rewrite ps (e/fvar (fv ps "hc")))
                       ihid (or (fv q1 "ih_tail'") (fv q1 "ih_tail"))
                       q2 (simp/simp-all q1 LEM)
                       q3 (if (and ihid (not (proof/solved? q2))) (basic/rewrite q2 (e/fvar ihid)) q2)
                       q4 (if (proof/solved? q3) q3 (simp/simp-all q3 LEM))]
                   (if (proof/solved? q4) q4 (basic/rfl q4)))
                 (fv ps "head")
                 (let [q0 (simp/simp ps ['List.map_cons])]
                   (basic/by-cases q0 (e/app (e/fvar (fv q0 "p")) (e/fvar (fv q0 "x")))))
                 :else
                 (let [q (simp/simp-all ps LEM)]
                   (if (proof/solved? q) q
                     (basic/by-cases q (e/app (e/fvar (fv q "p")) (e/fvar (fv q "x"))))))))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "Y" "p" "x" "L"])
        ps (basic/induction ps (fv ps "L"))
        ps (solve-all ps step)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── Lemma A : per-row premise ⇒ filter pushes through flatMap ──
(defn- prove-A []
  (let [z lvl/zero L1 (lvl/succ z) type0 (e/sort' L1)
        boolT (e/const' (nm "Bool") [])
        fa (e/fvar 63001) fb (e/fvar 63002) fg (e/fvar 63003) fq (e/fvar 63004) fp (e/fvar 63005) fxs (e/fvar 63006)
        listOf (fn [t] (e/app (e/const' (nm "List") [z]) t))
        listA (listOf fa) listB (listOf fb)
        flatmap (fn [g l] (e/app* (e/const' (nm "List.flatMap") [z z]) fa fb g l))
        filterB (fn [l] (e/app* (e/const' (nm "List.filter") [z]) fb fq l))
        filterA (fn [l] (e/app* (e/const' (nm "List.filter") [z]) fa fp l))
        condB (fn [px gx] (e/app* (e/const' (nm "cond") [L1]) listB px gx (e/app (e/const' (nm "List.nil") [z]) fb)))
        hyp (e/forall' "x" fa
              (e/app* (e/const' (nm "Eq") [L1]) listB
                      (filterB (e/app fg (e/bvar 0)))
                      (condB (e/app fp (e/bvar 0)) (e/app fg (e/bvar 0)))) :default)
        concl (e/app* (e/const' (nm "Eq") [L1]) listB (filterB (flatmap fg fxs)) (flatmap fg (filterA fxs)))
        goal (-> (e/forall' "H" hyp concl :default)
                 (#(e/forall' "xs" listA (e/abstract1 % 63006) :default))
                 (#(e/forall' "p"  (e/forall' "_" fa boolT :default) (e/abstract1 % 63005) :default))
                 (#(e/forall' "q"  (e/forall' "_" fb boolT :default) (e/abstract1 % 63004) :default))
                 (#(e/forall' "g"  (e/forall' "_" fa listB :default) (e/abstract1 % 63003) :default))
                 (#(e/forall' "b"  type0 (e/abstract1 % 63002) :default))
                 (#(e/forall' "a"  type0 (e/abstract1 % 63001) :default)))
        LEM ['List.filter_cons_of_pos 'List.filter_cons_of_neg 'List.flatMap_cons 'List.flatMap_nil
             'List.filter_nil 'cond_true 'cond_false 'List.filter_append 'cond
             'List.append_nil 'List.nil_append 'List.append_eq 'List.cons_append
             'List.flatten_cons 'List.map_cons 'List.filter_cons 'List.flatMap_append]
        step (fn [ps]
               (cond
                 ;; a by-cases branch (has hc) — check BEFORE head, since the split
                 ;; cons goal carries both `head` and `hc`.
                 (fv ps "hc")
                 (let [hcid (fv ps "hc")
                       p2 (basic/rewrite ps (e/fvar hcid))
                       q (simp/simp-all p2 LEM)
                       ihid (or (fv q "ih_tail'") (fv q "ih_tail"))
                       q2 (if (and ihid (not (proof/solved? q))) (basic/rewrite q (e/fvar ihid)) q)
                       q3 (if (proof/solved? q2) q2 (simp/simp-all q2 LEM))
                       hc2 (fv q3 "hc")
                       q4 (if (and hc2 (not (proof/solved? q3))) (basic/rewrite q3 (e/fvar hc2)) q3)
                       q5 (if (proof/solved? q4) q4 (simp/simp-all q4 LEM))]
                   (if (proof/solved? q5) q5 (basic/rfl q5)))
                 ;; unsplit cons goal: expose filter q (g head) via H, then split
                 (fv ps "head")
                 (let [hd (fv ps "head")
                       p0 (simp/simp ps ['List.flatMap_cons 'List.filter_append] {})
                       p1 (basic/rewrite p0 (e/app (e/fvar (fv p0 "H")) (e/fvar hd)))
                       ph (e/app (e/fvar (fv p1 "p")) (e/fvar hd))]
                   (basic/by-cases p1 ph))
                 :else
                 (let [q (simp/simp-all ps LEM)]
                   (if (proof/solved? q) q (basic/rfl q)))))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["a" "b" "g" "q" "p" "xs" "H"])
        ps (basic/induction ps (fv ps "xs"))
        ps (solve-all ps step)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── C : compose A with B as the per-row premise for Map.join ──
(defn- compose-C []
  (let [z lvl/zero L1 (lvl/succ z)
        nat (e/const' (nm "Nat") [])
        prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat)
        listN (e/app (e/const' (nm "List") [z]) nat)
        listNN (e/app (e/const' (nm "List") [z]) prodNN)
        deceq (e/const' (nm "instDecidableEqNat") [])
        boolT (e/const' (nm "Bool") [])
        n->n (e/forall' "_" nat nat :default) n->b (e/forall' "_" nat boolT :default)
        pp (e/fvar 62001) kf (e/fvar 62002) lf (e/fvar 62003) ys (e/fvar 62004) xs (e/fvar 62005)
        joinT (fn [xs'] (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq kf lf xs' ys))
        predPair (e/lam "pr" prodNN (e/app pp (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
        filterPair (fn [l] (e/app* (e/const' (nm "List.filter") [z]) prodNN predPair l))
        filterN (fn [l] (e/app* (e/const' (nm "List.filter") [z]) nat pp l))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listNN (filterPair (joinT xs)) (joinT (filterN xs)))
                 (#(e/forall' "xs" listN (e/abstract1 % 62005) :default))
                 (#(e/forall' "ys" listN (e/abstract1 % 62004) :default))
                 (#(e/forall' "lf" n->n (e/abstract1 % 62003) :default))
                 (#(e/forall' "kf" n->n (e/abstract1 % 62002) :default))
                 (#(e/forall' "p"  n->b (e/abstract1 % 62001) :default)))
        ;; one delta step of Map.join → flatMap nat prodNN g xs (NOT reduced into brecOn)
        mj-val (.getValue (kenv/lookup (a/env) (nm "Map.join")))
        join-1 (beta-spine mj-val [nat nat nat deceq kf lf xs ys])
        g (nth (second (e/get-app-fn-args join-1)) 2)
        Bc (e/const' (nm "List.filter_map_pair_eq_cond") [])
        premise (e/lam "a" nat
                  (let [ga (e/instantiate1 (e/lam-body g) (e/bvar 0))   ; map nat prodNN (mk a) L_a
                        La (nth (second (e/get-app-fn-args ga)) 3)]
                    (e/app* Bc nat nat pp (e/bvar 0) La)) :default)
        Ac (e/const' (nm "List.filter_flatMap_cond") [])
        C (e/app* Ac nat prodNN g predPair pp xs premise)
        C-closed (-> C
                     (#(e/lam "xs" listN (e/abstract1 % 62005) :default))
                     (#(e/lam "ys" listN (e/abstract1 % 62004) :default))
                     (#(e/lam "lf" n->n (e/abstract1 % 62003) :default))
                     (#(e/lam "kf" n->n (e/abstract1 % 62002) :default))
                     (#(e/lam "p"  n->b (e/abstract1 % 62001) :default)))]
    [goal C-closed]))

(deftest filter-into-join-pushdown
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (binding [a/*verbose* false]
        ;; B
        (let [[bgoal bproof] (prove-B)]
          (is (some? bproof) "lemma B proved")
          (is (true? (checks? bproof bgoal)) "B kernel-checks")
          (reset! a/ansatz-env (kenv/add-constant (a/env)
                                 (kenv/mk-thm (nm "List.filter_map_pair_eq_cond") [] bgoal bproof))))
        ;; A
        (let [[agoal aproof] (prove-A)]
          (is (some? aproof) "lemma A proved")
          (is (true? (checks? aproof agoal)) "A kernel-checks")
          (reset! a/ansatz-env (kenv/add-constant (a/env)
                                 (kenv/mk-thm (nm "List.filter_flatMap_cond") [] agoal aproof))))
        ;; C = compose
        (let [[cgoal cproof] (compose-C)]
          (is (true? (checks? cproof cgoal))
              "C (filter-into-join pushdown) kernel-checks against the Map.join goal")
          (reset! a/ansatz-env (kenv/add-constant (a/env)
                                 (kenv/mk-thm (nm "Map.filter_join_pushdown") [] cgoal cproof)))
          (is (some? (kenv/lookup (a/env) (nm "Map.filter_join_pushdown")))
              "pushdown theorem registered"))
        ;; END-TO-END: the cost-directed search AUTO-ADOPTS the pushdown — the
        ;; cardinality cost model (pipeline-cost) prefers filtering xs BEFORE the
        ;; join even though it's SOAC-count-neutral — and the adopted rewrite is
        ;; INDEPENDENTLY kernel-certified (:verified?).
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
              r (opt/optimize-cost (a/env) term :lctx lctx)
              s (e/->string (:term r))]
          (is (contains? (set (:rewrites r)) "Map.filter_join_pushdown")
              "cost search auto-adopted the filter-into-join pushdown")
          (is (true? (:verified? r)) "the adopted rewrite is kernel-certified")
          (is (and (clojure.string/includes? s "Map.join")
                   (clojure.string/includes? s "(List.filter.{0} Nat"))
              "filter is now INSIDE the join (filters xs before joining)"))))
    (is true "SKIP filter-into-join-pushdown: no Init env")))
