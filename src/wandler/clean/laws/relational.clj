(ns wandler.clean.laws.relational
  "Phase 8 Level 2 (clean tree) — the SEMIJOIN / ANTI-JOIN relational laws, re-proven THINLY.
   These let the optimizer rewrite a membership filter `filter (x ∈ ys) xs` into an index probe
   `filter (isSome (lookup x (group_by id ys))) xs` (and the negated anti-join), turning a nested-loop
   O(|xs|·|ys|) scan into a hash probe. The OLD engine (`wandler.laws.relational`) proved the crux
   `Map.lookup_group_by` by a ~60-line hand-built induction (manual IH-at-accumulator + nested
   by-cases over the `Map = Subtype` representation boundary). Here the whole chain is THIN tactic
   scripts (the `Eq.ndrec`-over-Subtype concern, #41, is resolved: the Subtype boundary is crossed by
   `Map.lookup_insert`'s opaque-unfold-during-isDefEq, and `rewrite Map.isSome_lookup_insert` fires as
   a controlled `rw` where simp's disc-tree can't).

   Chain: Map.gbStepId (opaque group_by-id step) → Map.isSome_lookup_insert → Map.lookup_group_by_gen
   (accumulator-generalized presence invariant) → Map.lookup_group_by (closed form, group_by) →
   List.elem_filter_eq_index_probe (semijoin) + List.elem_not_filter_eq_index_probe (anti-join)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [wandler.clean.laws.bucket :as bucket]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))
(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ lvl/zero))
(defn- c [s ls] (e/const' (nm/from-string s) ls))

(defn- install-gbStepId!
  "Admit the opaque group_by-id fold step `Map.gbStepId K dec = λ m x. Map.insert x (x :: getD (lookup
   x m) []) m` (a def, not a theorem; `Map.group_by id` is def-eq to a foldl over it)."
  []
  (when-not (has? "Map.gbStepId")
    (let [fK (e/fvar 84001) fd (e/fvar 84003)
          type0 (e/sort' L1)
          listK (e/app (c "List" [z]) fK)
          mapKLK (e/app* (c "Map" [z z]) fK listK)
          deceqK (e/app (c "DecidableEq" [L1]) fK)
          x (e/bvar 0) m (e/bvar 1)
          bucket-e (e/app* (c "List.cons" [z]) fK x
                           (e/app* (c "Option.getD" [z]) listK
                                   (e/app* (c "Map.lookup" []) fK listK fd x m)
                                   (e/app (c "List.nil" [z]) fK)))
          inner (e/app* (c "Map.insert" []) fK listK fd x bucket-e m)
          val (-> inner (#(e/lam "x" fK % :default)) (#(e/lam "m" mapKLK % :default))
                  (#(e/lam "dec" deceqK (e/abstract1 % 84003) :default))
                  (#(e/lam "K" type0 (e/abstract1 % 84001) :default)))
          ty (-> (e/forall' "m" mapKLK (e/forall' "x" fK mapKLK :default) :default)
                 (#(e/forall' "dec" deceqK (e/abstract1 % 84003) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 84001) :default)))]
      (swap! a/ansatz-env env/check-constant
             (env/mk-def (nm/from-string "Map.gbStepId") [] ty val :hints :opaque)))))

(defn install!
  "Install the semijoin/anti-join relational laws (idempotent). Builds on `bucket/install!` (for
   `Map.lookup_insert` + the List/Bool prelude). Each `theorem` is kernel `check-constant`-verified."
  []
  (bucket/install!)
  (install-gbStepId!)

  ;; isSome_lookup_insert: presence after an insert — `isSome (lookup k (insert k' v m)) = (k==k') ∨
  ;; isSome (lookup k m)`. The per-step lemma the group_by invariant rewrites with.
  (a/deftheorem Map.isSome_lookup_insert
    [K :- Type, V :- Type, dec :- (DecidableEq K), k :- K, k' :- K, v :- V, m :- (Map K V)]
    (= Bool (Option.isSome (Map.lookup K V dec k (Map.insert K V dec k' v m)))
            (Bool.or (BEq.beq K (instBEqOfDecidableEq K dec) k k') (Option.isSome (Map.lookup K V dec k m))))
    (rewrite Map.lookup_insert)
    (split)
    (all_goals (simp_all [cond cond_true cond_false Option.isSome Bool.true_or Bool.false_or Bool.or_true Bool.or_false])))

  ;; lookup_group_by_gen: the accumulator-generalized presence invariant —
  ;;   isSome (lookup k (foldl gbStepId m xs)) = (k ∈ xs) ∨ isSome (lookup k m).
  ;; `induction xs generalizing m` (the quantified IH auto-applies at the recursive accumulator via
  ;; simp_all), `unfold Map.gbStepId` exposes the insert so `rewrite Map.isSome_lookup_insert` fires
  ;; across the Subtype boundary, then `by_cases (k == head)` resolves the elem-cons matcher and the
  ;; Bool.or rearrangement closes.
  (a/deftheorem Map.lookup_group_by_gen
    [K :- Type, dec :- (DecidableEq K), k :- K, xs :- (List K), m :- (Map K (List K))]
    (= Bool
       (Option.isSome (Map.lookup K (List K) dec k (List.foldl (Map.gbStepId K dec) m xs)))
       (Bool.or (List.elem K (instBEqOfDecidableEq K dec) k xs) (Option.isSome (Map.lookup K (List K) dec k m))))
    (induction xs generalizing m)
    (all_goals (simp_all [List.foldl_nil List.foldl_cons]))
    (all_goals (try (unfold Map.gbStepId)))
    (all_goals (try (rewrite Map.isSome_lookup_insert)))
    (all_goals (try (by_cases (BEq.beq K (instBEqOfDecidableEq K dec) k head))))
    (all_goals (try (simp_all [List.elem_cons List.elem_nil Bool.or_assoc Bool.or_comm Bool.false_or Bool.or_false Bool.true_or Bool.or_true beq_iff_eq beq_self_eq_true cond cond_true cond_false]))))

  ;; lookup_group_by: closed form at `Map.group_by id` (what the semijoin consumes). From the gen at
  ;; m := empty; the `isSome (lookup k empty)` disjunct collapses by `Bool.or_false` (def-eq to false).
  (a/deftheorem Map.lookup_group_by
    [K :- Type, dec :- (DecidableEq K), k :- K, xs :- (List K)]
    (= Bool (Option.isSome (Map.lookup K (List K) dec k (Map.group_by K K dec (fn [x :- K] x) xs)))
            (List.elem K (instBEqOfDecidableEq K dec) k xs))
    (rewrite (Map.lookup_group_by_gen K dec k xs (Map.empty K (List K))))
    (exact (Bool.or_false (List.elem K (instBEqOfDecidableEq K dec) k xs))))

  ;; semijoin: a membership filter equals the index-probe filter — `filter (x ∈ ys) xs =
  ;; filter (isSome (lookup x (group_by id ys))) xs`. Induction on xs; per element the predicates agree
  ;; by `lookup_group_by` (explicit-args rewrite of the ite condition), tails by the IH.
  (a/deftheorem List.elem_filter_eq_index_probe
    [K :- Type, dec :- (DecidableEq K), xs :- (List K), ys :- (List K)]
    (= (List K)
       (List.filter (fn [x :- K] (List.elem K (instBEqOfDecidableEq K dec) x ys)) xs)
       (List.filter (fn [x :- K] (Option.isSome (Map.lookup K (List K) dec x (Map.group_by K K dec (fn [x :- K] x) ys)))) xs))
    (induction xs)
    (all_goals (simp_all [List.filter_nil List.filter_cons]))
    (all_goals (try (rewrite (Map.lookup_group_by K dec head ys))))
    (all_goals (try (rfl)))
    (all_goals (try (simp_all [List.filter_nil List.filter_cons]))))

  ;; anti-join: the negated semijoin — `filter (x ∉ ys) xs = filter (¬isSome (lookup x …)) xs`.
  (a/deftheorem List.elem_not_filter_eq_index_probe
    [K :- Type, dec :- (DecidableEq K), xs :- (List K), ys :- (List K)]
    (= (List K)
       (List.filter (fn [x :- K] (Bool.not (List.elem K (instBEqOfDecidableEq K dec) x ys))) xs)
       (List.filter (fn [x :- K] (Bool.not (Option.isSome (Map.lookup K (List K) dec x (Map.group_by K K dec (fn [x :- K] x) ys))))) xs))
    (induction xs)
    (all_goals (simp_all [List.filter_nil List.filter_cons]))
    (all_goals (try (rewrite (Map.lookup_group_by K dec head ys))))
    (all_goals (try (rfl)))
    (all_goals (try (simp_all [List.filter_nil List.filter_cons]))))

  ;; ── filter→join PUSHDOWN (B + A here; C = TODO) — push a key-predicate through Map.join ──────────
  ;; The OLD engine proved B/A by hand-built induction + a custom step-driver; here they are THIN.
  ;; C (`Map.filter_join_pushdown`, what the optimizer consumes) composes A over Nat Map.join with B as
  ;; the per-row premise. A thin `(rw [Map.join_eq])×2 (apply A)(intro)(apply B)` STALLS (the unfolded
  ;; flatMap doesn't syntactically match A's shape for `apply`), so C must be ported as the faithful
  ;; TERM-COMPOSITION (old `wandler.laws.relational/compose-C`) over the now-clean A,B constants.
  ;; ROOT-CAUSE FIX (this is why the naive thin attempt HUNG): use the GUARDED filter-cons lemmas
  ;; `List.filter_cons_of_pos` / `List.filter_cons_of_neg` — they fire only once the predicate value is
  ;; decided by `by_cases`. NEVER put bare `List.filter_cons` in a simp set with a `cond`/`bif` goal: it
  ;; unfolds filter-on-cons UNCONDITIONALLY into a cond and `simp_all` loops on it forever.
  ;;
  ;; B: filter (λpr. p pr.fst) (map (λy.(x,y)) L) = bif (p x) (map (λy.(x,y)) L) [].
  (a/deftheorem List.filter_map_pair_eq_cond
    [X :- Type, Y :- Type, p :- (=> X Bool), x :- X, L :- (List Y)]
    (= (List (Prod X Y))
       (List.filter (fn [pr :- (Prod X Y)] (p (Prod.fst pr)))
         (List.map (fn [y :- Y] (Prod.mk x y)) L))
       (bif (p x) (List.map (fn [y :- Y] (Prod.mk x y)) L) (List.nil (Prod X Y))))
    (induction L)
    (all_goals (simp [List.map_cons List.map_nil List.filter_nil]))
    (all_goals (try (by_cases (p x))))
    (all_goals (try (simp_all [List.filter_cons_of_pos List.filter_cons_of_neg
                               List.filter_nil List.map_nil List.map_cons cond_true cond_false]))))

  ;; A: per-row premise ⇒ filter pushes through flatMap —
  ;;   (∀x. filter q (g x) = bif (p x) (g x) []) → filter q (flatMap g xs) = flatMap g (filter p xs).
  (a/deftheorem List.filter_flatMap_cond
    [A :- (Sort 1), B :- (Sort 1), g :- (=> A (List B)), q :- (=> B Bool),
     p :- (=> A Bool), xs :- (List A),
     H :- (forall [x A] (= (List B) (List.filter q (g x)) (bif (p x) (g x) (List.nil B))))]
    (= (List B) (List.filter q (List.flatMap g xs)) (List.flatMap g (List.filter p xs)))
    (induction xs)
    (all_goals (simp [List.flatMap_cons List.flatMap_nil List.filter_nil]))
    (all_goals (try (simp [List.filter_append])))
    (all_goals (try (rw [(H head)])))
    (all_goals (try (by_cases (p head))))
    (all_goals (try (simp_all [List.filter_cons_of_pos List.filter_cons_of_neg
                               cond_true cond_false List.filter_append
                               List.flatMap_cons List.flatMap_nil List.filter_nil
                               List.append_nil List.nil_append]))))

  ;; C: Map.filter_join_pushdown — filter (p∘fst) (join kf lf xs ys) = join kf lf (filter p xs) ys.
  ;; THIN: `rw [Map.join_eq]` (×2) exposes the join's `flatMap g` on both sides, `apply A`
  ;; (filter_flatMap_cond) leaves the per-row premise, discharged by `apply B`
  ;; (filter_map_pair_eq_cond). This relies on ansatz `apply` matching via lazy meta-isDefEq (it
  ;; whnf's the bucket `g a → map mk L` once WITHOUT normalizing the stuck `group_by` inside the
  ;; bucket list — see the apply lazy-isDefEq fix). Shape-agnostic: no manual subterm extraction
  ;; (the earlier term-composition port of `compose-C` is retired now that `apply` doesn't diverge).
  (a/deftheorem Map.filter_join_pushdown
    [p :- (=> Nat Bool), kf :- (=> Nat Nat), lf :- (=> Nat Nat),
     ys :- (List Nat), xs :- (List Nat)]
    (= (List (Prod Nat Nat))
       (List.filter (fn [pr :- (Prod Nat Nat)] (p (Prod.fst pr)))
         (Map.join Nat Nat Nat instDecidableEqNat kf lf xs ys))
       (Map.join Nat Nat Nat instDecidableEqNat kf lf (List.filter p xs) ys))
    (rw [Map.join_eq]) (rw [Map.join_eq])
    (apply List.filter_flatMap_cond) (intro a) (apply List.filter_map_pair_eq_cond))
  :installed)
