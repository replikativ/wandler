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
  (when-not (has? "Map.isSome_lookup_insert")
    (try
      (eval '(ansatz.core/theorem Map.isSome_lookup_insert
               [K :- Type, V :- Type, dec :- (DecidableEq K), k :- K, k' :- K, v :- V, m :- (Map K V)]
               (= Bool (Option.isSome V (Map.lookup K V dec k (Map.insert K V dec k' v m)))
                       (Bool.or (BEq.beq K (instBEqOfDecidableEq K dec) k k') (Option.isSome V (Map.lookup K V dec k m))))
               (rewrite Map.lookup_insert)
               (split)
               (all_goals (simp_all [cond cond_true cond_false Option.isSome Bool.true_or Bool.false_or Bool.or_true Bool.or_false]))))
      (catch Throwable _ nil)))

  ;; lookup_group_by_gen: the accumulator-generalized presence invariant —
  ;;   isSome (lookup k (foldl gbStepId m xs)) = (k ∈ xs) ∨ isSome (lookup k m).
  ;; `induction xs generalizing m` (the quantified IH auto-applies at the recursive accumulator via
  ;; simp_all), `unfold Map.gbStepId` exposes the insert so `rewrite Map.isSome_lookup_insert` fires
  ;; across the Subtype boundary, then `by_cases (k == head)` resolves the elem-cons matcher and the
  ;; Bool.or rearrangement closes.
  (when-not (has? "Map.lookup_group_by_gen")
    (try
      (eval '(ansatz.core/theorem Map.lookup_group_by_gen
               [K :- Type, dec :- (DecidableEq K), k :- K, xs :- (List K), m :- (Map K (List K))]
               (= Bool
                  (Option.isSome (List K) (Map.lookup K (List K) dec k (List.foldl (Map K (List K)) K (Map.gbStepId K dec) m xs)))
                  (Bool.or (List.elem K (instBEqOfDecidableEq K dec) k xs) (Option.isSome (List K) (Map.lookup K (List K) dec k m))))
               (induction xs generalizing m)
               (all_goals (simp_all [List.foldl_nil List.foldl_cons]))
               (all_goals (try (unfold Map.gbStepId)))
               (all_goals (try (rewrite Map.isSome_lookup_insert)))
               (all_goals (try (by_cases (BEq.beq K (instBEqOfDecidableEq K dec) k head))))
               (all_goals (try (simp_all [List.elem_cons List.elem_nil Bool.or_assoc Bool.or_comm Bool.false_or Bool.or_false Bool.true_or Bool.or_true beq_iff_eq beq_self_eq_true cond cond_true cond_false])))))
      (catch Throwable _ nil)))

  ;; lookup_group_by: closed form at `Map.group_by id` (what the semijoin consumes). From the gen at
  ;; m := empty; the `isSome (lookup k empty)` disjunct collapses by `Bool.or_false` (def-eq to false).
  (when-not (has? "Map.lookup_group_by")
    (try
      (eval '(ansatz.core/theorem Map.lookup_group_by
               [K :- Type, dec :- (DecidableEq K), k :- K, xs :- (List K)]
               (= Bool (Option.isSome (List K) (Map.lookup K (List K) dec k (Map.group_by K K dec (fn [x :- K] x) xs)))
                       (List.elem K (instBEqOfDecidableEq K dec) k xs))
               (rewrite (Map.lookup_group_by_gen K dec k xs (Map.empty K (List K))))
               (exact (Bool.or_false (List.elem K (instBEqOfDecidableEq K dec) k xs)))))
      (catch Throwable _ nil)))

  ;; semijoin: a membership filter equals the index-probe filter — `filter (x ∈ ys) xs =
  ;; filter (isSome (lookup x (group_by id ys))) xs`. Induction on xs; per element the predicates agree
  ;; by `lookup_group_by` (explicit-args rewrite of the ite condition), tails by the IH.
  (when-not (has? "List.elem_filter_eq_index_probe")
    (try
      (eval '(ansatz.core/theorem List.elem_filter_eq_index_probe
               [K :- Type, dec :- (DecidableEq K), xs :- (List K), ys :- (List K)]
               (= (List K)
                  (List.filter K (fn [x :- K] (List.elem K (instBEqOfDecidableEq K dec) x ys)) xs)
                  (List.filter K (fn [x :- K] (Option.isSome (List K) (Map.lookup K (List K) dec x (Map.group_by K K dec (fn [x :- K] x) ys)))) xs))
               (induction xs)
               (all_goals (simp_all [List.filter_nil List.filter_cons]))
               (all_goals (try (rewrite (Map.lookup_group_by K dec head ys))))
               (all_goals (try (rfl)))
               (all_goals (try (simp_all [List.filter_nil List.filter_cons])))))
      (catch Throwable _ nil)))

  ;; anti-join: the negated semijoin — `filter (x ∉ ys) xs = filter (¬isSome (lookup x …)) xs`.
  (when-not (has? "List.elem_not_filter_eq_index_probe")
    (try
      (eval '(ansatz.core/theorem List.elem_not_filter_eq_index_probe
               [K :- Type, dec :- (DecidableEq K), xs :- (List K), ys :- (List K)]
               (= (List K)
                  (List.filter K (fn [x :- K] (Bool.not (List.elem K (instBEqOfDecidableEq K dec) x ys))) xs)
                  (List.filter K (fn [x :- K] (Bool.not (Option.isSome (List K) (Map.lookup K (List K) dec x (Map.group_by K K dec (fn [x :- K] x) ys))))) xs))
               (induction xs)
               (all_goals (simp_all [List.filter_nil List.filter_cons]))
               (all_goals (try (rewrite (Map.lookup_group_by K dec head ys))))
               (all_goals (try (rfl)))
               (all_goals (try (simp_all [List.filter_nil List.filter_cons])))))
      (catch Throwable _ nil)))
  :installed)
