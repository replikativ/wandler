(ns wandler.clean.laws.frame
  "The relational FAQ/frame laws of the CLEAN wandler core — the aggregate-level join algebra, proved
   ENTIRELY at the sum level with NO `List.Perm` (the thesis of the clean reimpl: the materialized
   join-list is not load-bearing for the planner, so join commutativity is a Fubini fact about sums,
   not a bag-permutation). Mirrors lean-wandler's `Wandler/Laws/Frame.lean`.

   This is the first namespace of the clean tree (`wandler.clean.*`, strangler over the old wandler
   oracle). It sits ON TOP of `ansatz.prelude.list` — the domain-agnostic Batteries-tier big-operator
   prelude (`wsum` over a `WAddMonoid`, `wsum_map_*`, the Fubini `wsum_map_sum_comm`, and the
   filter→guard bridge `sum_filter_map`). Those generic lemmas stay in ansatz; the JOIN vocabulary
   (`aggJoin_*`) is relational and lives here.

   ─ The two laws (each kernel `check-constant`-verified by `install!`) ─────────────────────────────
     aggJoin_split    — THE FAQ FACTORIZATION (O(|xs|·|ys|) → O(|xs|+|ys|) via a pre-aggregated index):
                        the aggregate of a join is the per-left-row sum over that row's matching bucket.
                        Join inlined as `flatMap x → map (x,·) (filter (p x) ys)`, aggregated by an
                        abstract `f : X→Y→S`. PURE SIMP (map_flatMap → map_map → wsum_flatten → comp);
                        no induction, no case-split. The core planner win.
     aggJoin_reorder  — THE JOIN-COMMUTATIVITY CAPSTONE: the aggregate of an equi-join is invariant
                        under swapping the two inputs (so the planner may build the index on whichever
                        side is smaller). Recipe: factor BOTH join orders (`aggJoin_split`), turn each
                        filter into a guard (`sum_filter_map`), swap the two summation orders by Fubini
                        (`wsum_map_sum_comm`). The swapped predicate `(fun y x => p x y)` makes the two
                        guarded double-sums literally identical — no `eq_comm` needed in the
                        abstract-predicate form. This is the verified Fubini that RETIRES List.Perm.

   `p : X→Y→Bool` is an abstract match predicate (the kf/lf/DecidableEq equi-join is a later
   specialization). `install!` installs the ansatz prelude first, then proves + registers both.
   Requires the full Init store. Companion: ansatz/docs/WANDLER_REIMPL_PLAN.md (the aggregate-level
   refinement)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.prelude.list :as plist]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn installed? [] (and (has? "aggJoin_split") (has? "aggJoin_reorder")))

(defn install!
  "Install the ansatz big-operator prelude, then prove + register `aggJoin_split` and
   `aggJoin_reorder` into the current env (idempotent). Returns :installed."
  []
  (plist/install!)
  ;; aggJoin_split — the FAQ factorization. Pure simp: unfold the inlined join (map over a flatMap of
  ;; a filtered map), fuse the maps, push the sum through flatten, reduce the composition. No List.Perm.
  (a/deftheorem aggJoin_split
    [X :- Type, Y :- Type, S :- Type, m :- (WAddMonoid S) :inst,
     p :- (=> X (=> Y Bool)), f :- (=> X (=> Y S)), xs :- (List X), ys :- (List Y)]
    (= S
       (wsum (List.map (fn [pr :- (Prod X Y)] (f (Prod.fst pr) (Prod.snd pr)))
               (List.flatMap
                 (fn [x :- X] (List.map (fn [y :- Y] (Prod.mk x y))
                               (List.filter (p x) ys))) xs)))
       (wsum (List.map (fn [x :- X]
               (wsum (List.map (fn [y :- Y] (f x y))
                       (List.filter (p x) ys)))) xs)))
    (simp [List.map_flatMap List.map_map wsum_flatten Function.comp_def]))
  ;; aggJoin_factor — THE FAQ FRAME RULE for a separable weight `w x * v y` (lean-wandler Laws/Frame.lean
  ;; `aggJoin_factor`): the right factor `v` is summed ONCE per matching bucket, not once per pair, so an
  ;; O(|xs|·|ys|) aggregate becomes O(|xs|+|ys|) with a pre-aggregated index. This REPLACES old wandler's
  ;; Map-based `Map.foldl_join_sum_factor`/`Map.foldl_join_frame` cluster (~400 LOC of explicit
  ;; congrArg/Eq.trans term-building) with a THIN proof over the prelude: factor the join
  ;; (`aggJoin_split` with the separable f) then pull the loop-invariant `w x` out of each inner sum
  ;; (`wsum_map_mul_left`). Carrier-generic over any WSemiring (the multiplication lives there).
  (a/deftheorem aggJoin_factor
    [X :- Type, Y :- Type, S :- Type, m :- (WSemiring S) :inst,
     p :- (=> X (=> Y Bool)), w :- (=> X S), v :- (=> Y S), xs :- (List X), ys :- (List Y)]
    (= S
       (wsum
         (List.map
           (fn [pr :- (Prod X Y)] (WSemiring.mul m (w (Prod.fst pr)) (v (Prod.snd pr))))
           (List.flatMap
             (fn [x :- X] (List.map (fn [y :- Y] (Prod.mk x y))
                           (List.filter (p x) ys))) xs)))
       (wsum
         (List.map (fn [x :- X]
           (WSemiring.mul m (w x)
             (wsum (List.map v (List.filter (p x) ys))))) xs)))
    (rw (aggJoin_split X Y S p
          (fn [x :- X] (fn [y :- Y] (WSemiring.mul m (w x) (v y)))) xs ys))
    (simp [wsum_map_mul_left]))
  ;; aggJoin_reorder — the join-commutativity capstone. Factor both orders, filter→guard, Fubini.
  (a/deftheorem aggJoin_reorder
    [X :- Type, Y :- Type, S :- Type, m :- (WAddMonoid S) :inst,
     hc :- (Std.Commutative S (WAddMonoid.add m)),
     p :- (=> X (=> Y Bool)), f :- (=> X (=> Y S)),
     xs :- (List X), ys :- (List Y)]
    (= S
       (wsum (List.map (fn [pr :- (Prod X Y)] (f (Prod.fst pr) (Prod.snd pr)))
               (List.flatMap
                 (fn [x :- X] (List.map (fn [y :- Y] (Prod.mk x y))
                               (List.filter (p x) ys))) xs)))
       (wsum (List.map (fn [pr :- (Prod Y X)] (f (Prod.snd pr) (Prod.fst pr)))
               (List.flatMap
                 (fn [y :- Y] (List.map (fn [x :- X] (Prod.mk y x))
                               (List.filter (fn [x :- X] (p x y)) xs))) ys))))
    (rw (aggJoin_split X Y S p f xs ys))
    (rw (aggJoin_split Y X S (fn [y :- Y] (fn [x :- X] (p x y)))
                      (fn [y :- Y] (fn [x :- X] (f x y))) ys xs))
    (simp [sum_filter_map])
    (rw (wsum_map_sum_comm X Y S hc
          (fn [x :- X] (fn [y :- Y] (if (p x y) (f x y) (WAddMonoid.zero m)))) xs ys)))
  :installed)
