(ns wandler.clean.laws.bucket
  "The group_by-bucket foundation of the CLEAN wandler core — the bridge from a REAL `Map.join`
   (whose buckets are built by `Map.group_by` = a foldl of `Map.insert`) down to the keyed
   `filter`-of-rows form that the aggregate frame laws (`wandler.clean.laws.frame`) reason about.

   Map = `{ l : List (K×V) // NodupKeys l }` (a Subtype); `Map.lookup`/`insert`/`group_by` are
   `:opaque`-hint defs over `.val`. The whole cluster used to be ~1500 LOC of hand-built
   congrArg/Eq.trans terms (old `wandler.laws.proofs` §3 + `relational`); here it is three thin
   surface proofs riding the assoc-list lemmas in `ansatz.prelude.list`
   (`List.lookup_filter_ne`, `List.lookup_insert`):

     Map.lookup_insert       — `lookup k (insert k' v m) = bif (k==k') (some v) (lookup k m)`.
                               One-line `exact (List.lookup_insert … m.val)`: the goal is DEF-EQ to the
                               List lemma at the underlying AList (the opaque Map ops unfold during
                               `is-def-eq`, which `exact` uses — opacity blocks simp's delta, not the
                               kernel's conversion check).
     Map.bucket_content_gen  — the foldl-of-inserts INVARIANT, generalized over the accumulator map:
                               `getD (lookup k (foldl gbStep m ys)) = foldl(::) (getD (lookup k m))
                               (filter (k == f ·) ys)` where `gbStep m x = insert (f x) (x :: bucket) m`.
                               `induction ys generalizing m` (the accumulator must vary in the IH;
                               simp_all auto-applies the quantified IH at the stepped map) + `by_cases`
                               on `k == f head` + `Map.lookup_insert` + simp_all⇄dsimp to fixpoint.
     Map.bucket_content      — the closed form at the empty map: `getD (lookup k (group_by f ys)) =
                               foldl(::) [] (filter (k == f ·) ys)`. `exact` of `bucket_content_gen` at
                               `m := Map.empty` — `group_by ≡ foldl gbStep empty` and
                               `getD (lookup k empty) ≡ []` are both def-eq.

   `foldl (λacc x. x::acc)` = the bucket in REVERSE of the matched rows (an `Map.insert` prepends), so
   downstream the order is washed out at the aggregate level by `wsum_reverse`+`foldl_cons_acc` (prelude).
   Requires the full Init store + `wandler.kmap/install!`. Companion: ansatz/docs/WANDLER_REIMPL_PLAN.md."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.prelude.list :as plist]
            [wandler.clean.laws.frame :as frame]
            [wandler.kmap :as kmap]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(def ^:private bucket-lem
  '[List.foldl_nil List.foldl_cons List.filter_nil List.filter_cons_of_pos List.filter_cons_of_neg
    Map.lookup_insert cond_true cond_false beq_iff_eq beq_self_eq_true beq_eq_false_iff_ne Option.getD])

(defn install!
  "Install kmap + the ansatz prelude, then prove + register the three bucket-foundation lemmas
   (idempotent). Returns :installed."
  []
  (kmap/install!)
  (plist/install!)
  (frame/install!)
  ;; Map.lookup_insert — def-eq to List.lookup_insert at m.val (opaque Map ops unfold in is-def-eq).
  (when-not (has? "Map.lookup_insert")
    (try
      (eval '(ansatz.core/theorem Map.lookup_insert
               [α :- Type, β :- Type, dec :- (DecidableEq α), k :- α, k' :- α, v :- β, m :- (Map α β)]
               (= (Option β)
                  (Map.lookup α β dec k (Map.insert α β dec k' v m))
                  (bif (BEq.beq α (instBEqOfDecidableEq α dec) k k')
                       (Option.some β v) (Map.lookup α β dec k m)))
               (exact (List.lookup_insert α β dec k k' v
                        (Subtype.val (List (Prod α β)) (Map.NodupKeys α β) m)))))
      (catch Throwable _ nil)))
  ;; Map.bucket_content_gen — the foldl-of-inserts invariant, accumulator-generalized.
  (when-not (has? "Map.bucket_content_gen")
    (try
      (eval (concat
              '(ansatz.core/theorem Map.bucket_content_gen
                 [α :- Type, β :- Type, dec :- (DecidableEq α), f :- (=> β α), k :- α,
                  ys :- (List β), m :- (Map α (List β))]
                 (= (List β)
                    (Option.getD (List β)
                      (Map.lookup α (List β) dec k
                        (List.foldl (Map α (List β)) β
                          (fn [mm :- (Map α (List β)) x :- β]
                            (Map.insert α (List β) dec (f x)
                              (List.cons β x (Option.getD (List β) (Map.lookup α (List β) dec (f x) mm) (List.nil β))) mm))
                          m ys))
                      (List.nil β))
                    (List.foldl (List β) β (fn [acc :- (List β) x :- β] (List.cons β x acc))
                      (Option.getD (List β) (Map.lookup α (List β) dec k m) (List.nil β))
                      (List.filter β (fn [x :- β] (BEq.beq α (instBEqOfDecidableEq α dec) k (f x))) ys)))
                 (induction ys generalizing m)
                 (all_goals (try (simp_all [List.foldl_nil List.filter_nil Option.getD])))
                 (all_goals (try (by_cases (BEq.beq α (instBEqOfDecidableEq α dec) k (f head))))))
              (mapcat (fn [_] (list (list 'all_goals (list 'try (list 'simp_all bucket-lem)))
                                    '(all_goals (try (dsimp)))))
                      (range 4))
              (list (list 'all_goals (list 'try (list 'simp_all bucket-lem))))))
      (catch Throwable _ nil)))
  ;; Map.bucket_content — closed form at empty: bucket_content_gen specialized (all def-eq).
  (when-not (has? "Map.bucket_content")
    (try
      (eval '(ansatz.core/theorem Map.bucket_content
               [α :- Type, β :- Type, dec :- (DecidableEq α), f :- (=> β α), k :- α, ys :- (List β)]
               (= (List β)
                  (Option.getD (List β) (Map.lookup α (List β) dec k (Map.group_by α β dec f ys)) (List.nil β))
                  (List.foldl (List β) β (fn [acc :- (List β) x :- β] (List.cons β x acc))
                    (List.nil β)
                    (List.filter β (fn [x :- β] (BEq.beq α (instBEqOfDecidableEq α dec) k (f x))) ys)))
               (exact (Map.bucket_content_gen α β dec f k ys (Map.empty α (List β))))))
      (catch Throwable _ nil)))
  ;; Map.join_eq — the rfl-unfolding of the opaque `Map.join` to its flatMap-of-grouped-buckets body.
  ;; Lets simp/rw expose the bucket so `Map.bucket_content` can rewrite it.
  (when-not (has? "Map.join_eq")
    (try
      (eval '(ansatz.core/theorem Map.join_eq
               [K :- Type, X :- Type, Y :- Type, d :- (DecidableEq K), kf :- (=> X K), lf :- (=> Y K),
                xs :- (List X), ys :- (List Y)]
               (= (List (Prod X Y))
                  (Map.join K X Y d kf lf xs ys)
                  (List.flatMap X (Prod X Y)
                    (fn [x :- X]
                      (List.map Y (Prod X Y) (fn [y :- Y] (Prod.mk X Y x y))
                        (Option.getD (List Y) (Map.lookup K (List Y) d (kf x) (Map.group_by K Y d lf ys)) (List.nil Y))))
                    xs))
               (rfl)))
      (catch Throwable _ nil)))
  ;; wsum_map_Map_join — THE AGGREGATE BRIDGE: the sum of an abstract weight `h` over a REAL `Map.join`
  ;; equals the same sum over the clean `filter`-`flatMap` join form (`aggJoin_split`'s input). The two
  ;; lists differ per-bucket by the group_by reversal (`Map.bucket_content` = foldl(::)[] = reverse), so
  ;; the equality holds only at the SUM level over a COMMUTATIVE monoid. Proof: `rw Map.join_eq` exposes
  ;; the grouped bucket; `induction xs` splits the flatMap; each cons head reduces (map_append/wsum_append/
  ;; map_map) to exactly `wsum_map_foldl_cons` on its bucket, the tail to the IH. This is what lets the
  ;; aggregate frame laws (`aggJoin_split`/`aggJoin_factor`) apply to a real group_by Map.join.
  (when-not (has? "wsum_map_Map_join")
    (try
      (eval '(ansatz.core/theorem wsum_map_Map_join
               [K :- Type, X :- Type, Y :- Type, S :- Type, d :- (DecidableEq K),
                m :- (WAddMonoid S), hc :- (Std.Commutative S (WAddMonoid.add m)),
                kf :- (=> X K), lf :- (=> Y K), h :- (=> (Prod X Y) S), xs :- (List X), ys :- (List Y)]
               (= S
                  (wsum m (List.map (Prod X Y) S h (Map.join K X Y d kf lf xs ys)))
                  (wsum m (List.map (Prod X Y) S h
                            (List.flatMap X (Prod X Y)
                              (fn [x :- X] (List.map Y (Prod X Y) (fn [y :- Y] (Prod.mk X Y x y))
                                            (List.filter Y (fn [y :- Y] (BEq.beq K (instBEqOfDecidableEq K d) (kf x) (lf y))) ys))) xs))))
               (rw (Map.join_eq K X Y d kf lf xs ys))
               (induction xs)
               (all_goals (simp_all [List.flatMap_nil List.flatMap_cons List.map_append List.map_nil
                                     wsum_append wsum.eq_1 wsum.eq_2 List.map_map Function.comp_def
                                     Map.bucket_content wsum_map_foldl_cons (WAddMonoid.zero_add m)]))))
      (catch Throwable _ nil)))
  ;; Map_aggJoin_factor — THE PLANNER-FACING KEYED FACTOR LAW (replaces term-built
  ;; Map.foldl_join_sum_factor). For a separable weight `w x * v y`, the aggregate over a REAL group_by
  ;; `Map.join` factors so the right factor `v` is summed ONCE per matching bucket — the O(|xs|·|ys|) →
  ;; O(|xs|+|ys|) FAQ win, via a pre-aggregated index. TWO rewrites: the aggregate bridge
  ;; `wsum_map_Map_join` (real join → clean filter-flatMap form) then the clean `aggJoin_factor`
  ;; (frame). Carrier-generic over any commutative WSemiring.
  (when-not (has? "Map_aggJoin_factor")
    (try
      (eval '(ansatz.core/theorem Map_aggJoin_factor
               [K :- Type, X :- Type, Y :- Type, S :- Type, dec :- (DecidableEq K), m :- (WSemiring S),
                hc :- (Std.Commutative S (WAddMonoid.add (WSemiring.toWAddMonoid m))),
                kf :- (=> X K), lf :- (=> Y K), w :- (=> X S), v :- (=> Y S), xs :- (List X), ys :- (List Y)]
               (= S
                  (wsum (WSemiring.toWAddMonoid m)
                    (List.map (Prod X Y) S
                      (fn [pr :- (Prod X Y)] (WSemiring.mul m (w (Prod.fst X Y pr)) (v (Prod.snd X Y pr))))
                      (Map.join K X Y dec kf lf xs ys)))
                  (wsum (WSemiring.toWAddMonoid m)
                    (List.map X S (fn [x :- X]
                      (WSemiring.mul m (w x)
                        (wsum (WSemiring.toWAddMonoid m)
                          (List.map Y S v (List.filter Y (fn [y :- Y] (BEq.beq K (instBEqOfDecidableEq K dec) (kf x) (lf y))) ys))))) xs)))
               (rw (wsum_map_Map_join K X Y S dec (WSemiring.toWAddMonoid m) hc kf lf
                     (fn [pr :- (Prod X Y)] (WSemiring.mul m (w (Prod.fst X Y pr)) (v (Prod.snd X Y pr)))) xs ys))
               (rw (aggJoin_factor X Y S m
                     (fn [x :- X] (fn [y :- Y] (BEq.beq K (instBEqOfDecidableEq K dec) (kf x) (lf y)))) w v xs ys))))
      (catch Throwable _ nil)))
  ;; Map_aggJoin_reorder — THE JOIN-COMMUTATIVITY / DRIVE-DIRECTION law over a real Map.join: the
  ;; aggregate of an equi-join is invariant under swapping the two inputs, so the planner may build the
  ;; group_by index on whichever side is smaller. `f : X→Y→S` the per-pair weight. FOUR rewrites:
  ;; bridge LHS to the clean form (`wsum_map_Map_join`), the clean `aggJoin_reorder` (Fubini, NO Perm),
  ;; bridge the swapped Map.join BACK, then `simp [beq_comm]` reconciles the key predicate `kf x == lf y`
  ;; with the swapped-drive `lf y == kf x`. Retires the old `Map.join_length_comm`/Perm reorder cluster.
  (when-not (has? "Map_aggJoin_reorder")
    (try
      (eval '(ansatz.core/theorem Map_aggJoin_reorder
               [K :- Type, X :- Type, Y :- Type, S :- Type, dec :- (DecidableEq K),
                m :- (WAddMonoid S), hc :- (Std.Commutative S (WAddMonoid.add m)),
                kf :- (=> X K), lf :- (=> Y K), f :- (=> X (=> Y S)), xs :- (List X), ys :- (List Y)]
               (= S
                  (wsum m (List.map (Prod X Y) S (fn [pr :- (Prod X Y)] (f (Prod.fst X Y pr) (Prod.snd X Y pr)))
                            (Map.join K X Y dec kf lf xs ys)))
                  (wsum m (List.map (Prod Y X) S (fn [pr :- (Prod Y X)] (f (Prod.snd Y X pr) (Prod.fst Y X pr)))
                            (Map.join K Y X dec lf kf ys xs))))
               (rw (wsum_map_Map_join K X Y S dec m hc kf lf
                     (fn [pr :- (Prod X Y)] (f (Prod.fst X Y pr) (Prod.snd X Y pr))) xs ys))
               (rw (aggJoin_reorder X Y S m hc
                     (fn [x :- X] (fn [y :- Y] (BEq.beq K (instBEqOfDecidableEq K dec) (kf x) (lf y)))) f xs ys))
               (rw (wsum_map_Map_join K Y X S dec m hc lf kf
                     (fn [pr :- (Prod Y X)] (f (Prod.snd Y X pr) (Prod.fst Y X pr))) ys xs))
               ;; goal-only simp (not simp_all) — the predicate reconciliation needs only the goal, and
               ;; the lighter pass installs reliably under full-suite memory pressure.
               (simp [beq_comm])))
      (catch Throwable _ nil)))
  :installed)
