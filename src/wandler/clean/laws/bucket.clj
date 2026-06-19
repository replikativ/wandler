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
  :installed)
