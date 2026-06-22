(ns wandler.clean.laws.groupby
  "Path 2b — GROUP-BY ELIMINATION under a unique key. When the grouping key `kf` is unique across the
   relation (`Nodup (map kf xs)` — the declared `{:unique-key}`/`:set` fact), every group-by bucket is
   a SINGLETON, so a query that denormalizes each row with its own group collapses to a plain map over
   the rows — the group_by + per-row lookups vanish. UNSOUND without the key (duplicate keys make a
   bucket longer than one row), so only a proof — never a stats planner — licenses it.

   The capability is composed from the bucket foundation (`Map.bucket_content`, bucket = a key-filter)
   and the singleton-bucket primitive (`bucket_singleton`, in wandler.clean.laws.uniqueness):

     Map.bucket_singleton_lookup : Nodup (map kf l) → r ∈ l →
                                     getD (lookup (kf r) (group_by kf l)) [] = [r]

   The bucket reversal that forces sum-level reasoning for `Map.join` is a NO-OP on a one-element
   bucket, so there is no Perm/commutativity obstacle here. Lifting the per-row identity under the
   row-map (each `r ∈ xs` discharges the membership) gives the removal law:

     Map.groupby_self_elim : Nodup (map kf xs) →
                               map (fun r => getD (lookup (kf r) (group_by kf xs)) []) xs
                             = map (fun r => [r]) xs

   The lift uses `List.map_congr_left` via the explicit-argument wrapper `List.map_congr_left_expl`
   (f/g/l explicit, so the per-element proof elaborates against a concrete equality — no implicit
   higher-order pinning)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [wandler.clean.laws.bucket :as bucket]
            [wandler.clean.laws.uniqueness :as uniqueness]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))
(defn installed? []
  (and (has? "List.map_congr_left_expl")
       (has? "Map.bucket_singleton_lookup")
       (has? "Map.groupby_self_elim")))

(defn install!
  "Install the group-by-elimination laws (idempotent). Builds on `bucket/install!` (Map.bucket_content)
   and `uniqueness/install!` (bucket_singleton). Returns :installed."
  []
  (bucket/install!)
  (uniqueness/install!)
  ;; explicit-argument map_congr_left: ∀a∈l, f a = g a ⊢ map f l = map g l (f/g/l explicit so a
  ;; per-element proof checks against a concrete equality — see ns docstring).
  (a/deftheorem List.map_congr_left_expl
    [A :- Type, B :- Type, f :- (=> A B), g :- (=> A B), l :- (List A),
     h :- (forall [a A] (=> (Membership.mem A (List A) (List.instMembership A) l a) (= B (f a) (g a))))]
    (= (List B) (List.map A B f l) (List.map A B g l))
    (exact (List.map_congr_left h)))
  ;; a unique-key bucket lookup returns the singleton (bucket_content ∘ bucket_singleton; the
  ;; foldl(::)[] reversal is a no-op on [r], so it closes by rfl after the two rewrites).
  (a/deftheorem Map.bucket_singleton_lookup
    [K :- Type, X :- Type, dec :- (DecidableEq K) :inst,
     linst :- (LawfulBEq K (instBEqOfDecidableEq K dec)) :inst,
     kf :- (=> X K), r :- X, l :- (List X)]
    (=> (List.Nodup K (List.map X K kf l))
     (=> (Membership.mem X (List X) (List.instMembership X) l r)
         (= (List X)
            (Option.getD (List X) (Map.lookup K (List X) dec (kf r) (Map.group_by K X dec kf l)) (List.nil X))
            (List.cons X r (List.nil X)))))
    (intro hn) (intro hr)
    (rw (Map.bucket_content K X dec kf (kf r) l))
    (rw (bucket_singleton K X (instBEqOfDecidableEq K dec) linst kf r l hn hr)))
  ;; THE GROUP-BY ELIMINATION law: denormalize-each-row-with-its-group collapses to map-over-rows.
  (a/deftheorem Map.groupby_self_elim
    [K :- Type, X :- Type, dec :- (DecidableEq K) :inst,
     linst :- (LawfulBEq K (instBEqOfDecidableEq K dec)) :inst,
     kf :- (=> X K), xs :- (List X)]
    (=> (List.Nodup K (List.map X K kf xs))
        (= (List (List X))
           (List.map X (List X)
             (fn [r :- X] (Option.getD (List X) (Map.lookup K (List X) dec (kf r) (Map.group_by K X dec kf xs)) (List.nil X)))
             xs)
           (List.map X (List X) (fn [r :- X] (List.cons X r (List.nil X))) xs)))
    (intro hn)
    (exact (List.map_congr_left_expl X (List X)
             (fn [r :- X] (Option.getD (List X) (Map.lookup K (List X) dec (kf r) (Map.group_by K X dec kf xs)) (List.nil X)))
             (fn [r :- X] (List.cons X r (List.nil X)))
             xs
             (fn [a :- X] (fn [ha :- (Membership.mem X (List X) (List.instMembership X) xs a)]
               (Map.bucket_singleton_lookup K X dec linst kf a xs hn ha))))))
  :installed)
