(ns wandler.clean.laws.uniqueness
  "Step 4 — the FD/UNIQUENESS capability proof. The thesis of the dependent-types-drive-the-planner
   direction is that some rewrites are SOUND ONLY GIVEN a declared key/uniqueness fact — unreachable
   by a cost/stats planner, which can only guess. This is the cleanest such member, proved Init-only
   (no Mathlib):

     nodup_eraseDups : Nodup l → eraseDups l = l       — DISTINCT-removal (drop a redundant dedup)

   It is UNSOUND without `Nodup l` (eraseDups of a list with duplicates is strictly shorter), so a
   stats planner gets it wrong; with the declared uniqueness it is a kernel-certified identity. The
   crux is the helper

     filter_bne_self_not_mem : a ∉ l → filter (·.beq a |> not) l = l

   (an `a`-free filter over a list missing `a` keeps everything), discharged by the BEq↔Eq +
   membership-contradiction recipe (cases on `b == a`, beq_iff_eq, absurd). The keystone is then
   `induction l` + eraseDups_cons (peeling `a :: eraseDups (filter (·≠a) tail)`) + the helper (the
   filter is identity since `a ∉ tail` under Nodup) + the IH.

   ── PATH 2a — KEYED distinct removal (the RELATIONAL FD, not just element-uniqueness):

     nodup_map_eraseDupsBy : Nodup (map kf xs) → eraseDupsBy (fun a b => kf a == kf b) xs = xs

   This is the FUNCTIONAL-DEPENDENCY analogue: when a KEY field `kf` is unique across the relation
   (`Nodup (map kf xs)` — the relational `{:unique-key}` fact, not whole-row dedup), `distinct-by kf`
   is the identity. UNSOUND without the key fact (two rows with equal keys would collapse), so again
   only a proof — never stats — licenses it. Same shape as Path 1 but the helper threads through the
   KEY IMAGE:

     filter_kf_not_mem : kf a ∉ map kf l → filter (fun b => decide ((kf b == kf a) = false)) l = l

   discharged via filter_eq_self + decide_eq_true_iff (strip the `decide` eraseDupsBy emits) +
   beq_eq_false_iff_ne, with the contradiction bridged by `List.mem_map_of_mem` (kf a = kf b ∧ b ∈ l
   ⇒ kf a ∈ map kf l, contradicting the hypothesis). The keystone mirrors nodup_eraseDups but uses
   eraseDupsBy_cons (whose filter is the `decide`-form, element-FIRST `kf b == kf head`) + `dsimp` to
   beta-reduce the inline comparator before the helper `rw`, and pulls `kf head ∉ map kf tail` out of
   the key-image Nodup via `nodup_cons` (def-eq through `map_cons`).

   ── PATH 2b — GROUP-BY removal foundation (the unique-key SINGLETON BUCKET):

     bucket_singleton : Nodup (map kf l) → r ∈ l → filter (fun y => kf r == kf y) l = [r]

   THE capability the investigation flagged as the missing primitive: when the key `kf` is unique
   (`Nodup (map kf l)`), every group-by bucket is a SINGLETON — grouping by a unique key is trivial,
   so an aggregate-over-groups collapses to a map-over-rows (group-by elimination / eager aggregation).
   UNSOUND without the key fact (a duplicated key makes the bucket longer than `[r]`). Proved by
   induction with two registered helpers:

     filter_key_eq_nil : k ∉ map kf l → filter (fun y => k == kf y) l = []   (absent-key bucket empty)
     key_beq_ne_true   : kf b ∉ map kf tail → a ∈ tail → ¬((kf a == kf b) = true)  (distinct-key ⇒ beq≠true)

   The keystone splits `r ∈ head::tail` (via `have`+`mem_cons`+`cases`): the r=head branch keeps head
   and empties the tail bucket (filter_key_eq_nil under the key-Nodup), the r∈tail branch drops head
   (key_beq_ne_true ⇒ filter_cons_of_neg) and recurses (IH). The remaining 2b productization is the
   group-by-aggregate optimizer STRATEGY (Map.group_by pattern recognition, Perm-aware) — a separate
   wiring task (cf. #132), riding this now-certified capability.

   The heavier FD-cluster siblings (join elimination, eager aggregation) follow the same shape — a law
   that TAKES the key fact as a hypothesis."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))
(defn installed? [] (and (has? "filter_bne_self_not_mem") (has? "nodup_eraseDups")
                         (has? "filter_kf_not_mem") (has? "nodup_map_eraseDupsBy")
                         (has? "filter_key_eq_nil") (has? "key_beq_ne_true") (has? "bucket_singleton")))

(defn install!
  "Prove + register the uniqueness capability laws into the current env (idempotent). Returns
   :installed. Init-only; needs the full Init store (eraseDups/Nodup/filter lemmas)."
  []
  ;; helper: a list missing `a` is unchanged by filtering OUT `a` (the BEq+membership lemma)
  (a/deftheorem filter_bne_self_not_mem
    [α :- Type, inst :- (BEq α) :inst, linst :- (LawfulBEq α inst) :inst, a :- α, l :- (List α)]
    (=> (Not (Membership.mem α (List α) (List.instMembership α) l a))
        (= (List α) (List.filter α (fn [b :- α] (Bool.not (BEq.beq α inst b a))) l) l))
    (intro hnm) (simp [List.filter_eq_self]) (intro b) (intro hb)
    (cases hbeq (BEq.beq α inst b a))
    (all_goals (try (simp_all [beq_iff_eq])))
    (all_goals (try (subst hbeq')))
    (all_goals (try (simp_all)))
    (all_goals (try (exact (absurd hb hnm)))))
  ;; THE CAPABILITY PROOF: eraseDups is the identity on a Nodup list (DISTINCT removal).
  (a/deftheorem nodup_eraseDups
    [α :- Type, inst :- (BEq α) :inst, linst :- (LawfulBEq α inst) :inst, l :- (List α)]
    (=> (List.Nodup α l) (= (List α) (List.eraseDups α inst l) l))
    (induction l)
    (all_goals (intro hn))
    (all_goals (try (rw (List.eraseDups_nil α inst))))
    (all_goals (try (rw (List.eraseDups_cons α inst head tail))))
    (all_goals (try (rw (filter_bne_self_not_mem α head tail
                                                 (And.left (Iff.mp (List.nodup_cons α head tail) hn))))))
    (all_goals (try (rw (ih_tail (And.right (Iff.mp (List.nodup_cons α head tail) hn))))))
    (all_goals (try (rfl))))
  ;; ── PATH 2a — KEYED distinct removal ───────────────────────────────────────────────────
  ;; helper: a list whose KEY-IMAGE misses `kf a` is unchanged by the key-eraseDupsBy filter.
  ;; The filter is the `decide`-form, element-FIRST predicate eraseDupsBy_cons actually emits.
  (a/deftheorem filter_kf_not_mem
    [K :- Type, X :- Type, inst :- (BEq K) :inst, linst :- (LawfulBEq K inst) :inst,
     kf :- (=> X K), a :- X, l :- (List X)]
    (=> (Not (Membership.mem K (List K) (List.instMembership K) (List.map X K kf l) (kf a)))
        (= (List X)
           (List.filter X
             (fn [b :- X]
               (Decidable.decide
                 (= Bool (BEq.beq K inst (kf b) (kf a)) Bool.false)
                 (instDecidableEqBool (BEq.beq K inst (kf b) (kf a)) Bool.false)))
             l)
           l))
    (intro hnm) (simp [List.filter_eq_self]) (intro b) (intro hb)
    (apply (Iff.mpr (decide_eq_true_iff
                      (= Bool (BEq.beq K inst (kf b) (kf a)) Bool.false)
                      (instDecidableEqBool (BEq.beq K inst (kf b) (kf a)) Bool.false))))
    (apply (Iff.mpr (beq_eq_false_iff_ne K inst linst (kf b) (kf a))))
    (intro he) (apply hnm) (rw (Eq.symm he))
    (exact (List.mem_map_of_mem X K l b kf hb)))
  ;; THE KEYED CAPABILITY PROOF: distinct-by-key is the identity when the key is unique
  ;; (Nodup over the key image) — the relational FUNCTIONAL DEPENDENCY analogue of nodup_eraseDups.
  (a/deftheorem nodup_map_eraseDupsBy
    [K :- Type, X :- Type, inst :- (BEq K) :inst, linst :- (LawfulBEq K inst) :inst,
     kf :- (=> X K), xs :- (List X)]
    (=> (List.Nodup K (List.map X K kf xs))
        (= (List X)
           (List.eraseDupsBy X (fn [x :- X] (fn [y :- X] (BEq.beq K inst (kf x) (kf y)))) xs)
           xs))
    (induction xs)
    (all_goals (intro hn))
    (all_goals (try (rw (List.eraseDupsBy_nil X (fn [x :- X] (fn [y :- X] (BEq.beq K inst (kf x) (kf y))))))))
    (all_goals (try (rw (List.eraseDupsBy_cons X head tail (fn [x :- X] (fn [y :- X] (BEq.beq K inst (kf x) (kf y))))))))
    (all_goals (try (dsimp)))
    (all_goals (try (rw (filter_kf_not_mem K X inst linst kf head tail
                          (And.left (Iff.mp (List.nodup_cons K (kf head) (List.map X K kf tail)) hn))))))
    (all_goals (try (rw (ih_tail (And.right (Iff.mp (List.nodup_cons K (kf head) (List.map X K kf tail)) hn))))))
    (all_goals (try (rfl))))
  ;; ── PATH 2b — GROUP-BY removal foundation: the unique-key SINGLETON BUCKET ──────────────
  ;; helper: a bucket keyed on an ABSENT key is empty.
  (a/deftheorem filter_key_eq_nil
    [K :- Type, X :- Type, inst :- (BEq K) :inst, linst :- (LawfulBEq K inst) :inst,
     kf :- (=> X K), k :- K, l :- (List X)]
    (=> (Not (Membership.mem K (List K) (List.instMembership K) (List.map X K kf l) k))
        (= (List X) (List.filter X (fn [y :- X] (BEq.beq K inst k (kf y))) l) (List.nil X)))
    (intro hnm)
    (apply (Iff.mpr (List.filter_eq_nil_iff X (fn [y :- X] (BEq.beq K inst k (kf y))) l)))
    (intro y) (intro hy) (intro he)
    (apply hnm)
    (rw (Iff.mp (beq_iff_eq K inst linst k (kf y)) he))
    (exact (List.mem_map_of_mem X K l y kf hy)))
  ;; helper: under a unique key, a tail element's key ≠ the head's key, so its beq is not true.
  (a/deftheorem key_beq_ne_true
    [K :- Type, X :- Type, inst :- (BEq K) :inst, linst :- (LawfulBEq K inst) :inst,
     kf :- (=> X K), a :- X, b :- X, tail :- (List X)]
    (=> (Not (Membership.mem K (List K) (List.instMembership K) (List.map X K kf tail) (kf b)))
     (=> (Membership.mem X (List X) (List.instMembership X) tail a)
         (Not (= Bool (BEq.beq K inst (kf a) (kf b)) Bool.true))))
    (intro hnm) (intro hrt) (intro ht)
    (apply hnm)
    (rw (Eq.symm (Iff.mp (beq_iff_eq K inst linst (kf a) (kf b)) ht)))
    (exact (List.mem_map_of_mem X K tail a kf hrt)))
  ;; THE 2b KEYSTONE: a unique-key bucket is a singleton (group-by-by-unique-key is trivial).
  (a/deftheorem bucket_singleton
    [K :- Type, X :- Type, inst :- (BEq K) :inst, linst :- (LawfulBEq K inst) :inst,
     kf :- (=> X K), r :- X, l :- (List X)]
    (=> (List.Nodup K (List.map X K kf l))
     (=> (Membership.mem X (List X) (List.instMembership X) l r)
         (= (List X) (List.filter X (fn [y :- X] (BEq.beq K inst (kf r) (kf y))) l)
            (List.cons X r (List.nil X)))))
    (induction l)
    (all_goals (intro hn))
    (all_goals (intro hr))
    ;; inline-proof `have` (ansatz have-with-proof): introduce + discharge the Or in one step.
    (all_goals (try (have hor (Or (= X r head) (Membership.mem X (List X) (List.instMembership X) tail r))
                      (Iff.mp (List.mem_cons X head tail r) hr))))
    (all_goals (try (cases hor)))
    (all_goals (try (subst h)))
    (all_goals (try (rw (List.filter_cons_of_pos X (fn [y :- X] (BEq.beq K inst (kf head) (kf y))) head tail
                         (beq_self_eq_true K inst (LawfulBEq.toReflBEq K inst linst) (kf head))))))
    (all_goals (try (rw (filter_key_eq_nil K X inst linst kf (kf head) tail
                         (And.left (Iff.mp (List.nodup_cons K (kf head) (List.map X K kf tail)) hn))))))
    (all_goals (try (rw (List.filter_cons_of_neg X (fn [y :- X] (BEq.beq K inst (kf r) (kf y))) head tail
                         (key_beq_ne_true K X inst linst kf r head tail
                           (And.left (Iff.mp (List.nodup_cons K (kf head) (List.map X K kf tail)) hn)) h)))))
    (all_goals (try (rw (ih_tail (And.right (Iff.mp (List.nodup_cons K (kf head) (List.map X K kf tail)) hn)) h))))
    (all_goals (try (rfl)))
    (all_goals (try (exfalso)))
    (all_goals (try (exact ((List.not_mem_nil X r) hr)))))
  :installed)
