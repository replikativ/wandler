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

   The heavier FD-cluster siblings (join elimination, GROUP-BY removal, eager aggregation via #132
   bucket_key_subst) follow the same shape — a law that TAKES the key fact as a hypothesis."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))
(defn installed? [] (and (has? "filter_bne_self_not_mem") (has? "nodup_eraseDups")))

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
  :installed)
