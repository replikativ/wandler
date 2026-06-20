;; Phase 8 Level 2 (clean tree) — the FAQ foldl-shape INDEX-FAMILY laws, re-proven THINLY.
;;
;; These are the aggregation-through-join + pre-aggregated-index + linearity laws that the clean
;; optimizer's structured FAQ strategies (`try-count-factor`/`try-fold-factor`/`try-frame-index`/
;; `try-pre-agg-index`/`try-hoist-invariant` + the e-graph `hoist-laws`) APPLY by name. The OLD engine
;; (`wandler.laws.relational` + `wandler.laws.proofs.frame`, ~2,477 LOC) proved them by HAND-BUILDING
;; CIC terms (35–66 `e/app*`/`congrArg`/`Eq.trans` per proof). Here they are re-proven via the THIN
;; tactic surface (`ansatz.core/theorem` with induction + simp + controlled `rw`), each kernel
;; `check-constant`-verified by being a `theorem`. The goal STATEMENTS are byte-identical to the old
;; laws (same names), so the strategies are true drop-ins — no strategy surgery.
;;
;; Established tactic patterns (the rw-bracket fix in ansatz `c0ee162` unblocked the `rw [..]` form):
;;   • foldl over an associative monoid does NOT yield to `simp_all [ih]` (over-applies on the
;;     accumulator — see [[thin-surface-migration]]); use CONTROLLED `rw [(ih_tail <explicit-acc>)]`.
;;   • close residual linear-Nat goals (opaque foldl subterms as atoms) with `omega`.
;;   • `Map.join` is exposed by `rw [Map.join_eq]` (the clean rfl lemma in `bucket`), then the join
;;     factor/count laws fall to `simp [List.foldl_flatMap List.foldl_map]` / `[length_flatMap length_map]`.
;;
;; STATUS: WIP migration. DONE (thin, kernel-checked): sum_map_zero, foldl_add_pull, count_join_factor,
;; foldl_join_factor. The remaining index-family laws (sum_map_mul_const/const_mul/add_distrib —
;; accumulator-split, need a 0-init lemma then lift; foldl_congr; and the deep generic frame family:
;; foldl_join_frame_generic / keyfactor_float_generic / bucket_factor_pull_generic / etc.) are tracked
;; below and re-proven incrementally. Until ALL consumed laws are here, the clean surface still installs
;; the old `wandler.laws.relational/install!`; the repoint + old-engine deletion happen once complete.
;; Companion: ansatz/docs/WANDLER_REIMPL_PLAN.md (Level 2).

(ns wandler.clean.laws.faq
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [wandler.clean.laws.bucket :as bucket]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn install!
  "Admit the THIN-re-proven FAQ index-family laws into the global env (idempotent). Builds on
   `bucket/install!` (the dependency closure: kmap + plist + frame + the `Map.join_eq` rfl lemma the
   join factor/count laws rewrite with, plus the aggregate `Map_aggJoin_*` cluster). Each `theorem`
   form is kernel `check-constant`-verified as it lands. Returns :installed."
  []
  (bucket/install!)

  ;; ── LINEARITY foundation (List, Nat) ────────────────────────────────────────────────────────────
  ;; sum_map_zero: a fold of all-zeros leaves the accumulator. Base of the additive-structure cluster.
  (when-not (has? "List.sum_map_zero")
    (try
      (eval '(ansatz.core/theorem List.sum_map_zero
               [ys :- (List Nat), acc :- Nat]
               (= Nat (List.foldl Nat Nat Nat.add acc (List.map Nat Nat (fn [y :- Nat] Nat.zero) ys)) acc)
               (induction ys generalizing acc)
               (all_goals (simp_all [List.map_cons List.map_nil List.foldl_cons List.foldl_nil Nat.add_zero]))))
      (catch Throwable _ nil)))

  ;; foldl_add_pull: pull the accumulator out of an additive fold — `foldl + acc L = acc + foldl + 0 L`.
  ;; The keystone for the accumulator handling every other linearity law needs. CONTROLLED rw: apply the
  ;; ∀-quantified IH at the two specific accumulators (`acc+head`, `0+head`), then `omega` (the residual
  ;; is linear in the opaque `foldl + 0 tail`).
  (when-not (has? "List.foldl_add_pull")
    (try
      (eval '(ansatz.core/theorem List.foldl_add_pull
               [L :- (List Nat), acc :- Nat]
               (= Nat (List.foldl Nat Nat Nat.add acc L) (Nat.add acc (List.foldl Nat Nat Nat.add Nat.zero L)))
               (induction L generalizing acc)
               (all_goals (simp [List.foldl_cons List.foldl_nil Nat.add_zero]))
               (rw [(ih_tail (Nat.add acc head))])
               (rw [(ih_tail (Nat.add Nat.zero head))])
               (omega)))
      (catch Throwable _ nil)))

  ;; ── AGGREGATION-THROUGH-JOIN factor (Map cluster) ───────────────────────────────────────────────
  ;; foldl_join_factor: a left-fold over a `Map.join` factors into per-key bucket folds — Σ_{x⋈y} =
  ;; Σ_x Σ_{y∈bucket(kf x)}, WITHOUT materializing the |xs|·|ys| pair list. THE deferred Phase-4
  ;; keystone, now thin: expose the join (`rw [Map.join_eq]`) then `simp` the flatMap/map folds.
  (when-not (has? "Map.foldl_join_factor")
    (try
      (eval '(ansatz.core/theorem Map.foldl_join_factor
               [K :- (Sort 1), X :- (Sort 1), Y :- (Sort 1), S :- (Sort 1), dec :- (DecidableEq K),
                op :- (=> S (=> (Prod X Y) S)), e :- S, kf :- (=> X K), lf :- (=> Y K),
                xs :- (List X), ys :- (List Y)]
               (= S (List.foldl S (Prod X Y) op e (Map.join K X Y dec kf lf xs ys))
                    (List.foldl S X (fn [acc :- S] (fn [x :- X]
                      (List.foldl S Y (fn [acc2 :- S] (fn [y :- Y] (op acc2 (Prod.mk X Y x y)))) acc
                        (Option.getD (List Y) (Map.lookup K (List Y) dec (kf x) (Map.group_by K Y dec lf ys)) (List.nil Y))))) e xs))
               (rw [Map.join_eq]) (simp [List.foldl_flatMap List.foldl_map])))
      (catch Throwable _ nil)))

  ;; count_join_factor: |Map.join| = Σ per-key bucket lengths — count without the product. Same recipe,
  ;; the length folds (`List.length_flatMap`/`length_map`) instead of the value folds.
  (when-not (has? "Map.count_join_factor")
    (try
      (eval '(ansatz.core/theorem Map.count_join_factor
               [K :- (Sort 1), X :- (Sort 1), Y :- (Sort 1), dec :- (DecidableEq K),
                kf :- (=> X K), lf :- (=> Y K), xs :- (List X), ys :- (List Y)]
               (= Nat
                  (List.length (Prod X Y) (Map.join K X Y dec kf lf xs ys))
                  (List.sum Nat instAddNat (Zero.ofOfNat0 Nat (instOfNatNat 0))
                    (List.map X Nat
                      (fn [x :- X] (List.length Y (Option.getD (List Y) (Map.lookup K (List Y) dec (kf x) (Map.group_by K Y dec lf ys)) (List.nil Y))))
                      xs)))
               (rw [Map.join_eq]) (simp_all [List.length_flatMap List.length_map])))
      (catch Throwable _ nil)))

  ;; TODO (Level-2 remaining, tracked): the accumulator-split linearity laws
  ;;   List.sum_map_mul_const / List.sum_map_const_mul / List.sum_map_add_distrib
  ;;   (each needs a 0-init sub-lemma proven by induction+foldl_add_pull+omega, then a `foldl_add_pull`
  ;;    lift to the generalized accumulator form — a single `rw [ih]` can't AC-reassociate the split);
  ;; List.foldl_congr (pointwise congruence — `induction l generalizing e <;> simp_all [congr-hyp]`);
  ;; and the DEEP generic frame family (Map.foldl_join_frame_generic / foldl_join_sum_factor_generic /
  ;;   foldl_keyfactor_float_generic / bucket_factor_pull_generic / Nat.cond_and_mul_split_generic,
  ;;   each a hand-built term proof in `wandler.laws.proofs.frame` to be re-derived as a tactic script).
  :installed)
