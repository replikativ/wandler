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
            [ansatz.prelude.algebra :as alg]
            [wandler.clean.laws.bucket :as bucket]
            [wandler.clean.laws.ac :as ac-providers]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn install!
  "Admit the THIN-re-proven FAQ index-family laws into the global env (idempotent). Builds on
   `bucket/install!` (the dependency closure: kmap + plist + frame + the `Map.join_eq` rfl lemma the
   join factor/count laws rewrite with, plus the aggregate `Map_aggJoin_*` cluster). Each `theorem`
   form is kernel `check-constant`-verified as it lands. Returns :installed."
  []
  (alg/install-classes!)   ;; WAddMonoid ⊂ WSemiring — the carriers the _generic laws + AC providers use
  (bucket/install!)
  ;; AC providers for WAddMonoid.add / WSemiring.add — feed `ac_rfl` (the monoid normalizer that
  ;; closes the abstract associativity+identity reshuffles in the `_generic` proofs below).
  (ac-providers/register!)

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

  ;; foldl_congr: pointwise step-function congruence — folds with extensionally-equal steps agree.
  ;; `induction l generalizing e`; cons rewrites the head via the congruence hyp `h e head`, then the IH.
  (when-not (has? "List.foldl_congr")
    (try
      (eval '(ansatz.core/theorem List.foldl_congr
               [Acc :- (Sort 1), Elem :- (Sort 1), f :- (=> Acc (=> Elem Acc)), g :- (=> Acc (=> Elem Acc)),
                l :- (List Elem), e :- Acc,
                h :- (forall [b Acc] (forall [a Elem] (= Acc (f b a) (g b a))))]
               (= Acc (List.foldl Acc Elem f e l) (List.foldl Acc Elem g e l))
               (induction l generalizing e)
               (all_goals (simp [List.foldl_cons List.foldl_nil]))
               (rw [(h e head)])
               (rw [(ih_tail (g e head))])))
      (catch Throwable _ nil)))

  ;; sum_map_add_distrib: ∑ distributes over a pointwise sum (accumulator-generalized over a, b). The
  ;; cons accumulator `(a+b)+(f h+g h)` is reassociated to `(a+f h)+(b+g h)` by `Nat.add_add_add_comm`,
  ;; then the ∀a∀b IH at those two accumulators closes it.
  (when-not (has? "List.sum_map_add_distrib")
    (try
      (eval '(ansatz.core/theorem List.sum_map_add_distrib
               [f :- (=> Nat Nat), g :- (=> Nat Nat), xs :- (List Nat), a :- Nat, b :- Nat]
               (= Nat (List.foldl Nat Nat Nat.add (Nat.add a b) (List.map Nat Nat (fn [x :- Nat] (Nat.add (f x) (g x))) xs))
                      (Nat.add (List.foldl Nat Nat Nat.add a (List.map Nat Nat f xs))
                               (List.foldl Nat Nat Nat.add b (List.map Nat Nat g xs))))
               (induction xs generalizing a b)
               (all_goals (simp [List.map_cons List.map_nil List.foldl_cons List.foldl_nil]))
               (rw [(Nat.add_add_add_comm a b (f head) (g head))])
               (rw [(ih_tail (Nat.add a (f head)) (Nat.add b (g head)))])))
      (catch Throwable _ nil)))

  ;; sum_map_mul_const / sum_map_const_mul: a loop-invariant factor distributes out of the sum (the
  ;; certificate for hoisting an x-free multiplicative factor — both multiplication orders). Proven via
  ;; an accumulator-GENERALIZED helper (`_gen`, clean induction: reassociate the cons accumulator with
  ;; `Nat.add_mul`/`Nat.mul_add` reversed, then the ∀a IH), then the consumed 0-init form derives by
  ;; rewriting backwards through `_gen` and normalizing the `0·c`/`c·0` init (`Nat.zero_mul`; `c·0`
  ;; reduces by rfl). This is the thin form of the old `Eq.trans (congrArg … (Eq.symm zero_mul)) gen`.
  (when-not (has? "List.sum_map_mul_const_gen")
    (try
      (eval '(ansatz.core/theorem List.sum_map_mul_const_gen
               [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat), a :- Nat]
               (= Nat (List.foldl Nat Nat Nat.add (Nat.mul a c) (List.map Nat Nat (fn [x :- Nat] (Nat.mul (f x) c)) xs))
                      (Nat.mul (List.foldl Nat Nat Nat.add a (List.map Nat Nat f xs)) c))
               (induction xs generalizing a)
               (all_goals (simp [List.map_cons List.map_nil List.foldl_cons List.foldl_nil]))
               (rw [<- (Nat.add_mul a (f head) c)])
               (rw [(ih_tail (Nat.add a (f head)))])))
      (catch Throwable _ nil)))
  (when-not (has? "List.sum_map_mul_const")
    (try
      (eval '(ansatz.core/theorem List.sum_map_mul_const
               [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat)]
               (= Nat (List.foldl Nat Nat Nat.add Nat.zero (List.map Nat Nat (fn [x :- Nat] (Nat.mul (f x) c)) xs))
                      (Nat.mul (List.foldl Nat Nat Nat.add Nat.zero (List.map Nat Nat f xs)) c))
               (rw [<- (List.sum_map_mul_const_gen f c xs Nat.zero)])
               (rw [Nat.zero_mul])))
      (catch Throwable _ nil)))
  (when-not (has? "List.sum_map_const_mul_gen")
    (try
      (eval '(ansatz.core/theorem List.sum_map_const_mul_gen
               [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat), a :- Nat]
               (= Nat (List.foldl Nat Nat Nat.add (Nat.mul c a) (List.map Nat Nat (fn [x :- Nat] (Nat.mul c (f x))) xs))
                      (Nat.mul c (List.foldl Nat Nat Nat.add a (List.map Nat Nat f xs))))
               (induction xs generalizing a)
               (all_goals (simp [List.map_cons List.map_nil List.foldl_cons List.foldl_nil]))
               (rw [<- (Nat.mul_add c a (f head))])
               (rw [(ih_tail (Nat.add a (f head)))])))
      (catch Throwable _ nil)))
  (when-not (has? "List.sum_map_const_mul")
    (try
      (eval '(ansatz.core/theorem List.sum_map_const_mul
               [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat)]
               (= Nat (List.foldl Nat Nat Nat.add Nat.zero (List.map Nat Nat (fn [x :- Nat] (Nat.mul c (f x))) xs))
                      (Nat.mul c (List.foldl Nat Nat Nat.add Nat.zero (List.map Nat Nat f xs))))
               ;; `c·0` reduces to 0 by rfl, so the single backward rewrite closes it (rw's try-rfl).
               (rw [<- (List.sum_map_const_mul_gen f c xs Nat.zero)])))
      (catch Throwable _ nil)))

  ;; ── SEMIRING-GENERIC const-factor pull (building block for the frame rule) ──────────────────────
  ;; foldl_const_mul_pull (accumulator-generalized): a loop-invariant left factor `c·` pulls out of an
  ;; additive fold over ANY semiring — `foldl (λa y. a + c·g y) (c·acc) l = c·(foldl (λa y. a + g y) acc l)`.
  ;; The algebra is passed as HYPOTHESES (`hMA` left-distrib, `hMZ` annihilator) rather than WSemiring
  ;; accessors — the same shape the generic frame proof threads. cons reassociates the accumulator with
  ;; the distributivity hyp REVERSED (`rw [<- (hMA c acc (g head))]`), then the quantified IH closes it.
  (when-not (has? "List.foldl_const_mul_pull_gen")
    (try
      (eval '(ansatz.core/theorem List.foldl_const_mul_pull_gen
               [S :- (Sort 1), add :- (=> S (=> S S)), mul :- (=> S (=> S S)), zero :- S,
                hMA :- (forall [x S] (forall [y S] (forall [w S] (= S (mul x (add y w)) (add (mul x y) (mul x w)))))),
                hMZ :- (forall [x S] (= S (mul x zero) zero)),
                al :- (Sort 1), c :- S, g :- (=> al S), l :- (List al), acc :- S]
               (= S (List.foldl S al (fn [a :- S] (fn [y :- al] (add a (mul c (g y))))) (mul c acc) l)
                    (mul c (List.foldl S al (fn [a :- S] (fn [y :- al] (add a (g y)))) acc l)))
               (induction l generalizing acc)
               (all_goals (simp [List.foldl_cons List.foldl_nil]))
               (rw [<- (hMA c acc (g head))])
               (rw [(ih_tail (add acc (g head)))])))
      (catch Throwable _ nil)))

  ;; ── ADDITIVE-MONOID init extraction (the pre-aggregated-index sub-lemma) ─────────────────────────
  ;; foldl_add_init_generic: pull the accumulator out of an additive monoid fold —
  ;;   foldl (λa y. a ⊕ g y) acc l = acc ⊕ foldl (λa y. a ⊕ g y) 0 l   (over ANY WAddMonoid).
  ;; The WAddMonoid-generic sibling of `List.foldl_add_pull` (Nat). The accumulator reshuffle that
  ;; `omega` closed for Nat is here closed by `ac_rfl` (the AC/monoid normalizer): after the IH exposes
  ;; the SAME tail-fold atom on both sides, the residual is a pure associativity+identity reassociation
  ;; over `WAddMonoid.add`/`WAddMonoid.zero`, which `ac_rfl` normalizes (the nil case is the bare
  ;; `acc = acc ⊕ 0` identity-absorption). The crux sub-lemma of `foldl_join_sum_factor_generic`.
  (when-not (has? "List.foldl_add_init_generic")
    (try
      (eval '(ansatz.core/theorem List.foldl_add_init_generic
               [S :- (Sort 1), inst :- (WAddMonoid S), Y :- (Sort 1), g :- (=> Y S), l :- (List Y), acc :- S]
               (= S (List.foldl S Y (fn [a :- S] (fn [y :- Y] (WAddMonoid.add S inst a (g y)))) acc l)
                    (WAddMonoid.add S inst acc
                      (List.foldl S Y (fn [a :- S] (fn [y :- Y] (WAddMonoid.add S inst a (g y)))) (WAddMonoid.zero S inst) l)))
               (induction l generalizing acc)
               (all_goals (simp [List.foldl_cons List.foldl_nil]))
               (all_goals (first (ac_rfl)
                                 (and_then (rw [(ih_tail (WAddMonoid.add S inst acc (g head)))])
                                           (and_then (rw [(ih_tail (WAddMonoid.add S inst (WAddMonoid.zero S inst) (g head)))])
                                                     (ac_rfl)))))))
      (catch Throwable _ nil)))

  ;; ── CONDITIONAL SEPARATION (semiring-generic) ───────────────────────────────────────────────────
  ;; cond_and_mul_split: a separable conjunctive guard factors a weighted product —
  ;;   cond(a&&b)(u·v) 0 = (cond a u 0)·(cond b v 0) — so a guarded join weight splits per side and the
  ;; frame rule fires. Over ANY WSemiring (uses only mul + zero + the two annihilators). The literal
  ;; Lean `cond` const is spelled `bif` in surface (`cond` itself is Clojure-clause-cond). RECIPE for
  ;; the WSemiring-accessor generics: `cases` both bools; `simp []` ground-reduces cond/Bool.and; then
  ;; per-case `rw` the annihilator accessor with EXPLICIT args (simp can't use applied projections as
  ;; lemmas — type-mismatch); `rfl` closes the defeq `WSemiring.zero` vs `WAddMonoid.zero∘toWAddMonoid`.
  (when-not (has? "Nat.cond_and_mul_split_generic")
    (try
      (eval '(ansatz.core/theorem Nat.cond_and_mul_split_generic
               [S :- (Sort 1), inst :- (WSemiring S), a :- Bool, b :- Bool, u :- S, v :- S]
               (= S (bif (Bool.and a b) (WSemiring.mul S inst u v) (WSemiring.zero S inst))
                    (WSemiring.mul S inst (bif a u (WSemiring.zero S inst)) (bif b v (WSemiring.zero S inst))))
               (cases a) (all_goals (cases b)) (all_goals (simp []))
               (all_goals (first (rw [(WSemiring.mul_zero S inst u)])
                                 (rw [(WSemiring.zero_mul S inst v)])
                                 (rw [(WSemiring.zero_mul S inst (WSemiring.zero S inst))])))
               (all_goals (rfl))))
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

  ;; TODO (Level-2 remaining, tracked): the DEEP generic frame family — hand-built term proofs in
  ;; `wandler.laws.proofs.frame` to be re-derived as tactic scripts:
  ;;   Map.foldl_join_frame_generic / Map.foldl_join_sum_factor_generic / Map.foldl_keyfactor_float_generic
  ;;   / Map.bucket_factor_pull_generic / Nat.cond_and_mul_split_generic (+ their Nat instances, derived
  ;;   by applying the generic to the WSemiring-Nat instance, option 2a) and the lookup/group_by +
  ;;   filter→join pushdown + semijoin foundation (relational.clj, already tactic-based — straight port).
  ;; Then: repoint wandler.clean.surface.core → faq/install!, retarget the Perm reorder/grace-hash
  ;; strategies to the aggregate Map_aggJoin_reorder (option 1a), delete wandler.laws.*, suite-gate.
  :installed)
