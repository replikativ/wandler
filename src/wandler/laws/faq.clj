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
;;     accumulator — see thin-surface-migration); use CONTROLLED `rw [(ih_tail <explicit-acc>)]`.
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
;; Companion: ansatz/docs/ARCHITECTURE.md (Level 2).

(ns wandler.laws.faq
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.prelude.algebra :as alg]
            [wandler.algebra :as algebra]
            [wandler.laws.bucket :as bucket]
            [wandler.laws.reorder :as reorder]
            [wandler.laws.relational :as relational]
            [wandler.laws.grace :as grace]
            [wandler.laws.ac :as ac-providers]
            [wandler.laws.semiring :as sreg]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn- install-linearity-laws!
  "FAQ index-family laws, group 1/3 — the List/Nat linearity foundation. (The law proofs are split
   across three sub-installers so no single method exceeds the JVM 64KB bytecode limit; `install!`
   calls the three groups in order.)"
  []
  ;; ── LINEARITY foundation (List, Nat) ────────────────────────────────────────────────────────────
  ;; sum_map_zero: a fold of all-zeros leaves the accumulator. Base of the additive-structure cluster.
  (a/deftheorem List.sum_map_zero
    [ys :- (List Nat), acc :- Nat]
    (= Nat (List.foldl Nat.add acc (List.map (fn [y :- Nat] Nat.zero) ys)) acc)
    (induction ys generalizing acc)
    (all_goals (simp_all [List.map_cons List.map_nil List.foldl_cons List.foldl_nil Nat.add_zero])))

  ;; foldl_add_pull: pull the accumulator out of an additive fold — `foldl + acc L = acc + foldl + 0 L`.
  ;; The keystone for the accumulator handling every other linearity law needs. CONTROLLED rw: apply the
  ;; ∀-quantified IH at the two specific accumulators (`acc+head`, `0+head`), then `omega` (the residual
  ;; is linear in the opaque `foldl + 0 tail`).
  (a/deftheorem List.foldl_add_pull
    [L :- (List Nat), acc :- Nat]
    (= Nat (List.foldl Nat.add acc L) (Nat.add acc (List.foldl Nat.add Nat.zero L)))
    (induction L generalizing acc)
    (all_goals (simp [List.foldl_cons List.foldl_nil Nat.add_zero]))
    (rw [(ih_tail (Nat.add acc head))])
    (rw [(ih_tail (Nat.add Nat.zero head))])
    (omega))

  ;; foldl_congr: pointwise step-function congruence — folds with extensionally-equal steps agree.
  ;; `induction l generalizing e`; cons rewrites the head via the congruence hyp `h e head`, then the IH.
  (a/deftheorem List.foldl_congr
    [Acc :- (Sort 1), Elem :- (Sort 1), f :- (=> Acc (=> Elem Acc)), g :- (=> Acc (=> Elem Acc)),
     l :- (List Elem), e :- Acc,
     h :- (forall [b Acc] (forall [a Elem] (= Acc (f b a) (g b a))))]
    (= Acc (List.foldl f e l) (List.foldl g e l))
    (induction l generalizing e)
    (all_goals (simp [List.foldl_cons List.foldl_nil]))
    (rw [(h e head)])
    (rw [(ih_tail (g e head))]))

  ;; lookup_map_kv: probing a key/value-mapped assoc list = mapping the value-fn over the probe —
  ;;   lookup k (map (λp. (p.1, f p.2)) l) = Option.map f (lookup k l).
  ;; THE pre-aggregated-index crux (the index is built by value-mapping group_by; a lookup of a key's
  ;; bucket then equals mapping the bucket-fn over the raw lookup). Thin: induction on l; the cons head
  ;; is opaque so `Prod.eta`-rewrite it to `(head.1, head.2)` first (else `lookup_cons` won't fire on the
  ;; RHS), reduce both sides to the same `BEq.beq k head.1` matcher, then `by_cases` that Bool — each
  ;; branch closes by `simp_all` (true → `some (f head.2)` both sides; false → parallel via the IH).
  (a/deftheorem List.lookup_map_kv
    [K :- Type, V :- Type, W :- Type, inst :- (BEq K), f :- (=> V W), k :- K, l :- (List (Prod K V))]
    (= (Option W)
       (List.lookup K W inst k
                    (List.map (fn [p :- (Prod K V)] (Prod.mk (Prod.fst p) (f (Prod.snd p)))) l))
       (Option.map V W f (List.lookup K V inst k l)))
    (induction l)
    (all_goals (try (rw [<- (Prod.eta K V head)])))
    (all_goals (simp [List.map_nil List.map_cons List.lookup_nil List.lookup_cons]))
    (all_goals (try (by_cases (BEq.beq K inst k (Prod.fst head)))))
    (all_goals (try (simp_all [Option.map List.lookup_cons]))))

  ;; sum_map_add_distrib: ∑ distributes over a pointwise sum (accumulator-generalized over a, b). The
  ;; cons accumulator `(a+b)+(f h+g h)` is reassociated to `(a+f h)+(b+g h)` by `Nat.add_add_add_comm`,
  ;; then the ∀a∀b IH at those two accumulators closes it.
  (a/deftheorem List.sum_map_add_distrib
    [f :- (=> Nat Nat), g :- (=> Nat Nat), xs :- (List Nat), a :- Nat, b :- Nat]
    (= Nat (List.foldl Nat.add (Nat.add a b) (List.map (fn [x :- Nat] (Nat.add (f x) (g x))) xs))
       (Nat.add (List.foldl Nat.add a (List.map f xs))
                (List.foldl Nat.add b (List.map g xs))))
    (induction xs generalizing a b)
    (all_goals (simp [List.map_cons List.map_nil List.foldl_cons List.foldl_nil]))
    (rw [(Nat.add_add_add_comm a b (f head) (g head))])
    (rw [(ih_tail (Nat.add a (f head)) (Nat.add b (g head)))]))

  ;; sum_map_mul_const / sum_map_const_mul: a loop-invariant factor distributes out of the sum (the
  ;; certificate for hoisting an x-free multiplicative factor — both multiplication orders). Proven via
  ;; an accumulator-GENERALIZED helper (`_gen`, clean induction: reassociate the cons accumulator with
  ;; `Nat.add_mul`/`Nat.mul_add` reversed, then the ∀a IH), then the consumed 0-init form derives by
  ;; rewriting backwards through `_gen` and normalizing the `0·c`/`c·0` init (`Nat.zero_mul`; `c·0`
  ;; reduces by rfl). This is the thin form of the old `Eq.trans (congrArg … (Eq.symm zero_mul)) gen`.
  (a/deftheorem List.sum_map_mul_const_gen
    [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat), a :- Nat]
    (= Nat (List.foldl Nat.add (Nat.mul a c) (List.map (fn [x :- Nat] (Nat.mul (f x) c)) xs))
       (Nat.mul (List.foldl Nat.add a (List.map f xs)) c))
    (induction xs generalizing a)
    (all_goals (simp [List.map_cons List.map_nil List.foldl_cons List.foldl_nil]))
    (rw [<- (Nat.add_mul a (f head) c)])
    (rw [(ih_tail (Nat.add a (f head)))]))
  (a/deftheorem List.sum_map_mul_const
    [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat)]
    (= Nat (List.foldl Nat.add Nat.zero (List.map (fn [x :- Nat] (Nat.mul (f x) c)) xs))
       (Nat.mul (List.foldl Nat.add Nat.zero (List.map f xs)) c))
    (rw [<- (List.sum_map_mul_const_gen f c xs Nat.zero)])
    (rw [Nat.zero_mul]))
  (a/deftheorem List.sum_map_const_mul_gen
    [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat), a :- Nat]
    (= Nat (List.foldl Nat.add (Nat.mul c a) (List.map (fn [x :- Nat] (Nat.mul c (f x))) xs))
       (Nat.mul c (List.foldl Nat.add a (List.map f xs))))
    (induction xs generalizing a)
    (all_goals (simp [List.map_cons List.map_nil List.foldl_cons List.foldl_nil]))
    (rw [<- (Nat.mul_add c a (f head))])
    (rw [(ih_tail (Nat.add a (f head)))]))
  (a/deftheorem List.sum_map_const_mul
    [f :- (=> Nat Nat), c :- Nat, xs :- (List Nat)]
    (= Nat (List.foldl Nat.add Nat.zero (List.map (fn [x :- Nat] (Nat.mul c (f x))) xs))
       (Nat.mul c (List.foldl Nat.add Nat.zero (List.map f xs))))
    ;; `c·0` reduces to 0 by rfl, so the single backward rewrite closes it (rw's try-rfl).
    (rw [<- (List.sum_map_const_mul_gen f c xs Nat.zero)])))

(defn- install-factor-pull-laws!
  "FAQ index-family laws, group 2/3 — const-factor pull, additive-monoid init extraction, WSemiring
   multiplicative pull, and conditional separation."
  []
  ;; ── SEMIRING-GENERIC const-factor pull (building block for the frame rule) ──────────────────────
  ;; foldl_const_mul_pull (accumulator-generalized): a loop-invariant left factor `c·` pulls out of an
  ;; additive fold over ANY semiring — `foldl (λa y. a + c·g y) (c·acc) l = c·(foldl (λa y. a + g y) acc l)`.
  ;; The algebra is passed as HYPOTHESES (`hMA` left-distrib, `hMZ` annihilator) rather than WSemiring
  ;; accessors — the same shape the generic frame proof threads. cons reassociates the accumulator with
  ;; the distributivity hyp REVERSED (`rw [<- (hMA c acc (g head))]`), then the quantified IH closes it.
  (a/deftheorem List.foldl_const_mul_pull_gen
    [S :- (Sort 1), add :- (=> S (=> S S)), mul :- (=> S (=> S S)), zero :- S,
     hMA :- (forall [x S] (forall [y S] (forall [w S] (= S (mul x (add y w)) (add (mul x y) (mul x w)))))),
     hMZ :- (forall [x S] (= S (mul x zero) zero)),
     al :- (Sort 1), c :- S, g :- (=> al S), l :- (List al), acc :- S]
    (= S (List.foldl (fn [a :- S] (fn [y :- al] (add a (mul c (g y))))) (mul c acc) l)
       (mul c (List.foldl (fn [a :- S] (fn [y :- al] (add a (g y)))) acc l)))
    (induction l generalizing acc)
    (all_goals (simp [List.foldl_cons List.foldl_nil]))
    (rw [<- (hMA c acc (g head))])
    (rw [(ih_tail (add acc (g head)))]))

  ;; ── ADDITIVE-MONOID init extraction (the pre-aggregated-index sub-lemma) ─────────────────────────
  ;; foldl_add_init_generic: pull the accumulator out of an additive monoid fold —
  ;;   foldl (λa y. a ⊕ g y) acc l = acc ⊕ foldl (λa y. a ⊕ g y) 0 l   (over ANY WAddMonoid).
  ;; The WAddMonoid-generic sibling of `List.foldl_add_pull` (Nat). The accumulator reshuffle that
  ;; `omega` closed for Nat is here closed by `ac_rfl` (the AC/monoid normalizer): after the IH exposes
  ;; the SAME tail-fold atom on both sides, the residual is a pure associativity+identity reassociation
  ;; over `WAddMonoid.add`/`WAddMonoid.zero`, which `ac_rfl` normalizes (the nil case is the bare
  ;; `acc = acc ⊕ 0` identity-absorption). The crux sub-lemma of `foldl_join_sum_factor_generic`.
  (a/deftheorem List.foldl_add_init_generic
    [S :- (Sort 1), inst :- (WAddMonoid S), Y :- (Sort 1), g :- (=> Y S), l :- (List Y), acc :- S]
    (= S (List.foldl (fn [a :- S] (fn [y :- Y] (WAddMonoid.add S inst a (g y)))) acc l)
       (WAddMonoid.add S inst acc
                       (List.foldl (fn [a :- S] (fn [y :- Y] (WAddMonoid.add S inst a (g y)))) (WAddMonoid.zero S inst) l)))
    (induction l generalizing acc)
    (all_goals (simp [List.foldl_cons List.foldl_nil]))
    (all_goals (first (ac_rfl)
                      (and_then (rw [(ih_tail (WAddMonoid.add S inst acc (g head)))])
                                (and_then (rw [(ih_tail (WAddMonoid.add S inst (WAddMonoid.zero S inst) (g head)))])
                                          (ac_rfl))))))

  ;; List.foldl_add_init — the Nat instance of the generic. The DBSP differential join builds with it
  ;; (exec/dbsp.clj's Map.join_count_incr). Derived by applying the generic to the Nat WAddMonoid
  ;; instance (WAddMonoid.add Nat (mk …) ≡ Nat.add by def-eq). Was admitted by the retired
  ;; wandler.laws.proofs.frame/prove-foldl-add-init.
  (a/deftheorem List.foldl_add_init
    [Y :- Type, g :- (=> Y Nat), l :- (List Y), acc :- Nat]
    (= Nat (List.foldl (fn [a :- Nat] (fn [y :- Y] (Nat.add a (g y)))) acc l)
       (Nat.add acc (List.foldl (fn [a :- Nat] (fn [y :- Y] (Nat.add a (g y)))) Nat.zero l)))
    (exact (List.foldl_add_init_generic Nat
                                        (WAddMonoid.mk Nat Nat.add Nat.zero Nat.add_assoc Nat.zero_add Nat.add_zero)
                                        Y g l acc)))

  ;; ── WSemiring multiplicative-pull foundation (for the frame rule's f(x)· factor) ─────────────────
  ;; foldl_add_init_wsem: the WSemiring-spelled sibling of foldl_add_init_generic (so the frame chain
  ;; stays in one spelling). Closed by `ac_rfl` over the registered WSemiring.add provider.
  (a/deftheorem List.foldl_add_init_wsem
    [S :- (Sort 1), inst :- (WSemiring S), Y :- (Sort 1), g :- (=> Y S), l :- (List Y), acc :- S]
    (= S (List.foldl (fn [a :- S] (fn [y :- Y] (WSemiring.add S inst a (g y)))) acc l)
       (WSemiring.add S inst acc (List.foldl (fn [a :- S] (fn [y :- Y] (WSemiring.add S inst a (g y)))) (WSemiring.zero S inst) l)))
    (induction l generalizing acc)
    (all_goals (simp [List.foldl_cons List.foldl_nil]))
    (all_goals (first (ac_rfl)
                      (and_then (rw [(ih_tail (WSemiring.add S inst acc (g head)))])
                                (and_then (rw [(ih_tail (WSemiring.add S inst (WSemiring.zero S inst) (g head)))])
                                          (ac_rfl))))))
  ;; foldl_const_mul_pull (acc-general): a loop-invariant LEFT factor `c·` pulls out of an additive
  ;; WSemiring fold — `foldl (λa y. a + c·g y) (c·acc) l = c·(foldl (λa y. a + g y) acc l)`. cons
  ;; reassociates the accumulator with mul_add REVERSED, then the quantified IH. (Distributivity, not
  ;; AC — so ac_rfl does NOT apply; this is the genuine semiring step the frame rule needs.)
  (a/deftheorem List.foldl_const_mul_pull_wsem_gen
    [S :- (Sort 1), inst :- (WSemiring S), al :- (Sort 1), c :- S, g :- (=> al S), l :- (List al), acc :- S]
    (= S (List.foldl (fn [a :- S] (fn [y :- al] (WSemiring.add S inst a (WSemiring.mul S inst c (g y))))) (WSemiring.mul S inst c acc) l)
       (WSemiring.mul S inst c (List.foldl (fn [a :- S] (fn [y :- al] (WSemiring.add S inst a (g y)))) acc l)))
    (induction l generalizing acc)
    (all_goals (simp [List.foldl_cons List.foldl_nil]))
    (rw [<- (WSemiring.mul_add S inst c acc (g head))])
    (rw [(ih_tail (WSemiring.add S inst acc (g head)))]))
  ;; foldl_const_mul_pull (0-init): the consumed form, derived from the acc-general lemma by
  ;; instantiating acc := zero and collapsing the `c·0 → 0` annihilator (the thin form of the old
  ;; `Eq.trans … (Eq.symm mul_zero)`).
  (a/deftheorem List.foldl_const_mul_pull
    [S :- (Sort 1), inst :- (WSemiring S), al :- (Sort 1), c :- S, g :- (=> al S), l :- (List al)]
    (= S (List.foldl (fn [a :- S] (fn [y :- al] (WSemiring.add S inst a (WSemiring.mul S inst c (g y))))) (WSemiring.zero S inst) l)
       (WSemiring.mul S inst c (List.foldl (fn [a :- S] (fn [y :- al] (WSemiring.add S inst a (g y)))) (WSemiring.zero S inst) l)))
    (rw [<- (List.foldl_const_mul_pull_wsem_gen S inst al c g l (WSemiring.zero S inst))])
    (rw [(WSemiring.mul_zero S inst c)]))

  ;; ── CONDITIONAL SEPARATION (semiring-generic) ───────────────────────────────────────────────────
  ;; cond_and_mul_split: a separable conjunctive guard factors a weighted product —
  ;;   cond(a&&b)(u·v) 0 = (cond a u 0)·(cond b v 0) — so a guarded join weight splits per side and the
  ;; frame rule fires. Over ANY WSemiring (uses only mul + zero + the two annihilators). The literal
  ;; Lean `cond` const is spelled `bif` in surface (`cond` itself is Clojure-clause-cond). RECIPE for
  ;; the WSemiring-accessor generics: `cases` both bools; `simp []` ground-reduces cond/Bool.and; then
  ;; per-case `rw` the annihilator accessor with EXPLICIT args (simp can't use applied projections as
  ;; lemmas — type-mismatch); `rfl` closes the defeq `WSemiring.zero` vs `WAddMonoid.zero∘toWAddMonoid`.
  (a/deftheorem Nat.cond_and_mul_split_generic
    [S :- (Sort 1), inst :- (WSemiring S), a :- Bool, b :- Bool, u :- S, v :- S]
    (= S (bif (Bool.and a b) (WSemiring.mul S inst u v) (WSemiring.zero S inst))
       (WSemiring.mul S inst (bif a u (WSemiring.zero S inst)) (bif b v (WSemiring.zero S inst))))
    (cases a) (all_goals (cases b)) (all_goals (simp []))
    (all_goals (first (rw [(WSemiring.mul_zero S inst u)])
                      (rw [(WSemiring.zero_mul S inst v)])
                      (rw [(WSemiring.zero_mul S inst (WSemiring.zero S inst))])))
    (all_goals (rfl))))

(defn- install-agg-frame-laws!
  "FAQ index-family laws, group 3/3 — aggregation-through-join factor, pre-aggregated index,
   the frame rule, and the FD-scope keyfactor."
  []
  ;; ── AGGREGATION-THROUGH-JOIN factor (Map cluster) ───────────────────────────────────────────────
  ;; foldl_join_factor: a left-fold over a `Map.join` factors into per-key bucket folds — Σ_{x⋈y} =
  ;; Σ_x Σ_{y∈bucket(kf x)}, WITHOUT materializing the |xs|·|ys| pair list. THE deferred Phase-4
  ;; keystone, now thin: expose the join (`rw [Map.join_eq]`) then `simp` the flatMap/map folds.
  (a/deftheorem Map.foldl_join_factor
    [K :- (Sort 1), X :- (Sort 1), Y :- (Sort 1), S :- (Sort 1), dec :- (DecidableEq K),
     op :- (=> S (=> (Prod X Y) S)), e :- S, kf :- (=> X K), lf :- (=> Y K),
     xs :- (List X), ys :- (List Y)]
    (= S (List.foldl op e (Map.join K X Y dec kf lf xs ys))
       (List.foldl (fn [acc :- S] (fn [x :- X]
                                    (List.foldl (fn [acc2 :- S] (fn [y :- Y] (op acc2 (Prod.mk x y)))) acc
                                                (Option.getD (Map.lookup K (List Y) dec (kf x) (Map.group_by K Y dec lf ys)) (List.nil Y))))) e xs))
    (rw [Map.join_eq]) (simp [List.foldl_flatMap List.foldl_map]))

  ;; count_join_factor: |Map.join| = Σ per-key bucket lengths — count without the product. Same recipe,
  ;; the length folds (`List.length_flatMap`/`length_map`) instead of the value folds.
  (a/deftheorem Map.count_join_factor
    [K :- (Sort 1), X :- (Sort 1), Y :- (Sort 1), dec :- (DecidableEq K),
     kf :- (=> X K), lf :- (=> Y K), xs :- (List X), ys :- (List Y)]
    (= Nat
       (List.length (Prod X Y) (Map.join K X Y dec kf lf xs ys))
       (List.sum Nat instAddNat (Zero.ofOfNat0 Nat (instOfNatNat 0))
                 (List.map (fn [x :- X] (List.length Y (Option.getD (Map.lookup K (List Y) dec (kf x) (Map.group_by K Y dec lf ys)) (List.nil Y))))
                           xs)))
    (rw [Map.join_eq]) (simp_all [List.length_flatMap List.length_map]))

  ;; ── PRE-AGGREGATED INDEX (FAQ) — separable SUM through a join, O(distinct keys) ──────────────────
  ;; foldl_join_sum_factor_generic: a SUM-aggregate `Σ_{x⋈y} g y` over a join equals a fold over xs that
  ;; probes a PRE-AGGREGATED index (each key's bucket pre-summed) — the FAQ asymptotic win, over ANY
  ;; WAddMonoid. THE first deep generic frame-family law re-proven THINLY (was a 50+-term hand proof).
  ;; Assembly recipe (the model for frame_generic / keyfactor_float_generic):
  ;;   (1) `rw [Map.foldl_join_factor]` exposes the per-key bucket fold (Σ_x Σ_{y∈bucket});
  ;;   (2) `apply List.foldl_congr` reduces to the per-key pointwise identity;
  ;;   (3) the pointwise chain: `simp` β-reduces, `foldl_add_init_generic` pulls the accumulator out,
  ;;       `lookup_map_kv` turns the index probe into `Option.map bucketSum (raw probe)`, and the
  ;;       EXPLICIT-arg `Option.getD_map` (the `zero` default isn't syntactically `bucketSum nil`, so the
  ;;       env-lemma form can't match — explicit args are the faithful analog of the old term proof) pushes
  ;;       the sum through `getD`; `rfl` closes (Map.lookup ≡ List.lookup over `Map.entries` by def).
  (a/deftheorem Map.foldl_join_sum_factor_generic
    [S :- (Sort 1), inst :- (WAddMonoid S), K :- (Sort 1), X :- (Sort 1), Y :- (Sort 1),
     dec :- (DecidableEq K), g :- (=> Y S), kf :- (=> X K), lf :- (=> Y K),
     e :- S, xs :- (List X), ys :- (List Y)]
    (= S
       (List.foldl (fn [acc :- S] (fn [p :- (Prod X Y)] (WAddMonoid.add S inst acc (g (Prod.snd p)))))
                   e (Map.join K X Y dec kf lf xs ys))
       (List.foldl (fn [acc :- S] (fn [x :- X]
                                    (WAddMonoid.add S inst acc
                                                    (Option.getD (List.lookup K S (instBEqOfDecidableEq K dec) (kf x)
                                                                              (List.map (fn [p :- (Prod K (List Y))]
                                                                                          (Prod.mk (Prod.fst p)
                                                                                                   (List.foldl (fn [a :- S] (fn [y :- Y] (WAddMonoid.add S inst a (g y)))) (WAddMonoid.zero S inst) (Prod.snd p))))
                                                                                        (Map.entries K (List Y) (Map.group_by K Y dec lf ys))))
                                                                 (WAddMonoid.zero S inst)))))
                   e xs))
    (rw [Map.foldl_join_factor])
    (apply List.foldl_congr)
    (intros b a)
    (simp [])
    (rw [List.foldl_add_init_generic])
    (rw [List.lookup_map_kv])
    (rw [(Option.getD_map (List Y) S
                          (fn [blk :- (List Y)] (List.foldl (fn [acc :- S] (fn [y :- Y] (WAddMonoid.add S inst acc (g y)))) (WAddMonoid.zero S inst) blk))
                          (List.nil Y)
                          (List.lookup K (List Y) (instBEqOfDecidableEq K dec) (kf a) (Map.entries K (List Y) (Map.group_by K Y dec lf ys))))])
    (try (rfl)))

  ;; ── PRE-AGGREGATED bucket-sum helper + the FRAME RULE (separable two-sided weight) ──────────────
  ;; bucket_sum_preagg: the per-key pointwise identity shared by sum_factor and the frame rule —
  ;; `Σ_{y∈bucket k} g y = getD (lookup k <pre-aggregated index>) 0`. Proven in a CLEAN context (no
  ;; intermediate simp), so `lookup_map_kv` + the explicit-arg `Option.getD_map` close it directly
  ;; (the eta-sensitive default matches here). Factored out so the frame proof closes by a single `rw`.
  (a/deftheorem Map.bucket_sum_preagg
    [S :- (Sort 1), inst :- (WSemiring S), K :- (Sort 1), Y :- (Sort 1),
     dec :- (DecidableEq K), g :- (=> Y S), lf :- (=> Y K), k :- K, ys :- (List Y)]
    (= S
       (List.foldl (fn [a :- S] (fn [y :- Y] (WSemiring.add S inst a (g y)))) (WSemiring.zero S inst)
                   (Option.getD (Map.lookup K (List Y) dec k (Map.group_by K Y dec lf ys)) (List.nil Y)))
       (Option.getD (List.lookup K S (instBEqOfDecidableEq K dec) k
                                 (List.map (fn [p :- (Prod K (List Y))]
                                             (Prod.mk (Prod.fst p)
                                                      (List.foldl (fn [a :- S] (fn [y :- Y] (WSemiring.add S inst a (g y)))) (WSemiring.zero S inst) (Prod.snd p))))
                                           (Map.entries K (List Y) (Map.group_by K Y dec lf ys))))
                    (WSemiring.zero S inst)))
    (rw [List.lookup_map_kv])
    (rw [(Option.getD_map (List Y) S
                          (fn [blk :- (List Y)] (List.foldl (fn [acc :- S] (fn [y :- Y] (WSemiring.add S inst acc (g y)))) (WSemiring.zero S inst) blk))
                          (List.nil Y)
                          (List.lookup K (List Y) (instBEqOfDecidableEq K dec) k (Map.entries K (List Y) (Map.group_by K Y dec lf ys))))])
    (try (rfl)))

  ;; foldl_join_frame_generic: THE FAQ FRAME RULE — a SEPARABLE two-sided weight `f(x)·g(y)` over a join
  ;; factorizes through the SAME pre-aggregated index: `Σ_{x⋈y} f(x)·g(y) = Σ_x f(x)·(Σ bucket g)`.
  ;; Generalizes sum_factor (its f≡1 case). The SECOND deep frame generic re-proven THINLY — unblocked
  ;; by the ansatz Miller-pattern unifier fix (commit f6f3557) which lets the HIGHER-ORDER rewrites
  ;; `foldl_add_init_wsem` / `foldl_const_mul_pull` fire on the f(x)-dependent step-λ (previously a
  ;; loose-bvar crash, which had forced fragile explicit-args). Chain: factor → congr → per-key pointwise
  ;; (add_init pulls the acc, const_mul_pull pulls the f(x) factor, bucket_sum_preagg closes).
  (a/deftheorem Map.foldl_join_frame_generic
    [S :- (Sort 1), inst :- (WSemiring S), K :- (Sort 1), X :- (Sort 1), Y :- (Sort 1),
     dec :- (DecidableEq K), f :- (=> X S), g :- (=> Y S), kf :- (=> X K), lf :- (=> Y K),
     e :- S, xs :- (List X), ys :- (List Y)]
    (= S
       (List.foldl (fn [acc :- S] (fn [p :- (Prod X Y)] (WSemiring.add S inst acc (WSemiring.mul S inst (f (Prod.fst p)) (g (Prod.snd p))))))
                   e (Map.join K X Y dec kf lf xs ys))
       (List.foldl (fn [acc :- S] (fn [x :- X]
                                    (WSemiring.add S inst acc
                                                   (WSemiring.mul S inst (f x)
                                                                  (Option.getD (List.lookup K S (instBEqOfDecidableEq K dec) (kf x)
                                                                                            (List.map (fn [p :- (Prod K (List Y))]
                                                                                                        (Prod.mk (Prod.fst p)
                                                                                                                 (List.foldl (fn [a :- S] (fn [y :- Y] (WSemiring.add S inst a (g y)))) (WSemiring.zero S inst) (Prod.snd p))))
                                                                                                      (Map.entries K (List Y) (Map.group_by K Y dec lf ys))))
                                                                               (WSemiring.zero S inst))))))
                   e xs))
    (rw [Map.foldl_join_factor])
    (apply List.foldl_congr)
    (intros b a)
    (simp [])
    (rw [List.foldl_add_init_wsem])
    (simp [])
    (rw [List.foldl_const_mul_pull])
    (rw [Map.bucket_sum_preagg])
    (try (rfl)))

  ;; ── KEY-REWEIGHT (the FD-scope keyfactor) ───────────────────────────────────────────────────────
  ;; lookup_reweight: a per-key weight commutes into the pre-aggregated index —
  ;;   `w(k)·getD(lookup k idx) 0 = getD(lookup k (map (λp.(p.1, w(p.1)·p.2)) idx)) 0`.
  ;; Key-DEPENDENT value map (unlike lookup_map_kv): induction on idx, Prod.eta the head, `by_cases` the
  ;; BEq; the lookup-miss leaf is `w(k)·0 = 0` closed by an explicit-arg `WSemiring.mul_zero` rw.
  (a/deftheorem List.lookup_reweight
    [S :- (Sort 1), inst :- (WSemiring S), K :- Type, dec :- (DecidableEq K), w :- (=> K S), k :- K, idx :- (List (Prod K S))]
    (= S
       (WSemiring.mul S inst (w k) (Option.getD (List.lookup K S (instBEqOfDecidableEq K dec) k idx) (WSemiring.zero S inst)))
       (Option.getD (List.lookup K S (instBEqOfDecidableEq K dec) k
                                 (List.map (fn [p :- (Prod K S)] (Prod.mk (Prod.fst p) (WSemiring.mul S inst (w (Prod.fst p)) (Prod.snd p)))) idx))
                    (WSemiring.zero S inst)))
    (induction idx)
    (all_goals (try (rw [<- (Prod.eta K S head)])))
    (all_goals (simp [List.map_nil List.map_cons List.lookup_nil List.lookup_cons]))
    (all_goals (try (by_cases (BEq.beq K (instBEqOfDecidableEq K dec) k (Prod.fst head)))))
    (all_goals (try (simp_all [Option.getD beq_iff_eq List.lookup_cons])))
    (all_goals (try (rw [(WSemiring.mul_zero S inst (w k))])))
    (all_goals (try (rfl))))

  ;; foldl_keyfactor_float_generic: the THIRD deep frame generic — float a per-key weight `w(kf x)` over a
  ;; foldl into the index (the FD-scope quotient: pre-reweight the index once instead of per row). Thin:
  ;; `apply List.foldl_congr` + per-key `lookup_reweight`. (Also unblocked by the Miller-pattern unifier
  ;; fix, which lets `apply foldl_congr` unify the higher-order step-functions.)
  (a/deftheorem Map.foldl_keyfactor_float_generic
    [S :- (Sort 1), inst :- (WSemiring S), K :- Type, X :- Type,
     dec :- (DecidableEq K), w :- (=> K S), kf :- (=> X K), e :- S, xs :- (List X), idx :- (List (Prod K S))]
    (= S
       (List.foldl (fn [acc :- S] (fn [x :- X]
                                    (WSemiring.add S inst acc
                                                   (WSemiring.mul S inst (w (kf x))
                                                                  (Option.getD (List.lookup K S (instBEqOfDecidableEq K dec) (kf x) idx) (WSemiring.zero S inst))))))
                   e xs)
       (List.foldl (fn [acc :- S] (fn [x :- X]
                                    (WSemiring.add S inst acc
                                                   (Option.getD (List.lookup K S (instBEqOfDecidableEq K dec) (kf x)
                                                                             (List.map (fn [p :- (Prod K S)] (Prod.mk (Prod.fst p) (WSemiring.mul S inst (w (Prod.fst p)) (Prod.snd p)))) idx))
                                                                (WSemiring.zero S inst)))))
                   e xs))
    (apply List.foldl_congr)
    (intros b a)
    (simp [])
    (rw [List.lookup_reweight])
    (try (rfl))))

(defn- do-install!
  "The expensive path: prove + admit the THIN-re-proven FAQ index-family law DAG. Each sub-installer
   guards on the presence of its capstone, so once the laws are already in the env this is a fast no-op."
  []
  (alg/install-classes!)   ;; WAddMonoid ⊂ WSemiring — the carriers the _generic laws + AC providers use
  (bucket/install!)
  (reorder/install!)       ;; count drive-direction reorder (Map.join_length_comm) — aggregate corollary, NO Perm
  (relational/install!)    ;; semijoin / anti-join (membership filter → group_by index probe)
  (grace/install!)         ;; grace-hash spill: List.chunk + flatten_chunk + Map.foldl_join_blockfold
  ;; AC providers for WAddMonoid.add / WSemiring.add — feed `ac_rfl` (the monoid normalizer that
  ;; closes the abstract associativity+identity reshuffles in the `_generic` proofs).
  (ac-providers/register!)
  (install-linearity-laws!)
  (install-factor-pull-laws!)
  (install-agg-frame-laws!)

  ;; Semiring CARRIERS (Nat counting/SUM + Bool provenance). Two thin facts per carrier:
  ;;  (1) the bundled WAddMonoid/WSemiring INSTANCE, kernel-verified ONCE from its axiom row
  ;;      (ansatz.prelude.algebra) — the optimizer emits it BY NAME (`instWSemiring_<C>`), Lean/Mathlib
  ;;      "one instance per carrier"; codegen's reduce_proj-faithful monomorphization lowers it to native ops.
  ;;  (2) the native-op↔carrier RECOGNITION row {:add :mul :zero} — IRREDUCIBLE, because the optimizer
  ;;      reflects over un-instanced surface terms (the user writes `Nat.add`, not `WSemiring.add`).
  ;; Adding a carrier = install-instance! its axiom row + register! its three native ops. (Nat's instance
  ;; is also installed lazily by reorder/install! above; install-instance! is idempotent.)
  (algebra/install-semiring-instance! "Nat" alg/nat-row)
  (algebra/install-semiring-instance! "Bool" alg/bool-row)
  (sreg/register! "Nat"  {:add "Nat.add" :mul "Nat.mul"  :zero "Nat.zero"})
  (sreg/register! "Bool" {:add "Bool.or" :mul "Bool.and" :zero "Bool.false"})
  ;; #184: the group-by-over-join factorization capstone (Map.groupby_reduce_join_factor) the
  ;; `try-groupby-reduce-join` recognizer instantiates. requiring-resolve avoids a load-order cycle.
  ((requiring-resolve 'wandler.laws.groupby-join/install!))
  :installed)

(defonce ^{:private true
           :doc "The proven law DAG, captured ONCE per process. The first `install!` snapshots the
                 constants the proof installers admit; later calls (a fresh env per test namespace, or a
                 second `w/install-laws!`) re-CHECK those cached proof terms instead of re-running the
                 tactic proofs. `check-constant` is the same kernel gate, so seeding is exactly as sound
                 as proving — only ~1000× faster (seconds → ~20ms)."}
  installed-cis (atom nil))

(defn- seed!
  "Re-check cached law proof terms into the current env (skipping any already present), retrying across
   passes so inter-law dependencies resolve regardless of order. A term that never checks (a missing
   dependency, a divergent env) is left for `do-install!` to reprove — the cache only ever speeds things
   up, never changes the result (every adopted constant still passes the kernel `check-constant`)."
  [cis]
  (loop [pending (remove #(env/lookup (a/env) (env/ci-name %)) cis)]
    (let [{:keys [stuck progressed]}
          (reduce (fn [acc ci]
                    (if (env/lookup (a/env) (env/ci-name ci))
                      acc                                   ; present already (a carrier or a just-seeded dep)
                      (if (try (swap! a/ansatz-env env/check-constant ci) true
                               (catch Throwable _ false))
                        (update acc :progressed conj ci)
                        (update acc :stuck conj ci))))
                  {:stuck [] :progressed []} pending)]
      (when (and (seq stuck) (seq progressed)) (recur stuck)))))

(defn install!
  "Admit the THIN-re-proven FAQ index-family laws into the global env (idempotent). Builds on
   `bucket/install!` (the dependency closure: kmap + plist + frame + the `Map.join_eq` rfl lemma the
   join factor/count laws rewrite with, plus the aggregate `Map_aggJoin_*` cluster). Each `theorem`
   form is kernel `check-constant`-verified as it lands. The law proofs are split across three
   sub-installers (JVM method-size limit).

   CACHED per-process: the first call proves the DAG and snapshots the admitted constants; subsequent
   calls (each test namespace resets to a fresh env) re-CHECK those proof terms — seconds → ~20ms —
   leaving anything that fails to seed for a full reprove, so the result is never cache-dependent.
   Returns :installed."
  []
  (if-let [cis @installed-cis]
    ;; FAST PATH: re-create the carrier inductives (WAddMonoid/WSemiring — not `check-constant`-able) so
    ;; carrier-typed proof terms type-check, seed the cached proofs (their presence makes every
    ;; sub-installer guard short-circuit), then `do-install!` runs as a fast guarded no-op.
    (do (alg/install-classes!)
        (seed! cis)
        (do-install!))
    ;; SLOW PATH (first call this process): prove for real, then snapshot the admitted constants.
    (let [before (into #{} (map (comp str env/ci-name)) (env/all-constants (a/env)))]
      (do-install!)
      (reset! installed-cis
              (into [] (remove #(before (str (env/ci-name %)))) (env/all-constants (a/env))))))
  :installed)
