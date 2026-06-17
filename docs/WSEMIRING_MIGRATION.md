# Migrating the generic frame-family laws to `[s : WSemiring S]` (Phase 3)

Goal: collapse the 8 generic semiring laws from 6 bare axiom-hypothesis params to ONE typeclass
instance, lean-wandler-thin, with no loss of functionality. Built on ansatz `a/structure :extends`
+ `wandler.semiring-class` (WAddMonoid ⊂ WSemiring, both verified-instance-capable).

## The thin shape (per law)

A law currently binds `S, add, zero, [mul], hAA, hZA, hAZ, [hMA, hMZ, hZM]` as forall binders,
intros them, and the proof retrieves each by name into a local (`addp (gf psg "add")` …). The migration:

- **Goal telescope:** replace the algebra binders with `(S : Type)` + `(inst : WClass S)` — 2 binders.
  Monoid-only laws (foldl_add_init, foldl_join_sum_factor) → `WAddMonoid`; laws needing `mul` →
  `WSemiring`.
- **Construction-time ops:** set `addF = (WClass.add S inst)`, `zeroF = (WClass.zero S inst)`, … as
  projections of the inst fvar, so the goal conclusion is built over the projections automatically.
- **`intros`:** `["S" "inst" <value params…>]`.
- **Proof body — KEY, low-churn:** the body uses LOCALS (`addp`, `zerop`, `haa`, …) that were set
  from `(gf psg "add")` etc. Only those binding lines change — rebind each local to the projection of
  `(gf psg "inst")`:
    addp = (WClass.add Sp instp), zerop = (WClass.zero Sp instp),
    haa  = (WClass.add_assoc Sp instp), hza = (WClass.zero_add Sp instp), haz = (WClass.add_zero Sp instp),
    mulp = (WSemiring.mul Sp instp), hma = (WSemiring.mul_add …), hmz = (WSemiring.mul_zero …),
    hzm  = (WSemiring.zero_mul …).
  The rest of the proof (which uses the locals) is UNCHANGED. Projections are `:abbrev` so
  `WSemiring.add s` defeq-unfolds to `WAddMonoid.add (toWAddMonoid s)` — the inherited axioms line up.

## The two application sites (per law)

1. **Concrete carrier wrapper** in frame.clj (e.g. prove-foldl-add-init, line ~139):
   `(e/app* pGen natT Nat.add Nat.zero Nat.add_assoc …)`  →  `(e/app* pGen natT (mk-instance natT nat-row))`.
2. **Optimizer emitter** in `optimize/physical.clj` (try-frame-sum-factor 321, try-frame-index 442,
   try-frame-index-cond 612/622, try-frame-index-keyfactor 661/672):
   `(e/app* law S (sr-c entry :add) … 6 consts …)`  →  `(e/app* law S (mk-instance S entry))`.

`mk-instance` builds the `WClass.mk` term inline from a registry row (add it to
`wandler.semiring-class`): WAddMonoid.mk S add zero hAA hZA hAZ  /  WSemiring.mk S <am-inst> mul hMA hMZ hZM.

## Ordering / prerequisites

- `wandler.laws.relational/install!` must call `wandler.semiring-class/install-classes!` BEFORE
  `build-all` (the generic-law proofs reference `WClass.*` projections). Add the require + call.
- **Store caveat:** the registry Nat row uses `Nat.mul_add`, ABSENT in init-medium (present in the
  full store). Switch the registry Nat `:hMA` to `Nat.left_distrib` (same statement, core name,
  present everywhere) as a prep step so WSemiring Nat instances verify on every store. Verify the
  optimizer tests' store before relying on `Nat.mul_add`.

## Dependency order (leaf-first, suite-gate each)

Internal proof deps: `bucket_factor_pull → foldl_const_mul_pull`, `keyfactor_float → lookup_reweight`
(a migrated law's RESULT is applied inside its dependent's proof, so migrate the leaf + update the
dependent's internal application together). Suggested order:
1. foldl_add_init (WAddMonoid, leaf, no emitter) — proves the recipe.
2. foldl_join_sum_factor (WAddMonoid, emitter try-frame-sum-factor).
3. lookup_reweight (WSemiring-mul) → then keyfactor_float (applies it).
4. foldl_const_mul_pull (WSemiring) → then bucket_factor_pull (applies it).
5. cond_and_mul_split (WSemiring), foldl_join_frame (WSemiring, the big assembly) + its emitters.

Gate: `clj -M:local-ansatz:test` (whole wandler suite) green after EACH law. Never leave a law's
signature changed without its two application sites updated in the same commit.

## Status
Recipe captured; infra (classes, instances, mk-instance) is the first concrete step. Laws not yet
migrated — execute incrementally per the order above.
