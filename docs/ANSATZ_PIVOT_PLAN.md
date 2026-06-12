# Wandler ⇐ Ansatz pivot — implementation plan

**Status**: authored 2026-06-11, against ansatz `feature/clj-ingest` @ `e934e24`
(post elaborator-unification, post WF-termination completion). Wandler consumes
ansatz via `:local/root "../ansatz"`, so this branch's changes apply immediately.

**Context**: ansatz just completed two large arcs that change wandler's foundation:

1. **Kernel-enforced termination everywhere** — structural, `:termination-by`
   (scalar / lexicographic `[m n]` / `(sizeOf xs)`), auto-measure (GuessLex incl.
   lex pairs and sizeOf), `loop`/`recur` hoisting, custom-inductive `SizeOf`
   auto-derivation, per-leaf `fix_eq` defining equations that simp consumes.
   `^:partial` remains the only trusted lane; everything else carries its proof
   in the kernel term.
2. **One elaborator** — the bvar `sexp->ansatz` is deleted (~680 lines).
   `ansatz.surface.elaborate` (fvar/metavar, lean4-shaped) elaborates bodies,
   signatures, measures, theorem statements, tactic arguments, and user
   extensions. Implicit + universe inference now works mid-form, e.g.
   `(List.map f xs)` infers `{α β}` and levels from the arguments alone.
3. **`register-elaborator!` is reborn** lean4 `macro_rules`-shaped:
   `(fn [arg-forms] → surface-form)`, registry in `ansatz.surface.ingest`,
   expanded by `elab-term` before its own dispatch. The old
   `(fn [env scope depth args lctx] → Expr)` contract is gone.
4. **Surface `if` over comparisons emits `dite`** (the lean4 `macro_inline` /
   `Decidable.casesOn` shape). Branch binders carry the guard hypothesis;
   `Bool.rec` remains only for non-comparison Bool conditions.

Three latent correctness bugs were found during the work (nested-match IH
conflation; recursor-rule level-param mismatch breaking ALL symbolic defeq on
custom inductives; silent gate gaps) — all invisible to closed-value testing.
This plan treats **differential testing as a first-class lane** in response.

---

## The lifting story (the contract wandler builds on)

Resolution order for `(head args…)` in the single elaborator:

1. **Registered surface forms** (`register-elaborator!`, syntax → syntax).
2. **Built-in forms**: binders, `match`, `if`(→`dite`/`Bool.rec`), `dif`,
   `loop`, `do`, `cond`, `sizeOf`, comparisons, `=`→`Eq`, type-directed
   arithmetic (`+ - *` via `ingest/arith-lift` keyed on the inferred operand
   type-head).
3. **Sugar**: `(:k s)` projection, `(get s :k)`, `(cons x xs)`.
4. **Clojure macros expand by default** (`resolve` → `:macro`, minus
   `no-expand-macros`): `->`, `when`, `and`/`or`, user macros compose free.
5. **Generic application**: scope fvar | env constant by exact name, with
   implicit/universe inference.
6. Otherwise an honest "Unknown constant" error.

**Principle**: Clojure lifts by *macro expansion + curated verb table + env
constants* — never by reflecting on arbitrary JVM functions. Functions without
kernel semantics either get a lift (with laws), enter as **typed axioms**
(the datahike-API pattern: trusted oracle behind a typed boundary), or are
honestly rejected. `(clojure.core/update-in …)` does not silently "work".

---

## Breakage inventory (wandler @ `fda7261` vs new ansatz)

| API | Status | Wandler usage | Action |
|---|---|---|---|
| `a/register-elaborator!` | **contract changed** | ~20+ verb elaborators in `collections.clj`, `relational.clj`, `records.clj`, `edn.clj`, `stream_surface.clj`, `gradual.clj`, `pipeline.clj` | re-port (phases W1–W2) |
| `#'a/sexp->ansatz` (private var refs) | **deleted** | 7 files (inside the old-contract elaborators) | dies with the re-port |
| `a/build-telescope*` internals | **deleted/changed** | 4 files | dies with the re-port |
| `*scope-types*` | **deleted** | 2 files | dies with the re-port |
| `a/get-arg-type` | survives | 7 files | keep; prefer inference where possible |
| optimizer law spellings (`Bool.rec` if-forms) | **canonical spelling moved to `dite`** | `optimize*`, `rel_laws`, simp-lemma statements | W3 triage: normalize or restate |

---

## Phases

### W0 — compile triage + extension-point decision (½ day)
- Get `clj -M:test` running against new ansatz; stub-disable the broken
  `install!` namespaces to chart the real breakage (expect the table above).
- **Decision to make first** (small ansatz PR if accepted): extend the registry
  to *two tiers*, mirroring lean4 exactly:
  - `macro_rules` tier (today's contract): `(fn [args] → surface-form)`.
  - `elab_rules` tier (new, optional): `(fn [est args] → Expr)` for the few
    verbs that must *inspect inferred types to choose different lowerings*
    (not just construct one). `est` gives `elab-term`, `infer-with-mvars`,
    `zonk` — the supported elaboration API.
  Most wandler verbs will NOT need the second tier (see W1); add it only when
  a concrete verb demands it.

### W1 — collections verbs (1 day)
The unification makes most of `ansatz.collections` collapse:
- `(mapv f xs)` → rewrite `(List.map f xs)` — implicits/universes infer. One line.
- Same for `filterv`→`List.filter`, `count`→`List.length`, `reduce`→`List.foldl`,
  `map-indexed`→`List.mapIdx`, `concat`→`List.append`, etc.
- Transducer arities (`(map f)`, `(filter p)`) and the `comp` pipeline forms are
  *syntax-shape* rewrites — still macro_rules tier.
- The old hand-computed `univ`/`list-elem` type plumbing is deleted, not ported.
- **Acceptance**: collections tests green; the diff is strongly negative in LOC.

### W2 — relational / records / edn / stream / gradual verbs (2–3 days)
- `relational.clj`'s ~15 verbs (`group-by`, `sort-by`, `frequencies`, `aput`…):
  most are rewrites to kernel constants; `sort`/`sort-by` may need the
  elab_rules tier (comparator instance choice by element type) — first real
  test of the W0 decision.
- `records.clj` (`assoc`/keyword access over Malli-schema'd records): keyword
  projection is already a core builtin; check overlap, port the rest.
- `edn.clj` `Value`-universe verbs; `stream_surface.clj` (typed Strm routing);
  `gradual.clj` front-door forms.
- **Acceptance**: each namespace's own test file green before moving on.

### W3 — optimizer/laws spelling triage (1–2 days, risk item)
- The optimizer and rel_laws match on term *spellings*. Two moves:
  1. Adopt **`dite` as the canonical if-spelling** in laws/matchers (it is the
     lean4 shape); keep a one-way `Bool.rec`→`dite` normalizer at the optimizer
     boundary for old stored terms.
  2. Re-run the law/optimizer suites; restate any law whose LHS no longer fires.
- This is also the natural moment for wandler's standing "boundary
  normalization" item (shape-matching rewrites fire on any spelling).

### W4 — the malli type surface MOVES TO ANSATZ (decision 2026-06-11) (3–4 days, ansatz-side)
**Boundary principle (revised)**: ansatz owns what a definition MEANS (type,
termination, faithfulness); wandler owns how it RUNS FAST (rewrites, plans,
modes, engines). Malli schemas determine meaning ⇒ the schema→type surface is
ansatz language, not wandler runtime. Also forced by dependencies: refinement
bounds are consumed by ansatz's WF decrease machinery (no circular dep).

Ansatz-side (new `ansatz.malli`; `metosin/malli` becomes an ansatz dep):
- **Schema→kernel-type translation** for signatures: scalars→Nat/Int/Bool/
  String, `[:sequential]`/`[:vector]`→List, `[:map]`→record structure,
  `[:maybe]`→Option, `[:int {:min/:max}]`→Subtype refinements.
- **`a/defn` reads malli's EXISTING function-schema idioms** — `m/=>`
  declarations / `:malli/schema` metadata — so the Clojurian porting story is
  a one-token diff: `defn` → `a/defn`, schemas unchanged. The gradual ladder:
  plain `defn` → `defn`+`m/=>` (runtime checks) → `a/defn`+same schema
  (kernel-verified) → refinements tighten proofs for free.
- **Refinement hypotheses in termination**: `[:int {:min 1}]` param ⇒ Subtype;
  measure `.val`, inject `.property` into decrease-proof scopes (they already
  carry Props). Unlocks `(f (- n step))` with `step ≥ 1` from the schema.
- **Differential lane as part of the definition contract** (opt-in flag on
  `a/defn`): schema generators produce inputs; assert compiled-runtime ≡
  kernel-whnf (≡ reference Clojure where given). The built-in guard for the
  "well-typed but source-unfaithful" bug class found three times in one session.

Stays in wandler (applications OF schemas, not the reading of them): the
conformance compiler (schema → verified `Value` predicate), record relational
laws, generative pipeline testing against the optimizer.

Also in W4 (small ansatz PRs):
- **Namespace story**: a/defn registers the qualified alias alongside the bare
  name; `resolve-const` tries verbatim, then bare.
- Parameterized-container `SizeOf` (`Tree α`) when a concrete need appears.

### W5 — cleanup + landing (1 day)
- Delete the dead hand-typed builders, the disabled stubs, the old contract docs.
- Update `CORE.md` §elaboration to point at the lifting story above.
- Sync with the ansatz PR (below); pin the ansatz dep once it merges.

---

## Design positions (opinions, held after this work)

1. **Two-tier extensions, lean4 names**: macro_rules for rewrites, elab_rules
   for type-directed lowering. Resist a third tier; if a verb needs more than
   `est`, it is an optimizer/law concern, not elaboration.
2. **Make the trust ladder visible**: (a) definitional lifts → (b) law-certified
   rewrites → (c) typed axioms (engine oracles) → (d) `^:partial`. Wandler's
   gradual front door should *report* which rung each definition sits on.
2b. **The malli type surface belongs in ANSATZ; the verb table in wandler.**
   The boundary: what a definition MEANS (type, termination, faithfulness) is
   ansatz; how it RUNS FAST is wandler. Malli-as-signatures is the gradual
   dependently-typed on-ramp for Clojurians and must sit upstream of the WF
   machinery that consumes refinement bounds. See W4.
3. **Runtime/kernel duality is a feature**: the compiled Clojure runs the
   surface-faithful program; the kernel constant carries the proof. Keep them
   separate and *differentially tested* — never let the optimizer rewrite the
   runtime without the certificate (this is already wandler's verified-rewrite
   gate; extend it to the new dite spellings in W3).
4. **Differential testing is not optional**: three latent bugs in one session
   were invisible to the kernel (it checks types, not source-faithfulness) and
   to closed evaluation. Schema-driven generation + runtime/kernel comparison
   catches exactly this class. Budget it as real work (W4), not as an
   afterthought.
5. **Faithful-first pays off measurably**: every shortcut replaced by the lean4
   mechanism this session (dependent casesOn motives, dite guards, fix_eq
   equations, macro_rules) deleted code and removed special cases. When in
   doubt, port the lean4 design before inventing.

---

## Ansatz-side wrap-up (PR checklist for `feature/clj-ingest`)

~25 commits: WF termination (kernel-enforced, lex, sizeOf, loop/recur,
custom-inductive SizeOf), elaborator unification P1–P5, three correctness
fixes (nested-match IH, recursor-rule levels, gate gaps), omega robustness
(Nat.sub/Nat.lt spellings), preludes (lex, sizeOf).

Before opening the PR:
- [ ] remove now-dead `wf-fix-ite?` / `wf-fix-ite->dite` / `wf-fix-eq-rhs`
      Bool.rec-conversion (one commit, suite-gated)
- [ ] optional: non-comparison Bool `if` → `b = true` coercion (retires
      Bool.rec from `if` entirely; can defer)
- [ ] `clj -M:test` green (452+) + `clj -T:build javac` clean
- [ ] squash-review the WF debug commits if a tidy history is wanted (or keep —
      each is suite-gated and self-documenting)
- [ ] PR body: the three bug write-ups deserve prominent placement; they are
      the strongest argument for the unification
