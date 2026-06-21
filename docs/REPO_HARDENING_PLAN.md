# Repo Hardening Plan — getting wandler into very good shape

Status as of 2026-06-20 (branch `rethink-dev-experience`). No release rush — the
goal is a repo that is *clean, honest, and ergonomic*, not a date. Soundness is
already done: every adopted optimization is independently `check-constant`
certified, the public surface (`wandler.core`) reaches only `wandler.clean.*`,
and both suites are green (ansatz 485/0, wandler 354/1608/0). What remains is the
cleanup tail of the strangler migration plus ergonomics.

This plan covers four tracks (A–D) sequenced into phases, plus a **Phase 0
(ansatz release)** that gates the wandler-side registry work. Each task has
file/line pointers and a verification step. Work top-to-bottom; every phase ends
green on both suites.

This spans **two repos**: `../ansatz` (the kernel DSL) and `wandler`. Phase 0 is
all ansatz; Phases 1–6 are wandler with one ansatz dependency (the `install-law`
helper, which ships in the Phase-0 ansatz release).

Legend: ☐ todo · ◐ in progress · ☑ done. Effort: S(<1h) · M(half-day) · L(multi-day).

---

## Phase 0 — Ansatz release (the kernel DSL) · gates Phase 3

`rethink-dev-experience` is **92 commits ahead of `main`**: the entire thin-surface
infrastructure (Miller HO-unify, `ac_rfl`, `rw [..]` brackets, cases/induction
recursive-field + Eq-revert fixes, `generalize`/`subst_vars`, split S1–S6, simp
instance synthesis, elab binder-zonk, the owned big-operator prelude). wandler pins
`org.replikativ/ansatz 0.1.60`; this cuts the next release. Do this FIRST so the
`install-law` helper (0.1) is available to wandler against a published pin, not just
`:local-ansatz`.

### 0.1 Add the registry helpers — M — ☑ (ansatz core.clj; suite green 485/1248/0)
Shipped THREE primitives (ansatz suite stays green):
- `install-theorem!` (fn) + `deftheorem` (macro) — idempotent, non-swallowing literal-form install.
- `install-guarded!` (macro) — idempotent, non-swallowing guard for PROGRAMMATIC installs
  (raw-term `mk-def`/`admit!`/generated forms) that don't fit `deftheorem`.
- `has-constant?` + `*install-ledger*`. Smoke-verified: admit/idempotent/re-raise/lenient-ledger.
- Lives in `ansatz.core` (alongside `prove-theorem` @1775 + `theorem` macro @1948).
  Currently there is NO idempotent, non-swallowing install primitive — that gap is
  exactly why wandler grew 86 `(try (eval …) (catch Throwable _ nil))` blocks.
- Contract: `has?`-guarded (idempotent), registers on success, **re-raises on proof
  failure by default**; an explicit `:lenient` mode records `{:name … :error …}` into
  a per-install ledger the caller can surface (admitted-vs-skipped counts). Drops the
  redundant `eval` for literal `theorem` forms; keep an `eval`/thunk path only for
  programmatically-built variadic forms.
- Study `../lean4` `Environment`/`addDecl` + the import DAG: Lean fails loudly at
  elaboration; our runtime-install equivalent is re-raise + a startup ledger.
- **Verify:** ansatz suite green; a deliberately-broken proof re-raises; a duplicate
  install is a no-op.

### 0.2 Cut the ansatz PR + release — ☑ PR OPEN (release on merge)
PR opened: replikativ/ansatz#44 (`rethink-dev-experience` → `main`, 93 commits, themed
description). CI runs on the PR; CircleCI deploys (Clojars) + GitHub-releases only on
merge to `main` — owner-driven, not automated here.

### 0.3 Bump wandler's pin — ☑ DONE (0.1.60 → 0.1.61, commit b9fbd02)
PR #44 squash-merged + released as **0.1.61**. Pin bumped; wandler compiles + frame-test
passes against the PUBLISHED jar (helpers confirmed in-jar). Full suite green on identical
code (355/1609/0). NB: some integration tests (`faq-plan-test` etc.) error when run in
ISOLATION (`ClassNotFoundException: List.foldl` — unpopulated surface-registry, the known
test-isolation quarantine, pin-independent); they pass in the full suite. `:local-ansatz`
remains for unreleased-feature dev.

### 0.2-orig Cut the ansatz PR + release — (superseded; see 0.2 above)
- Open PR `rethink-dev-experience → main` for ansatz with a curated description
  grouping the 92 commits by theme (unify · tactics · simp · prelude · elab).
- Confirm ansatz suite green (`clj -M:test`), `clj -T:build javac` clean.
- Version auto-derives `0.1.<git-count-revs>`; tag + release (Clojars). Decide:
  squash-theme vs merge-commit (recommend merge — the commit history is good and
  MEMORY references specific SHAs).
- **Verify:** new jar resolves; `lean_verify`-style smoke (a known theorem checks).

### 0.3 Bump wandler's pin — S — ☐
- `../wandler/deps.edn:7` `0.1.60` → the new release; keep `:local-ansatz` for dev.
- **Verify:** wandler suite green against the published pin (not just local).

**Phase 0 gate:** ansatz released with the helper; wandler builds green on the new pin.

---

## Phase 1 — Surface correctness (Track A1/A3/A4) · the user-facing lies

The repo currently *misleads a new user or maintainer*. Fix that first.

### 1.1 README quickstart is a hard load failure — S — ☐
- `README.md:39-40`: `(require '[wandler.laws.relational :as laws]) (laws/install!)`
  → that namespace is **deleted**. The documented first run fails to load.
  Repoint to the live install path (`wandler.core/install!` or the clean faq
  installer reached by `surface.streams`). Verify the exact public entry point
  before editing — `wandler.core/install!` is the intended front door.
- `README.md:124-150` layout table: documents the pre-strangler `wandler.surface.*`
  / `wandler.optimize.*` / `wandler.laws.*` tree. Rewrite the table to the actual
  reachable layout (clean tree canonical; `optimize.plan` is the live IR lens;
  `laws.semiring` is the carrier registry, not "laws").
- Stale stats: `README.md` Status block says `335 tests / 1522 assertions`;
  actual is `354 / 1608`. Regenerate from a real run.
- **Verify:** copy each README code block into a fresh REPL with the store
  mounted; every block must load and run.

### 1.2 Stale docstrings naming deleted namespaces — S — ☐
Code works; comments lie about install requirements. Fix each:
- `src/wandler/semiring_class.clj:88` — "require `wandler.laws.relational` / `.tropical`"
  → `relational` deleted; point at the clean carrier installers.
- `src/wandler/exec/dbsp.clj:319` — "Requires kmap/install! + **rel-laws**/install!"
- `src/wandler/surface/streams.clj:311` — "kmap/**rel-laws**/dbsp are installed first."
- `src/wandler/laws/semiring.clj:3` and `src/wandler/laws/tropical.clj:14` —
  reference `wandler.optimize.physical` (deleted; clean path is `wandler.clean.optimize.physical`).
- `src/wandler/gradual.clj:7` — "Three entry points over `wandler.optimize`" → `wandler.clean.optimize`.
- `src/wandler/inference/semiring.clj:127` — "what `wandler.optimize.faq` rides on" (verify; `optimize.faq` is vestigial).
- **Keep (NOT stale):** every `wandler.optimize.plan` reference — that ns is live.
- **Verify:** `grep -rn "laws.relational\|rel-laws\|optimize.physical\|over \`wandler.optimize\`" src/`
  returns only intentional historical mentions.

### 1.3 Vestigial namespaces — investigated; the review OVER-FLAGGED — S — ☑ (keep all)
Hands-on check (grep src vs test requirers) overturned the review's "delete these":
- `src/wandler/plan.clj` — NOT a deletion candidate. It is "Integration 1: the unified
  consumer-aware planner" exercised by **6 active tests** (`unified_plan_test`,
  `cross_engine_{source,capstone,pushdown}_test`, `planner_demo_test`, `plan_test`).
  A real, tested planner facade over the live `wandler.optimize.plan` lens. **Keep.**
- `src/wandler/optimize/faq.clj` — the semiring-query → certified-optimizer bridge,
  tested by `faq_plan_test`. No src requirer, but a meaningful integration surface,
  not dead code. **Keep.**
- `src/wandler/tools/reducer_bench.clj` — a standalone `:gen-class` dev bench under
  `tools/`. Harmless; doesn't masquerade as surface. **Keep** (optional: relocate to `dev/`).
- **Keep (confirmed live):** `wandler.optimize.plan` (IR lens), `wandler.surface.{vocabulary,streams}`,
  `wandler.laws.semiring` (carrier registry), `wandler.laws.{tropical,dist}` (opt-in carriers).
- **Conclusion:** no namespace deletion. The cleanup here is labeling/docs (Phase 4), not removal.

**Phase 1 gate:** fresh-clone README walkthrough works; no stale ns refs in `src/`; both suites green.

---

## Phase 2 — Test-coverage honesty (Track A2) · the green-but-empty mirage

`test-data/` is a gitignored symlink to `../ansatz/test-data`; `test/wandler/test_env.clj`
returns `nil` with no store. ~104 of ~118 test files guard on `(ready?)` and degrade
to `(is true "SKIP")` or **zero assertions**. A storeless clone/CI passes green while
testing almost nothing. The 354/1608 number is meaningful *only* with the store mounted.

**Store reality (measured 2026-06-20):** nothing is git-tracked but tiny fixtures;
everything real is gitignored. Sizes: `init-small.ndjson` 829K, `init-medium.ndjson`
3.2M, `init.ndjson` (full) 96M, `init-store/` (full PSS) 173M. **Decisive fact:**
**269** test references bind `init-full-env`; only **4** use `init-medium-env`. So
shipping small/medium alone does NOT un-skip the integration suite — those 269 tests
need full Init, which is not git-shippable. (And `init-small` is too thin regardless;
if we ship a git fixture it's `init-medium`.)

### 2.0 CI honesty gate — S — ☑ (test/wandler/store_gate_test.clj)
`wandler.store-gate-test`: prints a loud banner when the store is absent (never silent
green); with `WANDLER_REQUIRE_STORE=1` (CI) a missing store is a HARD FAILURE. Verified:
passes store-present (±env var); fails store-absent+env var; banners store-absent local.
This is the mechanism — the items below wire it / widen coverage and are the remainder.

### 2.2 On-demand fetch + local PSS cache — ☑ (test_env.clj, commit 6939dca)
The store-shipping mechanism (your release-asset + cache design): `init-full-env` resolution
gains (3) reuse a previously-fetched `$XDG_CACHE_HOME/wandler/init-store` cache and (4) OPT-IN
`WANDLER_FETCH_INIT=1` → download `init.ndjson` from `WANDLER_INIT_URL` (default the ansatz
0.1.61 release) → import to the cache once. Compile + local-store resolution verified; failures
degrade to nil (gate makes it loud). **Remaining ops step (yours): attach `init.ndjson` to a
release** (it's Init-only ~96M, NOT Mathlib; init-medium too thin — lacks List.Nodup). A curated
slice (~10M, just the constants the suite touches) is an optional later optimization.

### 2.1 Make storeless runs honest — ☑ (gate + loader) — **decision point resolved**
Three composable pieces (recommend **B now + C as the real-coverage follow-up**):
- **A. Git-track `init-medium` (3.2M)** + migrate a meaningful subset of the 269
  tests onto `init-medium-env` where they only need core lemmas → a genuine CI
  smoke slice without provisioning. (small is too thin; medium is the floor.)
- **B. Hard-fail gate** — a single env probe at suite start: if `WANDLER_REQUIRE_STORE=1`
  (set in CI) is on and the store is absent, the suite *errors* instead of silently
  passing. Locally without the flag, integration tests skip but **print a loud banner**
  with a skipped-count summary so the number is never mistaken for coverage.
- **C. Provision full Init in CI** — cache/release-asset the 96M `init.ndjson` (or
  build the 173M PSS), run the full integration job nightly or on a labeled CI lane.
- Recommend **B now** (cheap, kills the mirage), then **A** for a cheap always-on
  smoke slice, then **C** for full coverage on a heavier lane. They compose.

### 2.2 Replace silent `(is true "SKIP")` with counted skips — S — ☐
- Audit the ~104 guarded files; standardize on a shared `skip-unless-store` helper
  that records a skip (so the runner reports "N integration tests skipped — no store")
  rather than emitting a passing assertion. Keeps the assertion count honest.
- **Verify:** storeless run prints an explicit skipped-tests summary and a non-misleading
  assertion count; stored run unchanged.

### 2.3 (Optional, later) Un-defer `test-deferred/` — L — ☐
28 namespaces parked off the `:test` path. Primary blocker = global-registry
test-isolation (surface/codegen registries + kernel env are global atoms leaking
across namespaces in one JVM). Build a shared snapshot/restore fixture
(model: `test-isort-preservation`, `env/fork` + try/finally). Secondary blockers
are genuine open features (WF-fix runtime over custom inductives, `veq` partial,
double[] tier, reducers prove-pipeline) — leave those deferred. Tracked, not a blocker.

**Phase 2 gate:** no test path silently no-ops; CI either runs integration or fails loudly; skip counts visible.

---

## Phase 3 — Registration hygiene (Track B5) · un-hide proof failures

86 `(when-not (has? "X") (try (eval '(ansatz.core/theorem …)) (catch Throwable _ nil)))`
blocks across 22 files (`clean/laws/faq.clj` alone has 23). The `catch _ nil`
silently swallows proof failures — a broken proof becomes a silent missed
optimization (perf regression), invisible to the suite. This *is* the bug behind
the 2 silent law-drops in the cutover.

### 3.1 Design the `install-law` / `deftheorem` helper — M — ☐
A single form in `ansatz.core` (or `wandler` util) that:
- takes a theorem name + the `theorem` form (or a thunk producing it),
- guards on `(has? name)` for idempotency,
- on success registers and (optionally, under `*verbose*`) logs admission,
- on failure: **re-raises by default**, or under an explicit `:lenient` / strict-mode
  flag records `{:name … :error …}` into a per-install ledger that the installer
  surfaces as an admitted-vs-skipped count.
- drops the redundant `eval` for *literal* `theorem` forms (the macro already
  expands to a `prove-theorem` call); keep `eval` ONLY for programmatically-built
  variadic forms (e.g. `bucket_content_gen` in `clean/laws/bucket.clj:66`).
- Study `../lean4` `Environment`/`addDecl` + the import DAG for the faithful model:
  Lean fails loudly at elaboration time; we install at runtime (store load), so the
  loud-failure equivalent is re-raise + a startup ledger.

### 3.2 Mechanical migration — ◐ (done, suite-verify pending)
Outcome (52 swallow-sites migrated; the other ~34 `catch Throwable _ nil` are LEGITIMATE
defensive type-inference/whnf probes in the optimizer — correctly left):
- 48 literal-theorem installs → `deftheorem` via a paren-aware transformer (8 law files:
  faq 23, relational 8, bucket 6, frame 3, monoid 3, reorder 2, grace 2, par 1).
- 4 programmatic installs → `install-guarded!` (reorder `instCommNatAdd`, grace
  `Map.join.eq_unfold`, bucket `bucket_content_gen`, + the `(when-not (has?) (admit!))`
  no-catch sites already non-swallowing, left as-is).
- **Bug surfaced & fixed:** faq `install!` with 23 inlined `deftheorem` expansions blew the
  JVM 64KB method limit → split into 3 private sub-installers by section.
- **Deferred-feature surfaced:** `par/parFold` (fragile brecOn recursion encoding, the known
  ansatz gap) genuinely fails to elaborate → its swallow was INTENTIONAL; switched to
  lenient+LOUD (logs the deferral, doesn't crash or silently swallow). NOT `install-guarded!`.
- Smoke: `install-laws!` runs clean end-to-end against the store (no law re-raised).

### 3.2-orig Mechanical migration of the 86 blocks — L — (superseded by 3.2)
Per file, replace the pattern with the helper. Order by dependency leaf-first:
`plist`/`kmap` → `frame` → `bucket` → `faq` → `relational`/`reorder`/`grace` →
optimize/{physical,egraph,cse,certify} → surface/* → exec/*.
- **Verify after each file:** the law set admitted is identical (diff `has?` names
  before/after); both suites green. A strict-mode run admits every currently-green law.

### 3.3 Add a strict install self-check — S — ☐
A dev/test entry that runs every installer in strict mode and asserts zero
swallowed failures — so a future proof regression is caught, not hidden.
- **Verify:** new test passes today (proves no currently-swallowed failure exists);
  intentionally breaking one proof makes it fail loudly.

**Phase 3 gate:** no `catch Throwable _ nil` around proofs in `src/`; strict self-check green; suites green.

---

## Phase 4 — Docs sweep (Track C6) · describe the migrated world  ◐ (mostly done)

Architecture docs describe the pre-migration layout. Archive or rewrite.

**Done:** archived `WSEMIRING_MIGRATION.md` + `COHESION_AUDIT.md` to `docs/archive/`
(+ a README); added a "shipped" header to `COST_MODEL_REDESIGN.md` (kept — referenced);
fixed `DEPENDENT_TYPES.md` ns-ref; **wrote the two missing conceptual docs**
`PROGRAMMING_MODEL.md` (four-structure spec, §2/§12/§13 land where the ~10 source refs
cite) and `SPILL_AND_FAQ_PLAN.md` (the physical strategy ladder). **Remaining:**
regenerate `SURFACE.md` from the clean vocabulary (needs `dev/gen_surface_md.clj`); a few
conceptual `optimize/verified-rewrite?` shorthands in CORE.md (low-harm).

### 4.1 Archive superseded plans — S — ☐ (refined: only 2 are dead)
Hands-on link audit overturned part of the review:
- `WSEMIRING_MIGRATION.md` + `COHESION_AUDIT.md` — truly dead (no source roadmap
  refs; README ref already removed in Phase 1). → archive to `docs/archive/`.
- `COST_MODEL_REDESIGN.md` — **KEEP.** It exists AND is actively referenced as a
  live roadmap by source (`clean/optimize/cost.clj:286` §4, `exec/physical.clj:90`
  B2, `backend/raster.clj:126`, `jit/stream.clj`, BENCHMARKS, 2 tests). Add a
  "shipped as wandler.clean.optimize.cost; §4/B2 still roadmap" header note instead.

### 4.1b Create the referenced-but-missing conceptual docs — M — ☐ (new finding)
Two docs are cited widely but don't exist (dangling, not just stale):
- `PROGRAMMING_MODEL.md` — ~10 source docstring refs (§2 semiring, §12 lens,
  §13 ∂/FAQ) + CORE/LANGUAGE/SLIDES companion links. Write a concise four-structure
  spec (semiring · diff/comonad · lens/optic · measure) so all refs resolve at once.
- `SPILL_AND_FAQ_PLAN.md` — 4 refs (`exec/stream.clj`, pre_agg/planner_demo/grace_hash
  tests). Write a short spill+FAQ planning doc or repoint the refs.

### 4.2 Fix ns refs in living architecture docs — M — ☐
`CORE.md`, `SURFACE.md`, `DEPENDENT_TYPES.md`, `PHYSICAL_PLANNER.md`: replace
`relational.clj` / `optimize/verified-rewrite?` / `wandler.surface.collections` /
bare `wandler.optimize` with the clean-tree equivalents. Regenerate `SURFACE.md`
from the clean vocabulary (the generator the README cites — confirm it exists at
`dev/gen_surface_md.clj`; if not, write it).

### 4.3 Remove dangling doc links — S — ☐
`CORE.md`/`SLIDES.md`/`LANGUAGE.md` link `PROGRAMMING_MODEL.md` (doesn't exist
here — only `../ansatz/docs/PROGRAMMING_MODEL_GAPS.md`). `grace_hash_test.clj:10`
/ `planner_demo_test.clj:18` cite `docs/SPILL_AND_FAQ_PLAN.md` (doesn't exist).
Either write stubs, repoint, or drop the links.

### 4.4 README Status block + doc index — S — ☐
Rewrite the Status block to the post-strangler reality, fix the doc links, fix stats.

**Phase 4 gate:** every doc link resolves; no doc describes a deleted ns as current; SURFACE.md regenerated.

---

## Phase 5 — Syntax ergonomics (Track D) · close the statement-level gap

Proof *scripts* are at near-Lean parity (frame.clj/bucket.clj = 0 raw kernel
terms). The residual gap is statement-level boilerplate driven by elaborator
inference limits — statements run ~4–6× longer than Lean. These are ansatz
*elaborator* features; each shrinks every wandler statement. Highest leverage first.

### 5.1 Thin the law statements — ◐ frame.clj done — **NO elaborator change needed**
**MAJOR FINDING (overturns the review):** the ansatz elaborator ALREADY infers dropped
type args. Init signatures keep implicit binder info (`List.map => [α:implicit β:implicit
f l]`), so `insert-implicits` + unification solves them. PROVEN: `(List.map (fn x => x) xs)`
elaborates to the SAME kernel term as `(List.map Nat Nat (fn x => x) xs)`, by `rfl`. So the
"~104 explicit type args" are the LAW FILES written verbose — not a surface limitation.
Phase 5.1 is therefore a pure **wandler law-statement thinning**, no ansatz work.

- **frame.clj DONE** (commit 857fd31): all 3 aggregate laws thinned (~30% shorter, near-Lean);
  re-prove + frame_test + frame_index_test + surface_keyfactor_test green. The thin form is
  def-eq, so the optimizer (which matches on statement structure) is unaffected.
- **Head-dependence caveat (found surveying relational.clj):** the sweep is NOT uniform.
  Init SOAC heads (`List.map/filter/foldl/flatMap`) + `Prod.mk/fst/snd` are `:implicit` →
  thinnable. wandler-defined heads (`Map.lookup`, `Map.group_by`, `Option.isSome`,
  `List.elem`) may have EXPLICIT type params → not thinnable without changing their kmap
  signatures to mark the params implicit (a separate, deeper change). So a clean full sweep
  needs per-head triage + possibly kmap signature work.
- **Head triage (binder-info, verified against store):** thinnable (leading `:implicit`):
  `List.map/filter/foldl/flatMap`, `Prod.mk/fst/snd`, `Option.isSome/getD`. NOT thinnable
  (all-`:default`): every wandler `Map.*` (`lookup/group_by/gbStepId/insert/join`); also
  `List.lookup/elem`, `Option.map`, `BEq.beq`, `List.nil` (instance-entangled or
  result-type-only). To thin `Map.*` would need kmap signature changes (deeper, deferred).
- **SWEEP APPLIED (◐ suite-validation running):** wrote a paren-aware drop-transform keyed by
  the triaged head→count table (`/tmp/thin_typeargs.py`, skips comments/strings) and applied it
  across all law files: **~173 sites thinned** (faq 98, bucket 37, relational 26, monoid 9, par 2,
  reorder 1) + frame's 3 (manual). Whole chain re-proves (`install-laws!` clean); full suite +
  published-pin validation in flight.
- **Deferred (deeper):** making wandler `Map.*` signatures implicit (unlocks the Map.*-heavy
  verbosity); the instance-coercion `(WSemiring.toWAddMonoid m)` sites (5.2).

### 5.2 Instance-argument synthesis in statement position — L — ☐
~35 explicit instance args (`(WSemiring.toWAddMonoid m)`, `instBEqOfDecidableEq`).
Lean's instance resolution fills these. Implement instance synthesis for the
registered carrier/typeclass instances (we already have the registry). Composes
with 5.1.
- **Verify:** the WSemiring/BEq sites drop the explicit instance and resolve to the
  same term; suites green.

### 5.3 Binder + combinator sugar — M — ☐
161 typed `fn`-binders (`(fn [x :- X] …)` vs Lean `fun x =>`). Where the binder
type is inferable from context, allow it to be omitted; add `·.1`/`·.2`-style
anonymous projection sugar (the `Prod.snd` / `Order.1` cases). Surface-only;
desugars to current forms.
- **Verify:** golden desugar tests; suites green.

### 5.4 Route `List.chunk` through `a/defn` + match — M — ☐
`grace.clj` holds `List.chunk` as 39 raw `e/app*` terms / hand-managed de Bruijn.
Re-express as an `a/defn` with `match`, eliminating the raw-term debt (needs the
match-codegen path that earlier blocked mapcat∘filter — confirm it now handles this
shape, else this stays deferred).
- **Verify:** `List.chunk` + dependents (`flatten_chunk`, blockfold) still check-constant;
  grace_hash_test green.

**Phase 5 gate:** statement-level boilerplate measurably reduced (re-run the syntax
audit); every reformulated statement def-eq to its explicit predecessor; suites green.

---

## Phase 6 — Deferred technical roadmap (Track D) · the real depth work

Documented in `../ansatz/docs/WANDLER_REIMPL_PLAN.md`; not release blockers.

### 6.1 Perm-aware automation for the grace_proofs cluster — L — ☐
`grace_proofs.clj`: the `List.Perm` cluster is **189 raw `e/app*` terms**, only 1 of
15 builders migrated to thin. Needs either a `Perm`-aware tactic (a permutation
solver / `calc`-block surface) or a focused set of Perm rewrite lemmas the thin
`rw`/`simp` surface can drive. The single biggest remaining raw-term debt.

### 6.2 Level-2: deep generic frame family + delete `wandler.laws.*` — L — ☐
`clean/laws/faq.clj:514-521`: re-derive `Map.foldl_join_frame_generic` /
`_sum_factor_generic` / `keyfactor_float_generic` / `bucket_factor_pull_generic` /
`Nat.cond_and_mul_split_generic` on the clean tree, repoint, then literally delete
the remaining `wandler.laws.*`. The last structural step of the strangler.

### 6.3 Smaller deferred items — tracked — ☐
- `parFold`/`parFold_eq` recursive certification (`clean/core/monoid.clj:72`) —
  blocked on an ansatz structural-recursion gap.
- filter→join pushdown case C (`clean/laws/relational.clj:137`).
- Phase-4 un-materialized nested-sum index (`faq.clj:310`).
- Float-tier semiring proofs (`:pending`, `inference/semiring.clj`).
- The `prelude/list.clj` 312-line big-operator library — an *ecosystem* gap
  (no Mathlib BigOperators), not fixable by surface work; revisit if/when a
  Mathlib algebra import path exists.

---

## Sequencing summary

1. **Phase 1** (S, ~1 session) — stop misleading users. Highest ratio.
2. **Phase 2** (M) — stop the green mirage. Protects everything after.
3. **Phase 3** (M+L) — un-hide proof failures. Protects the optimizer's value prop.
4. **Phase 4** (M) — docs match reality. Fast follow on 1–3.
5. **Phase 5** (L) — ergonomics; each lever shrinks every statement.
6. **Phase 6** (L) — depth; the documented roadmap, no rush.

Every phase ends with both suites green. Phases 1–4 are the "very good shape"
core; 5–6 are the ongoing improvement track.
