# Strangler Retirement — completing the clean cutover

The `wandler.clean.*` strangler reimplementation is **functionally done**: `wandler.core/install!`
reaches only the clean optimizer + clean surface, and the differential parity gate
(`wandler.clean.diff` + `test/wandler/clean/diff_test.clj` — plan ≡ result ≡ proof, clean vs old vs
clojure.core) is built and green. What remains is the cosmetic finish (drop the `.clean.` staging
prefix) + the deferred laws port. This doc sequences that into suite-gated phases.

**Companion:** `docs/REPO_HARDENING_PLAN.md` (the broader hardening tracks; this doc is the
cutover-specific subset, with the user's decision to do the **full finish + promote to `wandler.*`**).

**Invariant for every phase:** `clj -M:test` stays green (store mounted — set `WANDLER_REQUIRE_STORE=1`;
storeless runs skip ~104 files and prove nothing). The differential test must stay green across the
rename — it is the soundness witness that clean ≡ the reference.

**Keepers (do NOT purge — new/integration, just not wired into `install!`):** `wandler.adaptive`,
`wandler.infer`, `wandler.jit.*` (this session's refinement-planner + verified-JIT work),
`wandler.gradual`, `wandler.bridge.*`.

---

## Phase A — Safety net: strict install self-check  ·  S  ·  ☑ DONE
*(REPO_HARDENING_PLAN Phase 3.3. Do first — protects every later move.)*

A new dev test that admits the law DAG and asserts **zero swallowed proof failures** — no
`catch Throwable _ nil` silently dropping a law. After this, a rename/port that breaks a proof fails
loudly instead of quietly disabling an optimization.

- Add `install-laws!`-with-strict-mode (or a test that re-proves each law via `env/verifies?` and
  asserts all present + checked).
- Gate: the strict check is green; suite green.

---

## Phase B — Promote `wandler.clean.* → wandler.*`  ·  M  ·  ☑ DONE
Pure mechanical rename, **one reviewable commit** (no logic change), suite-gated.

**B0 — collision pre-resolution.** The only file-name clash is `clean/optimize/faq.clj` vs the dead old
`optimize/faq.clj`. Delete old `optimize/faq.clj` + `faq_plan_test` first (dead-from-core), verify green.
(No other clashes: `surface/` old = streams,vocabulary; `laws/` old = semiring,dist,tropical; both
disjoint from the clean names.)

**B1 — file moves (`git mv`):**

| from | to | new ns |
|---|---|---|
| `clean/optimize.clj` | `optimize.clj` | `wandler.optimize` |
| `clean/optimize/{certify,cost,cse,egraph,faq,physical,filter_elim}.clj` | `optimize/…` | `wandler.optimize.…` (beside surviving `optimize/plan.clj`) |
| `clean/surface/{collections,relational,records,malli,refine,strings,option,core,common}.clj` | `surface/…` | `wandler.surface.…` (beside `surface/{streams,vocabulary}`) |
| `clean/laws/{frame,relational,fusion,grace,grace_proofs,groupby,faq,reorder,uniqueness,bucket,ac}.clj` | `laws/…` | `wandler.laws.…` (beside `laws/{semiring,dist,tropical}`) |
| `clean/core/{par,monoid}.clj` | `core/…` | `wandler.core.par` / `wandler.core.monoid` (coexist with `core.clj`) |
| `clean/diff.clj` | `diff.clj` | `wandler.diff` |
| `test/wandler/clean/*` | `test/wandler/*` | — |

**B2 — reference rewrite.** `wandler.clean.X → wandler.X` in every `ns`/`require` across `src` + `test`
(scripted), **plus** the `requiring-resolve`/`resolve` string literals an IDE rename misses:
`core.clj:109`, `exec/mode.clj:358/371/387/398`, `jit/stream.clj:63-64`,
`surface/streams.clj:314/371/394`, `laws/grace.clj`, `optimize/faq.clj`, and test-side
(`physical_test`, `mode_test`, `seq_accessors_test`, `egraph_test`).

**B3 — gate.** `clj -M:test` green (incl. the differential test). Commit:
`refactor: promote wandler.clean.* → wandler.* (mechanical rename, no logic change)`.

**Risk:** broad edit; mitigated by full-suite + differential gate. Do as ONE commit so review is "diff is
all renames."

---

## Phase C — Purge superseded old namespaces  ·  ☑ INVESTIGATED — nothing genuine to purge
Reading the actual files (not just the audit's "dead-from-core" label) showed the flagged candidates
are **distinct dormant FEATURES**, not duplicate old implementations of the clean tree:
- `wandler.stdlib` — a one-stop convenience installer that registers the (clean) `surface.*` vocabulary.
- `wandler.verified` — the drop-in transducer/reducer SURFACE (reads like Clojure transducers).
- `wandler.reducers` (+ `reducers/*`) — the transducer calculus; a **live dependency of `backend.stratum`**.
- `wandler.plan` — the unified source→sink planner entry ("every plan kernel-certified ≡ naive").

The genuine strangler DUPLICATES were already gone (surface/optimizer were never duplicated — clean was
the sole impl; the one true duplicate, `wandler.optimize.faq`, was removed in B0). "Dead-from-core" meant
"not reached by `install!`," not "obsolete." So there is no strangler debt to delete here — matching
`REPO_HARDENING_PLAN.md` Phase 1.3's original "keep all".

**Decision deferred to feature-scoping (not cleanup):** whether these dormant feature surfaces ship in the
first release is a product call. They are kept (tested, working); we do NOT silently delete working code.
If a leaner 1.0 is wanted, scope which features ship as an explicit, separate decision.

---

## Phase D — Level-2 laws port (the real depth work)  ·  L (multi-session)  ·  ☐
*(REPO_HARDENING_PLAN Phase 6.2.)* Retire old `wandler.laws.{semiring,dist,tropical}` that the promoted
`laws.faq`/`laws.frame` still ride.

- **D1** re-derive the generic frame family on the promoted tree: `Map.foldl_join_frame_generic`,
  `_sum_factor_generic`, `keyfactor_float_generic`, `bucket_factor_pull_generic`,
  `Nat.cond_and_mul_split_generic` (hand kernel proofs — the multi-day part).
- **D2** repoint `laws.faq` / `optimize.faq` / `semiring_class` off `wandler.laws.semiring`.
- **D3** delete `wandler.laws.{semiring,dist,tropical}`; migrate carrier tests.
- Gate each sub-step on the differential harness + suite.

**Recommendation:** ship A–C first (the visible cutover finish); do D as a focused follow-up — it is
the deferred technical roadmap, no rush, and it gates a "zero old code ridden" claim, not function.

---

## Phase E — Docs + first release  ·  ◐ (docs swept; release tooling pending)
After the rename, sweep doc references `wandler.clean.* → wandler.*` (README layout table, SURFACE.md,
architecture docs). Then the first-release checklist: version + CHANGELOG, tag → CI/CD (no manual
release). The README quickstart already loads clean and describes the clean tree as canonical.

---

## Sequencing
**A** (safety net) → **B** (rename) → **C** (purge) → **E-docs** → ship a first release → **D**
(laws port) as a follow-up. A–C + E are the user-visible "completion"; D is depth.
