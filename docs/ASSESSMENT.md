# Wandler consistency and development assessment

Review date: 2026-10-03. Wandler has a coherent core: elaborate a pure pipeline,
search for an equivalent term, independently check the equality proof, then lower
the term. Its opportunity is to make this core usable inside a bounded adaptive
runtime. The immediate work is to strengthen the execution contracts and measure
total costs before adding more integrations.

This review covers the source, tests, recent history, documentation, and current
sibling checkouts. It does not certify every lowering or engine adapter. Wandler
began this review with a clean tree at `db48945`. Remote main subsequently advanced
to `d8a6c38`, removing archived documentation; the upgrade PR is based on that
revision. Much of the recent machinery work is in sibling repositories.

Reviewed sibling heads: Ansatz `d01f0ba`, Simmis `a221eb5`, its website
`e63a796`, Dvergr `70780f0`, Spindel `7355bda`, Foerster `6650974`, and
Raster `1c47d3e3`. Spindel is on `feat/affine-world-forks` with uncommitted
inference work; these checkouts are not a single synchronized release. Foerster
currently pins released Spindel 0.1.96. No sibling files were changed.

## Ansatz upgrade

The dependency moves from 0.2.68 to **0.2.115**, the latest release in
[Clojars' live Maven metadata](https://repo.clojars.org/org/replikativ/ansatz/maven-metadata.xml).
The sibling HEAD adds only a formatting commit after that
release. The published jar and the local checkout are tested separately.

Changes that matter to Wandler include strict kernel soundness fixes, opaque
theorems, pairwise definitional-equality caches, type-directed arithmetic and
numerals, Lean's instance registry, and versioned content-addressed CBOR stores.
The additive elaborator, optimizer-hook, and codegen seams still exist.

Import full Init with `ansatz.import` into a fresh current-format store and use
`(a/init! store-path "init")` (see the README). The live published store index
currently contains only Mathlib: `(a/init! "init")` cannot fetch standalone Init
on a fresh machine. Old store paths require re-importing; Ansatz has no migration. Wandler's test
resolver still accepts an NDJSON fixture and builds a low-level test cache from
the older pinned Init export. Its fetched cache path includes the store format, so a pre-CBOR cache is not
reopened or overwritten by the new decoder. That fixture path does not exercise the complete
current store importer, manifest, attributes, or instance-index lifecycle.
`bin/smoke-init.clj` checks public explicit-store initialization separately from
fixture-based integration tests. A fresh format-1 Init import and this smoke
check passed, including complete law installation and the README pipeline.

## Findings and changes

| Priority | Finding | Action in this update |
|---|---|---|
| High | Raster recognized any fold step mentioning addition and ignored the initial accumulator. This can lower a different function. | Require an actual Float-add step and a recognized zero seed; otherwise decline. Free indices outside the map argument also decline. |
| High | Raster parallel sums implicitly changed Float reduction order, contradicting the SIMD adapter's default refusal. | Decline by default; require `register! {:allow-float-reassociation? true}`. The opt-in accepts rounding changes and is a trusted numerical boundary. |
| High | Documentation treated a term rewrite certificate as sufficient proof of arbitrary lowering and stateful hot-swap behavior. | Correct the README trust ledger and document caller obligations in the JIT guide. |
| Medium | Raster registration erased every cost backend. Repeated registration could not safely compose engines. | Replace only the backend with the same name. |
| Medium | Cost selection lowered every candidate before comparing prices, potentially compiling expensive native kernels that could never win. | Compare estimates first, try affordable candidates in cost order, stop at the first supported lowering. |
| Medium | The one-shot window JIT accumulated sample rows after its only replanning trigger. | Retain sample rows only during warmup. Result collection remains finite and eager. |
| Medium | A benchmark asserted wall-clock speedups in the unit suite and failed under concurrent validation. | Keep certification and answer equality as assertions; print timings as informational measurements. |
| Medium | The core optimizer records caught exceptions but `explain` hid their messages. | Include `:error` when a report has one. |
| Medium | Optional Raster tests treated adapter load failures as an absent dependency. | Skip only when Raster is absent; an installed broken adapter now fails the test. |
| Medium | Range inference always emitted `:int`; length inference also overwrote union schemas. Both could reject the original sample. | Preserve numerical carriers, optional entry properties, and unions; omit bounds for nonfinite samples and handle mixed small-domain values. |
| Medium | Raw replay/store fixtures lacked Ansatz's environment-local instance registry. Elaboration repeatedly rebuilt the discovery index by scanning the library. | Attach the bundled Lean registry once, intersected with the fixture, with a one-time discovery fallback. Keep global proof state untouched. |
| High | With a real registry, Wandler's unregistered carrier definitions could no longer synthesize `WAddMonoid Nat`. Name-based discovery had concealed the missing registration. | Register admitted Nat/Bool/tropical and canonical Std instances on the owning environment, including checked-cache restores. |

| High | Wandler still lowered Int arithmetic and monoid merges to checked machine operations while current Ansatz promotes unbounded Nat/Int arithmetic. Primitive hints also narrowed fused results. | Use promoting operators and boxed Nat/Int steps; retain primitive hints only for machine carriers. Nonprimitive long-array maps return vectors to preserve promoted results. |

The independent gate in `optimize/certify.clj` uses strict `TypeChecker.check`
and checks the proof type against the requested equality after closing the local
context. This is the right separation between untrusted search and admission.
Rejecting an unverifiable candidate and retaining the original is also the right
fallback. Equality saturation and cost policy remain outside the trusted gate.

The remaining execution boundary is substantial. `backend/simd.clj`'s
`associative-proven?` currently classifies names and metadata rather than checking
a supplied theorem there. `backend/stratum.clj` can offload Float sums and convert
integral values to long arrays. An abstract Nat/Int law alone does not establish
machine overflow, trapping, conversion, or floating-point behavior. Raster's
latest commits explicitly address checked and total integer arithmetic; Wandler
needs the same precision at every representation boundary.

An additional contract risk is `induce-types! :refined? true`: it registers
sample-derived bounds in a Malli function schema, which can become hard Subtype
assumptions in Ansatz. The `::source :sample-prior` tag is descriptive; it is
not itself a runtime guard. Validate future inputs against those bounds, or keep
them in cost priors, before using them to license filter elimination. Tests that
only check that the sample validates do not establish correctness on future data.

## Independent review follow-ups

Three focused reviews covered certification/arithmetic, JIT state and replay, and
upgrade/inference completeness. They identified these concrete remaining boundaries:

| Priority | Area | Evidence and next action |
|---|---|---|
| High | Stateful adaptive guards | A malformed join delta retained in source state can invalidate a later optimized step even when the new delta is valid. Fixed in the JIT follow-up: `:state-guard` covers pre-step state and delta support; regression checks retraction and safe re-entry. |
| High | PGO replay | `:reverify? true` skipped missing certificates and executed an arbitrary supplied closure. Fixed in the JIT follow-up: strict replay checks both expressions and their equality, then compiles locally, ignoring the supplied closure. |
| High | Inferred input contracts | Ansatz currently maps Malli `:int` to Nat and optional record fields to mandatory kernel fields. Samples containing negative integers or missing fields do not establish a faithful carrier; restrict or normalize the induction boundary and guard future inputs. |
| High | SIMD fallback | Every double-array monoid computes addition, even a max/custom spec. Honor its combine and identity or decline unsupported specs. Machine-long addition also differs from unbounded Int addition. |
| High | Stratum offload | Integral values and keys can narrow to long; Float sums can reassociate without permission. Require representation and numerical contracts before offloading. |
| Medium | Graph replacement | `carry-output!` copies only the running output. It does not transfer downstream subscriptions or input routing; The follow-up narrows its documented contract; graph replacement remains unimplemented. |
| Medium | Adaptive benchmark pricing | `adaptive-groupby` guards every invocation but divides the measured guard cost by `:amortize` when choosing. Fixed in the JIT follow-up: charge the actual per-call guard cost. Caching still requires a validated immutable relation. |
| Medium | Compiler artifacts | Generic Raster compilation interns fresh vars without a cache or cleanup. Repeated replanning needs session-owned bounded artifacts. |
| Medium | Fork ownership | The Spindel adapter captures an ordinary operator atom outside context state. A context fork does not establish independent operator storage; test isolation before speculative trials. |

The JIT state/replay/pricing items are addressed in a focused follow-up to the upgrade. The
optional SIMD/Stratum contracts and inference admission need their own changes;
they are existing defects, and the base suite's skipped adapters do not validate them.

## Code quality and testing

The module separation is useful: certification, costs, plan inspection, modes,
and adapters have recognizable owners. However, namespace-load registration and
global atoms make installations order-dependent. Law installation also relies on
a global Ansatz environment and mutates its extensions during admission. This
is a concern for concurrent compilation and forked worlds, even when individual
plans are pure. A compiler session should eventually own these registries,
environment references, and reports.

Some comments still describe the retired old/clean split, optional Malli aliases
that are no longer optional, and roadmap items that now exist. Treat the source
and tests as the current capability ledger; reconcile these notes incrementally
when changing their owning modules rather than undertaking another large rename.

There are 67 broad `catch Throwable` sites in source. Some are intentional
best-effort search boundaries, but the pattern conflates unsupported shapes,
bad proofs, dependency faults, and resource failures. Preserve rejection reasons
as data and give development/CI a strict diagnostic mode. Successful execution
with no rewrites should not conceal a broken optimizer.

Repository-wide clj-kondo initially reports 872 errors and 305 warnings across
228 files. Many findings come from unrecognized Ansatz binders, tactic syntax,
and macros, so this is not a count of runtime defects. Add/export DSL hooks,
then establish a useful lint baseline rather than suppressing entire namespaces.
The touched backend/registry files have no lint errors.

The documented 418 tests, 1897 assertions, and 3.5 minute runtime predate the
upgrade. Initial unprepared-fixture runs spent over half an hour progressing
through law installation. A JVM thread dump identified repeated
`build-instance-index` calls from elaboration. The fixture bootstrap now carries
the registry like normal Ansatz initialization; the full runs were restarted
after this correction. This also exposed and corrected missing registration of
Wandler's own carrier instances, which an ordinary Ansatz bootstrap already
requires. Measure namespace loading,
fixture loading, proof construction, strict admission, optimization, compilation,
and execution separately. Reusable law artifacts must carry an environment and
dependency identity and still be checked before use; cache presence is not proof.

Regression tests added here exercise registry composition, cost-first lowering,
numerical opt-in, zero-seed preservation, and rejecting a misleading addition
step. The certifier test also compared two aliases of the same namespace as its
supposed old/new oracle. It now checks the fused shape and independent proof
gate, including rejection of forged candidates. Existing swap and async-seq tests
also run. Optional engine coverage should
eventually have explicit CI jobs that fail if the selected engine cannot load.
The base suite's graceful optional-dependency skips are not integration coverage.

## Position in the current stack

| Project | Observed responsibility | Proposed relationship to Wandler |
|---|---|---|
| Ansatz | Kernel, elaboration, library stores, instance and proof search infrastructure | Certify pure term transformations; keep the existing three seams. |
| Spindel | Reactive execution contexts, forks, savepoints, inference, resource and settlement authority | Run bounded experiments on snapshots; install code between steps. A fork is not permission to adopt effects. |
| Foerster | Inference policies over savepoints, traces, replay, scoring, diagnostics | Optional statistical search policy over candidates and cost uncertainty. Its probabilistic result is not an equality certificate. |
| Dvergr | Agent workflows, sandboxed code, room/world forks, budgets and review | Propose laws, strategies, or experiments outside the kernel gate. Keep generated code and effects under its existing authority model. |
| Simmis | Versioned shared workspace, governed proposals, databases, books and room repositories | A possible source of real workloads and reviewed experiments. Wandler need not become an application framework. |
| Raster | Typed numerical compilation across CPU and GPU targets | Execute eligible numerical fragments under explicit arithmetic, layout, device, and transfer contracts. |

These are architectural proposals, not newly integrated capabilities. The current
Wandler Spindel adapter keeps the operator in a plain host atom while its version
signal lives in a context. Forking a context does not make that operator atom
world-local. Test parent/fork isolation before using the adapter as an autonomous
experimental runtime. Its two updates also need a concurrency/boundary contract.

Foerster's trace-aware Monte Carlo algorithms and Wandler's finite semiring FAQ
factorization solve different problems. A useful first bridge would optimize pure
deterministic likelihood or scoring subgraphs, with site addresses and stochastic
effect order fixed. Whole-model rewrites require stronger effect and trace laws.

## Recommended next increments

1. **Make candidate admission explicit.** Introduce a compiled-plan artifact with
   the original term, candidate term, local-context and environment identity,
   checked proof and axiom dependencies, backend and numerical contract, and
   state-schema identity. Search policies must not admit new equality axioms or
   silently turn asserted monoid laws into kernel-proven laws.
   Keep a low-level function swap available, but give adaptive installation a
   separate admission API. Batch equality does not prove a state migration.

2. **Finish a bounded finite-window loop.** Start with stateless maps or full
   window aggregates. Use bounded samples and output delivery, profile-aware
   reported costs, compilation deadlines/budgets, hysteresis, and a last-known
   valid fallback. Add repeated drift triggers only after this contract works.
   Check correctness against the original on duplicate keys, empty windows,
   skewed inputs, and profile changes. Avoid timing assertions in ordinary tests.

3. **Model end-to-end numerical costs.** Include boxing, layout conversion,
   transfer, synchronization, compilation, and cache reuse. In this review's
   current-Raster run, the compute-heavy array kernel was about 3x faster, but
   square summation from a boxed list was about 2.8–4x slower including conversion.
   These are single-machine observations, not portable thresholds. Preserve
   array-native data before adding transparent GPU dispatch.

4. **Explore bounded search without enlarging trust.** Let a simple policy choose
   among certified alternatives first. Compare static heuristics, empirical
   selection, and a Foerster policy under the same workload and total budget.
   Spindel can isolate trials; Dvergr can later propose candidate strategies.
   Adoption must still obey certification, arithmetic contracts, state identity,
   and settlement authority.

5. **Use one application workload as evidence.** Select a read-only Simmis
   query/report or a pure inference scoring kernel. Record correctness, latency,
   compilation cost, memory, deopts, and total experiment cost. This would show
   whether adaptation pays before expanding cross-project integration.

The first milestone should demonstrate repeated adaptation on a pure finite
workload with explicit candidate admission and lower total cost. It need not
integrate every project or claim verification of the surrounding agent system.

## Validation results

| Check | Result |
|---|---|
| Published Ansatz 0.2.115, full Init required, including JIT follow-up | 435 tests, 1964 assertions; zero failures/errors. |
| Local Ansatz HEAD, full Init required, upgrade branch | 429 tests, 1945 assertions; zero failures/errors. |
| Current sibling Raster | 3 tests, 13 assertions; zero failures/errors. |
| Current sibling Spindel adapter | 1 test, 9 assertions; zero failures/errors. |
| LogicNG WMC backend | 3 tests, 12 assertions; zero failures/errors. |
| Carrier-registry and cache restoration regression | 1 test, 5 assertions; zero failures/errors. |
| Public store lifecycle | Fresh format-1 Init import via `ansatz.import`, then public `a/init!`, complete law installation, and quickstart pipeline passed. |
| Fixture cache | Current-format cache import and reuse passed using a local full Init export; cache directory includes the format version. |
| Package | `clojure -T:build jar` succeeds. |
| Formatting and links | Touched Clojure files checked with cljfmt; changed Markdown links resolve locally. |

The live Datahike/Stratum integrations, GPU execution, fork isolation, and a
named-store download lifecycle were not validated in this update.
The base suite still skips absent optional engines. No sibling repository was
modified and no artifact was published.
