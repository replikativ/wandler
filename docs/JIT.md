# The verified JIT — profile steers, the kernel guarantees

Wandler's plan is static by default, but a pipeline can also **adapt to the data it actually
sees** — re-planning against measured statistics, and even hot-swapping operators mid-stream.
Profiling chooses among kernel-certified expressions. Correct execution additionally
requires faithful lowering, guarded runtime hypotheses, compatible state, and safe
installation boundaries. The raw swap APIs leave those obligations to their callers.

There are two layers, and they compose: a **planning JIT** (measure → re-optimize, static) and
a **runtime hot-swap JIT** (a swappable operator cell driven by a guarded-adaptive policy). They
live in `wandler.core/optimize-measured` and `wandler.jit.*`.

## Layer 1 — the planning JIT (`optimize-measured`)

`w/optimize-measured` measures a pipeline's filter selectivities on a real sample, folds them
(plus any caller-supplied cardinalities, e.g. from a stream window or a datahike `:estimate`)
into the cost model, and **re-runs the certified optimizer**. The result is kernel-re-checked,
so adapting to the workload cannot make it unsound.

```clojure
(def low  (vec (for [i (range 500)] {:rev (mod (* i 7) 90)})))   ; almost nothing > 100
(def high (vec (for [i (range 500)] {:rev (+ 100 (mod i 50))}))) ; everything >= 100

(:profile   (w/optimize-measured 'big-orders [low]))   ;;=> {"…" 0.01}   ; measured pass-rate
(:verified? (w/optimize-measured 'big-orders [low]))   ;;=> true
(:profile   (w/optimize-measured 'big-orders [high]))  ;;=> {"…" 0.98}
```

On a single filter the selectivity just confirms the plan. On a **join** it steers the
cost-gated choices the OPTIMIZER exposes — drive direction (index the side the filter shrinks),
the pre-aggregated index, grace-hash spill. Whatever it picks comes back kernel-certified.

> **⚠ trusted input, ✓ proven output.** The *measurement* is a statistic about your data — a
> trusted, fallible observation. It steers a *cost* decision; the plan it picks is still proved
> `≡` the original before it runs. (`optimize-measured` takes a flat seq of the elements the
> filters see — distinct from `w/plan`, which takes whole inputs to time the function.)

This is the static loop: **measure → re-plan → run.** For a long-running stream you want to do
it *continuously*, which is layer 2.

## Layer 2 — the runtime hot-swap JIT (`jit/swap`)

Here an operator is replaced *while the stream is flowing*. Two pieces: a mechanism and a
policy.

### The mechanism — `PSwapNode`

A per-step operator is reified as a **replaceable value behind one indirection** — one impl per
substrate, so the same swap works in batch (an atom cell), async-seq (a generator read through
the cell), spindel, and DBSP (a stage fn plus its carried integrator). "Mode-indexed": the
mechanism is the same shape in every corner of the mode lattice.

```clojure
(defprotocol PSwapNode
  (current    [node]   "the operator currently installed")
  (swap-op!   [node f] "atomically install operator f; caller establishes equivalence,
                        state compatibility, and a safe boundary")
  (generation [node]   "number of swaps performed"))
```

Operators are **Mealy steps** `(state, input) → [state', output]`, so state threads across
inputs *and across a swap*. A stateless `map` ignores `state`; a running aggregate or a DBSP
integrator carries it.

### The policy — `run-adaptive`

This is HotSpot's speculate-with-deopt, regrounded on proof. Install the *optimized* operator.
Per element:

- an input-local `:guard` checks the current input; a `:state-guard` checks
  `(state, input)` when the hypothesis involves retained data. At least one is required;
  if both are supplied, both must hold;
- guard holds → run the fast operator;
- guard fails → **deopt**: run the certified *original* on the **same** input (the guard is a
  *pre*-check, so fallback is lossless — nothing dropped or duplicated), and count a violation;
- after `cutoff` violations → **pin** to the original and stop guarding (anti-thrash).

```clojure
(if (and (if guard (guard in) true)
         (if state-guard (state-guard st in) true))
  (let [[st' out] (optimized st in)] ...)        ; fast path: hypothesis holds
  (let [[st' out] (original  st in)]             ; deopt: original on the SAME input
    (when (>= viol' cutoff) (swap-op! node original)) ...))   ; pin after repeated misses
```

A DBSP join guard must cover the **pre-step retained source support and incoming
delta support**. A malformed row retained after fallback can invalidate the next
optimized step despite a valid new delta. Checking only the prospective integrated
sources is also insufficient during retraction: the delta computation still reads
the old sources. Fallback handles that retraction; optimized execution can resume
on a later input once the state hypothesis holds.

### Conditions for a sound swap

For a pure per-window operator, the planner can certify equality with the original
term before compilation. Installing its compiled function between completed windows
preserves results provided the lowering implements that term faithfully.

A stateful Mealy operator needs a stronger contract: equivalence must cover both
output and next state, and the two implementations must share a compatible state
representation. Preserving the state *type* alone does not establish that contract.
A conditional rewrite also needs a guard that discharges its hypothesis on the
actual input and state.

`PSwapNode`, `swap-cell`, and `run-adaptive` are mechanisms that trust these
obligations to their callers. They do not accept or check a certificate, derive
a state migration, or establish a quiescent boundary themselves. The existing
adapter tests exercise specific examples of correct replacement.

## Strict PGO replay

`wandler.jit.pgo/replay` with `:reverify? true` strictly typechecks both closed
expressions, checks their equality certificate, and compiles the checked plan
locally. It ignores the artifact's supplied `:run` closure. A changed plan needs
a valid proof; an identical plan may omit it but must still typecheck. Runtime
sources must satisfy the local-context types and refinements; replay does not
validate arbitrary input data. The code generator remains trusted.

Artifacts containing `:run` are in-process caches, not a serialization format.
Replaying without re-verification trusts that executable cache. Environment and
backend identities still need explicit representation before persisted artifacts
or concurrent compiler sessions can safely share plans.

`adaptive-groupby` checks every relation passed to its returned function. Plan
selection now charges the full measured guard cost on each invocation. The
`:amortize` option remains telemetry; guard caching needs a separately validated
immutable relation.

`carry-output!` only seeds a new DBSP node's output. The caller must separately
rewire subscriptions and input routing and establish state compatibility.

## How the layers compose

The stream JIT (`jit/stream`) is both at once: profile a window's finite `List` term with
sampled cardinalities (layer 1), re-optimize it, and hot-swap the resulting operator (layer 2).
The planner certifies the new finite-window term against the original and compiles
it before swapping the function between windows. This demonstrates stateless window
replacement. General stateful incremental replacement needs the state and delta
contracts described above; batch equality alone does not certify arbitrary effects.

## Where to go next

- **OPTIMIZER.md** — the cost model the planning JIT feeds, and the certified rewrites it picks
  among.
- **STREAMING.md** — the incremental views the hot-swap JIT keeps fast under changing load.
- **TUTORIAL.md** §6 — the JIT from the user's side, runnable.
- **PROGRAMMING_MODEL.md** — translation validation as the discipline that makes a mid-stream
  swap as trustworthy as a compile-time rewrite.

## Current implementation boundaries

The kernel certifies term rewrites. `PSwapNode` and `swap-cell` accept ordinary
functions and do not check certificates themselves. Their caller must establish
operator equivalence, compatible state representation, purity, and a safe swap
boundary. A proof of a batch function does not alone establish those properties
for an arbitrary stateful or effectful operator. `run-adaptive` also trusts the
caller-supplied guard and operator pair.

`jit-stream` currently replans once after `:warmup` windows. It retains only the
warmup sample, but collects all results before returning. It is a finite-window
prototype, not yet a continuously adapting, bounded-memory stream processor.
Its reported before/after costs use default parameters rather than the measured
profile. Drift triggers, compilation budgets, and state migration certificates
remain future work.

Raster's parallel Float reductions can change rounding relative to a sequential
fold. They now decline by default. `(wandler.backend.raster/register!
{:allow-float-reassociation? true})` enables this numerical contract explicitly;
it is a trusted approximate lowering, not a bit-exact CIC-certified result.
