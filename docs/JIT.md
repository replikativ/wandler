# The verified JIT — profile steers, the kernel guarantees

Wandler's plan is static by default, but a pipeline can also **adapt to the data it actually
sees** — re-planning against measured statistics, and even hot-swapping operators mid-stream.
The one idea that makes this safe: *profiling chooses which certified plan runs; it never
decides whether the plan is correct.* A bad statistic can only make wandler pick a **slower
correct** plan, never a wrong one — because every plan it might switch to was proved equal to
the original before it ran.

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
  (swap-op!   [node f] "atomically install operator f — sound mid-stream because every
                        wandler-compiled operator is kernel-certified ≡ the one it replaces")
  (generation [node]   "number of swaps performed"))
```

Operators are **Mealy steps** `(state, input) → [state', output]`, so state threads across
inputs *and across a swap*. A stateless `map` ignores `state`; a running aggregate or a DBSP
integrator carries it.

### The policy — `run-adaptive`

This is HotSpot's speculate-with-deopt, regrounded on proof. Install the *optimized* operator.
Per element:

- a **guard** discharges the optimized operator's hypothesis on this input (e.g. "this
  `group-by` can be dropped because the key is unique here");
- guard holds → run the fast operator;
- guard fails → **deopt**: run the certified *original* on the **same** input (the guard is a
  *pre*-check, so fallback is lossless — nothing dropped or duplicated), and count a violation;
- after `cutoff` violations → **pin** to the original and stop guarding (anti-thrash).

```clojure
(if (guard in)
  (let [[st' out] (optimized st in)] ...)        ; fast path: hypothesis holds
  (let [[st' out] (original  st in)]             ; deopt: original on the SAME input
    (when (>= viol' cutoff) (swap-op! node original)) ...))   ; pin after repeated misses
```

### Why the swap is sound

What makes replacing an operator mid-stream safe is two facts the kernel gives you:

1. **The operators are certified equal.** The optimized and original are
   `optimized ≡ original` (translation validation, the same gate the whole optimizer uses), so
   switching between them never changes the function computed.
2. **State migrates by identity, not reconstruction.** The Mealy state has a type the proof
   preserves, so carrying it across a swap is the *identity* — no frame rebuild.

> **✓ proven, ⚠ one checked hypothesis.** Contrast HotSpot: it speculates on a *profile* and
> rebuilds a stack frame on deopt. Wandler speculates on a *proved equivalence whose hypothesis
> is checked by a runtime guard*, and "deopts" by calling the other *certified* operator over
> the same state. The guard's predicate (the trusted-but-checked hypothesis) is the only runtime
> trust; the equivalence behind both operators is proven. The one thing the proof does *not*
> give is anti-thrash — hence the `cutoff` pin, borrowed straight from HotSpot's trap history.

## How the layers compose

The stream JIT (`jit/stream`) is both at once: profile a window's finite `List` term with
sampled cardinalities (layer 1), re-optimize it, and hot-swap the resulting operator (layer 2).
Because the new plan is proved `≡` the old, the swap is just a `reset!` — there is no deopt path
to take, only a faster certified operator installed at a quiescent boundary between windows. The
differential pass commutes with the optimizer, so a re-optimized per-step operator re-embeds
into the coinductive stream without re-deriving the increment laws.

## Where to go next

- **OPTIMIZER.md** — the cost model the planning JIT feeds, and the certified rewrites it picks
  among.
- **STREAMING.md** — the incremental views the hot-swap JIT keeps fast under changing load.
- **TUTORIAL.md** §6 — the JIT from the user's side, runnable.
- **PROGRAMMING_MODEL.md** — translation validation as the discipline that makes a mid-stream
  swap as trustworthy as a compile-time rewrite.
