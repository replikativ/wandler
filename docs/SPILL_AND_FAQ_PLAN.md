# Spill & FAQ planning — the physical strategy ladder for joins and aggregates

> Referenced from `wandler.exec.stream`, the pre-agg / planner-demo / grace-hash tests.
> Companion to [`PROGRAMMING_MODEL.md`](PROGRAMMING_MODEL.md) §3/§6 and
> [`PHYSICAL_PLANNER.md`](PHYSICAL_PLANNER.md). Every strategy below is certified equal to
> the naive plan by `wandler.optimize.certify/verified-rewrite?`; the planner only
> *chooses* among them by cost.

## The ladder

For a join (optionally feeding an aggregate), the planner picks a physical realization
over the plan lens (`wandler.optimize.plan`). In rough cost order:

1. **In-memory hash join** — build a hash index on the smaller side, probe the larger.
   The default when the build side fits memory. Proof: `member`/filter over a list ≡ a
   `group_by` + `lookup` index probe.
2. **Nested-loop join** — O(n·m); the fallback when no key function / no index is usable.
3. **Grace-hash spill** — when the build side does *not* fit: partition both inputs into
   key-aligned chunks (`List.chunk`), join chunk-by-chunk, concatenate. Certified by
   `List.flatten_chunk` + `Map.foldl_join_blockfold` (+ the `List.Perm` cluster for
   order-insensitivity). Home: `wandler.laws.grace`.
4. **Pre-aggregated (FAQ) index** — when the consumer is a *separable SUM* over the join
   (`Σ_{x⋈y} w(x)·v(y)`), don't materialize pairs at all: pre-sum each bucket once, so the
   held index is O(distinct keys), not O(|ys|). Certified by
   `Map.foldl_join_sum_factor_generic` (the crux `List.lookup_map_kv`) and the frame rule
   `Map.foldl_join_frame_generic`. Home: `wandler.laws.faq`.

## What gates the choice

- **Memory** — build-side size estimate vs budget routes 1 → 3 (spill).
- **Separability** — the optimizer recognizes a separable-SUM consumer (a `foldl (λacc p.
  acc + g(snd p))` over a join) and only then admits strategy 4; a non-separable consumer
  (e.g. a bare count with no per-row weight) declines it.
- **`:ndv`** — a DuckDB-style distinct-value oracle makes the small held-index estimate
  for strategy 4 *sound*; without a credible ndv the planner keeps the safe plan.
- **Consumer order-sensitivity** — order-destroying rewrites (join reorder via
  `Map.join_comm`, a `List.Perm`) only certify as `Eq` under an order-invariant consumer
  (count/sum), so `:vector` (materialize-ordered) sinks never unlock them. This is
  enforced by `verified-rewrite?` itself, not by a flag (see `wandler.plan`,
  consumer-aware planning).

## Why this is sound, not just fast

The planner's search over the ladder is untrusted. Each rung ships with a kernel proof
that its output equals the naive join/aggregate; the gate re-checks that proof per
program. A mis-estimated cost can pick a *slower* rung, never a *wrong* one — a bad plan
is rejected, never miscompiled.

## Status / roadmap

Rungs 1–4 are proven and wired. The deep generic frame family
(`Map.foldl_keyfactor_float_generic`, the FD-scope keyfactor) is the Level-2 remainder
tracked in `wandler.laws.faq`. Multi-way FAQ variable elimination (recursive join
ordering) is the open research frontier; single aggregating joins factor today.
