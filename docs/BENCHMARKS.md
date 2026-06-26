# Benchmarks — what the certified rewrites buy

Every plan below produces **the same answer as the naive plan, kernel-certified
equal** (`optimized ≡ original` is a CIC theorem, re-checked per program). The
speedups are therefore *free of correctness risk*: a rewrite that didn't preserve
the answer would have been rejected by the kernel gate, never run. What's measured
here is only the wall-clock the certificate licenses.

## Methodology

- numbers are wall-clock, JVM warmed, median of repeated runs (`t!` = 3-run mean
  after a warm-up call), produced by the runnable demo tests listed under each
  result — not hand-quoted.
- each demo asserts `(= (naive …) (factored …))` at every size, so the table is also
  a correctness test.
- machine-dependent; reproduce locally with the commands shown. Trends (asymptotic
  divergence) are the point, not the absolute ms.

Reproduce all of them:

```
clj -M:test    # runs the whole suite incl. the demo namespaces below
```

## 1. FAQ frame-rule factorization — the headline

A 3-way aggregating join `Σ over (custs ⋈ orders ⋈ C)` on a few distinct keys, over
malli-typed records `[:map [:cid :int] [:val :int]]`. The naive plan materializes
the `|custs|·|orders|·|C|` product; the certified plan factors the sum through
per-key pre-aggregated indices (`Map.foldl_join_frame` + the FD keyfactor-float),
never building the product. **Same certified Σ at every size.**

| rows/list | naive product | naive (ms) | factored (ms) | speedup |
|---:|---:|---:|---:|---:|
| 240 | 216,000 | 26 | 6.7 | **4×** |
| 480 | 1,728,000 | 336 | 14.9 | **22×** |
| 720 | 5,832,000 | 836 | 44.8 | **19×** |

The naive plan grows ~**cubically** (26 → 336 → 836 ms); the factored plan stays
near-linear (6.7 → 15 → 45 ms) — the gap **widens** with size. This is an
*asymptotic* win the cost model sees from the schema (few distinct keys ⇒ the
pre-aggregated index is `O(distinct keys)`), not a constant-factor tweak.

> Source: `test/wandler/perf_faq_demo_test.clj`
> (`clj -M:test` prints the table; the same query certifies + runs at each size).

The factorization is **semiring-generic** — the identical machinery factors a
boolean-provenance query (`∨/∧`) and a tropical shortest-path query (`min/+`),
each certified at its carrier. See [`PROGRAMMING_MODEL.md`](PROGRAMMING_MODEL.md) §2(a).

## 2. The certified planner picks the right physical strategy

`test/wandler/planner_demo_test.clj` runs one logical aggregating-join query and
shows the cost model choosing among **four** physical strategies — hash / nested-loop
/ grace-hash spill / pre-aggregated index — by cardinality, each adopted only after
`cert/verified-rewrite?` certifies it equal to the original. The plan *changes with
the stats* (ndv, sizes, memory budget); the certificate is re-established for
whichever plan wins. (32 assertions, green.)

This is the database-optimizer ↔ certified-rewriting correspondence made literal:
join-order / strategy selection is an *untrusted* cost search whose every output is
*kernel-verified* before it runs.

## 3. Other measured wins (reproduce via the named test)

Each is a runnable demonstration that the certified rewrite beats the naive form on
wall-clock while the kernel proves them equal. Run the suite to get fresh numbers on
your machine (absolute figures are machine-dependent; the listed magnitudes are
prior local measurements):

| rewrite | what it does | certifying law | demo / prior measure |
|---|---|---|---|
| **semijoin** | `filter (member · ys)` O(n·m) scan → build-once hash-index probe | `List.elem_filter_eq_index_probe` | `semijoin_test` — ~100–476× on low-hit-rate data |
| **map∘filter fusion** | two passes → one `filterMap` pass | `List.map_filter_filterMap` | `fusion_test`; vs `clojure.core` transducers ~4.5–11× (`affine`-style fused scan) |
| **loop-invariant hoist** | a fold-invariant subterm computed once, not per row | `List.sum_map_mul_const` + linearity | `faq_plan_test` — 592–4106× on the cross-stream nested-reduce shape |
| **parallel monoid fold** | sequential `foldl` → fork-join `r/fold` | `Nat.add_assoc` + identities (the associativity proof *is* the parallelization licence) | `parallel_fold_test` — ~1.3× (boxing-bound; unboxed `long[]` is the next win) |

The point of the table is not the constant: it's that **the optimization and its
soundness precondition are the same artifact** — a proven algebraic law — so the
fast path ships only when the kernel has certified it preserves the answer.

## Caveats / honesty

- absolute ms are machine- and JVM-warmup-dependent; trends are stable.
- the parallel-fold win is currently boxing-bound (~1.3×); the unboxed-`long[]`
  parallel path is identified but not yet the default.
- tropical / boolean carriers are certified end-to-end at the optimizer level;
  tropical *execution* (running the chosen plan) still needs `ENat` runtime codegen
  — the rewrite + proof are complete, the lowering is the open item.

## See also

- [`PROGRAMMING_MODEL.md`](PROGRAMMING_MODEL.md) — how the malli schema licenses these
  rewrites.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) §3 — the cost model / planner (the two cost dimensions).
