# Physical planner — the chunked-array model

How a verified logical pipeline becomes a physical execution, below the mode lattice. The seam is
`wandler.exec.mode/execute` → `route` (mode) → `wandler.exec.physical/physical-route` (batch
realization over the plan lens). This doc pins the *array* realization.

## The unifying representation: a transducer over unboxed column-array chunks

The right physical shape is NOT "preallocate one finite array" — it is the **chunked-array
transducer**: process the input in **fixed-size chunks** (e.g. 8192 elements, L2-resident), each chunk
a **preallocated unboxed array**, with a **monoid merge** combining per-chunk results.

- the **bounded unit is the chunk**, so memory is bounded for *any* input length (finite or streaming);
- each chunk is unboxed (`long[]`/`double[]`) → primitive speed, SIMD/GPU eligible;
- the per-chunk results combine by a monoid → parallel + out-of-core for free.

This is exactly stratum's execution model (8192-element column chunks + per-chunk SIMD kernels +
monoid accumulators) and raster's per-kernel array op — and it generalizes our eager `amapl`/`apfoldl`.

## The certificate we already own

The law that licenses chunking is `fold (a ++ b) = merge (fold a) (fold b)` for an associative step —
i.e. the **verified monoid** (`Std.Associative`, the `apfoldl` parallel-fold proof). So the boundedness
"analysis" is really **chunkability**, and for the load-bearing case (folds) the certificate already
exists; we gate on it, we don't reprove it.

| plan op | chunk behavior | certificate (have it) |
|---|---|---|
| map / filter / filterMap / flatMap | per-chunk independent (concat outputs) | fusion laws |
| foldl / aggregate | per-chunk fold + monoid merge | `monoid-fold-op` / `Std.Associative` |
| join / group_by | cross-chunk hash (bounded by the table) | memory-budget + grace-hash / pre-agg (#74/#75/#77) |

Cardinality (`optimize.cost/pipeline-resources`) then only sizes the chunk count / picks dense-vs-hash —
it never gates correctness (same role stratum's zone-maps play).

## One representation, three chunk kernels (adapter seam)

`physical-route`'s `:array` tag = chunked-array execution with a **pluggable per-chunk kernel**, all
bounded, all certified by the same monoid proof:

- **clojure-chunked** (always available): partition → per-chunk unboxed op → reduce-merge. Generalizes
  `apfoldl`. No deps; the equal-result fallback.
- **raster** (optional, numerical, `wandler.backend.raster` under the `:raster` alias): per-chunk →
  raster `deftm`/`par` → SOAC-fused SIMD/GPU. Whole-array is "one chunk". Detect-and-lower adapter
  (registers into the `:array` seam); falls back to clojure/eager when absent. v1 lowers the canonical
  Float reductions (`Σxs`→`par/sum`, `Σx²`→`par/dot-product`) and is CORRECT, but PERF FINDING: these
  cheap memory-bound reductions do NOT beat C2-auto-vectorized Clojure `areduce` over a `double[]`
  (~1.1× kernel-only) and LOSE once the `List→double[]` boundary is paid (~0.6×). Raster's real edge is
  COMPUTE-heavy custom kernels (the general `deftm`+`compile-aot` path), parallelism, GPU, and
  array-NATIVE data (no conversion) — so the cost model must only route to raster when the workload
  justifies it. Packaging caveat: raster 0.1.3's git deps (pattern/typedclojure) don't survive the
  Maven pom boundary, so the `:raster` alias replicates them consumer-side (upstream fix = publish them).
- **stratum** (optional, columnar/OLAP): emit columns `{:type :data array}` to stratum's planner, OR
  `idx-scan` stratum chunks into our verified kernel. Both directions share the chunk shape, because
  stratum's per-chunk SIMD kernels are monoid-accumulating like ours.

Layering stays clean: ansatz never depends on these; raster/stratum enter via `register-engine!` /
`register-foreign!` as typed boundaries, exactly like the existing engine bridges.

## Scenarios

| # | scenario | bounded unit | backend | certificate |
|---|---|---|---|---|
| 1 | `Σ (x·x)` over a 10k double[] | whole = 1 chunk | raster SOAC-fused SIMD | monoid + |
| 2 | `Σ price·qty` over 100M rows | 8192-chunk | chunked SIMD, monoid-merge | apfoldl / assoc |
| 3 | `group-by dept Σ salary` over a column table | chunk + dense-acc | stratum PDenseGroupBy | group-by factor (#77) |
| 4 | custom verified aggregate over a 1B-row stratum index | stratum chunk (lazy) | stratum source → kernel | monoid + validity |
| 5 | large join `customers ⋈ orders` | hash partition (budgeted) | stratum hash-join / grace-hash | join laws + spill (#75) |
| 6 | live incremental aggregate over a changing set | delta chunk | spindel dual-interval | DBSP (#79–82) |
| 7 | verified per-chunk transform → stratum OLAP agg | shared 8192 chunk | chunked-transducer glue | per-chunk fusion + monoid |

Scenario 7 (our verified kernel feeding stratum's OLAP) falls out for free: both sides are
monoid-accumulating transducers over the same chunk.

## Sequencing

1. **Chunkability classifier** over the plan lens — tag each op `:per-chunk` / `:monoid-merge` /
   `:cross-chunk`, reading the existing `monoid-fold-op` certificate for folds. (the in-core analysis)
2. **clojure-chunked `:array` kernel** — partition → per-chunk → merge, generalizing `apfoldl`; the
   always-available realization. Wired as a `physical-route` tag behind `:eager`-default.
3. **raster adapter** — optional detect-and-lower for the numerical per-chunk kernel.
4. **stratum adapter** — optional, both directions (destination + source), the chunked-transducer glue.

Each additive on the `physical-route` / plan-lens spine; `:eager` stays the default until the classifier
makes the choice automatic.
