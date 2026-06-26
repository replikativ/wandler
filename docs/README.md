# Wandler — documentation

Wandler is a **verified data-pipeline compiler**. You write ordinary Clojure pipelines
(`map`/`filter`/`reduce`/`group-by`/`join`) as `a/defn`s; wandler elaborates them to terms in
the [ansatz](../../ansatz) CIC kernel — the same kind of kernel that checks Lean 4 / Mathlib —
**optimizes** them by rewriting where *every adopted rewrite carries a machine-checked proof
that the optimized pipeline equals the one you wrote*, and **lowers** them to fast Clojure
(fused single passes, factorized joins, incremental views, parallel folds).

The discipline under all of it: a hard line between what the kernel **proves** and what wandler
**trusts** (a foreign engine, a measured statistic, a floating-point weight, the async clock).
Every doc keeps that line visible with `✓ proven` / `⚠ trusted` callouts.

## Start here

New to wandler? Read the **[Tutorial](TUTORIAL.md)** — it walks a single pipeline up a gradual
ladder (no types → inferred types → explicit types) and then through every feature, with every
example validated end-to-end.

## Guides

| Document | What it covers |
|----------|----------------|
| **[Tutorial](TUTORIAL.md)** | The gradual ladder: plain Clojure → inferred types → explicit types → verbs, streaming, infinite sources, the JIT. The runnable spine. |
| **[Architecture](ARCHITECTURE.md)** | The engine: elaborate → optimize → lower; the three seams into ansatz; the trust boundary (translation validation); the module map; mode dispatch. |
| **[Optimizer](OPTIMIZER.md)** | Term-as-IR, simp-as-certifier; fusion; the FAQ factorization family (group-by-over-join, filter pushdown, reorder, semijoin, pre-agg, grace-hash); the cost model; the e-graph search. |
| **[Streaming](STREAMING.md)** | DBSP: Z-sets, linear vs bilinear operators, the ∂ pass, the query interpreter, `dbsp/ivm`, the async push graph, and exactly where incremental maintenance stops being exact. |
| **[JIT](JIT.md)** | The verified JIT: planning re-optimization (`optimize-measured`) and runtime hot-swap (`PSwapNode` / guarded-adaptive driving). Profile steers, the kernel guarantees. |
| **[Engines](ENGINES.md)** | Cross-engine integration & end-to-end planning: datahike/stratum as trusted axioms, the plan-lens `lift`/`lower` bridge, the cost handshake, and a query that spans two databases — certified. |
| **[Inference](INFERENCE.md)** | Inference = sum-product over a chosen semiring: variable elimination as the certified FAQ factorization, the carriers (counting / Bool / tropical / probability / provenance), WMC, and the FinDist/Giry monad. |
| **[Programming model](PROGRAMMING_MODEL.md)** | The formalization: the malli → type functor, dependent types in practice, the semiring view of aggregation and inference, and the gradual-typing ladder — honest about proven vs aspirational. |
| **[Reference](REFERENCE.md)** | The verb vocabulary (what each lowers to), type-annotation forms, idioms, the inspection API, and the honest limits (clean rejections, the linearity edge). |
| **[Benchmarks](BENCHMARKS.md)** | What the verification actually buys, measured. |

## The trust ledger, in one table

| Proven by the CIC kernel (L0) | Trusted boundary (L2) |
|---|---|
| Fusion (`fused ≡ naive`) | The async clock — when deltas arrive |
| Join factorization / filter pushdown / reorder | Measured selectivity & cardinality (the JIT's input) |
| Incremental ∂ stages (bilinear join, linear filter, sum homomorphism) | Foreign engine results (datahike / stratum / a `register-foreign!` fn) |
| Productivity (`Strm` vs `List` typing) | Floating-point probability weights |
| Monoid laws → parallel-fold licence | |

An L2 input can make wandler *slower* or feed it *wrong data*; it can never make a verified
pipeline compute a different function than the code you wrote.
