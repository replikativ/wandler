# Wandler Documentation

You write ordinary Clojure data pipelines. Wandler elaborates them to CIC kernel
terms, **optimizes them by certified rewriting** (every adopted rewrite carries a
machine-checked proof `optimized ≡ original`), and lowers them to fast Clojure.
The optimizer's search is untrusted; only the per-program certificate is — a bad
rewrite is *rejected*, never miscompiled.

For a one-page overview and the 30-second quickstart, see the
[main README](../README.md). This index organizes the rest by topic.

## 🚀 Getting started

| Document | What it covers |
|----------|----------------|
| [Tutorial](TUTORIAL.md) | One pipeline up a ladder: run verified → infer a schema → better algorithm → switch execution modes → self-optimize. **Start here.** |
| [Cookbook](COOKBOOK.md) | Copy-paste idioms that work today, the three install levels, and an honest list of what isn't wired yet. |
| [Surface](SURFACE.md) | The Clojure vocabulary you can write — `map`/`filter`/`reduce`/`group-by`/`join`, `for` comprehensions, windowing (`partition-all`), sampling (`take-nth`), `zip`/`interleave`, and how each lowers. |

## 🏗️ The engine

| Document | What it covers |
|----------|----------------|
| [Architecture](ARCHITECTURE.md) | The compile pipeline (surface → kernel term → optimize+certify → codegen), the one-way kernel trust boundary, the three seams, the runtime. |
| [Planner](PLANNER.md) | The optimizer/planner: certified rewriting, the cost model, the recognizer set (fusion, filter-pushdown, FAQ factorization, group-by-over-join), and physical planning. |
| [Programming model](PROGRAMMING_MODEL.md) | The four algebraic structures (semiring · differential · lens · measure) over one certified core, and the malli → type functor. |

## 📈 Going deep

| Document | What it covers |
|----------|----------------|
| [Streaming & modes](STREAMING.md) | Tumbling windows, downsampling, multi-stage stream pipelines; the batch / async / DBSP-incremental mode lattice; the linearity boundary; cross-engine routing. |
| [Dependent types](DEPENDENT_TYPES.md) | How a malli schema becomes a refinement type that drives the planner (carrier selection, FD scope quotient, relational-law licensing). |
| [Inference](INFERENCE.md) | Probabilistic inference and cross-engine queries as one semiring sum-product (FAQ variable elimination, FinDist monad, WMC). |
| [Gradual verification](GRADUAL.md) | The verification ladder — verify the algebra, treat the functions as parameters. |
| [Benchmarks](BENCHMARKS.md) | What the certified rewrites actually buy, with reproduction commands. |

## The one idea

> **Verification licenses the fast representation.** A pipeline is correct *by
> proof*, so the runtime is free to use the fast form — unboxed primitive arrays,
> a hash-map for a finite `Map`, a parallel fork-join fold, a join that never
> materializes its product — because the kernel already certified that the fast
> form computes the same value as the obvious one.

Built on [`ansatz`](https://github.com/replikativ/ansatz) — the Lean-4-in-Clojure
proof kernel + DSL. **Ansatz formulates and proves; Wandler transforms and optimizes.**
