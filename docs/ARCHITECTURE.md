# Architecture — the spine

Wandler is a compiler with a proof obligation. You write an ordinary Clojure data
pipeline; wandler **elaborates** it to a term in the `ansatz` CIC kernel (the same
kernel that checks Lean 4 / Mathlib), **optimizes** it by rewriting — where every
rewrite it keeps carries a machine-checked proof that the optimized term equals the
one you wrote — and **lowers** it to fast Clojure. This document is the map: how the
three stages fit together, how wandler plugs into ansatz without forking it, and where
the proven/trusted line runs. Each subsystem then has its own deep doc (linked at the
bottom).

The slogan, and the whole design: **verification licenses the fast representation.**
Because the kernel proved your fused pipeline equals the obvious one, wandler is free to
run the fused one — single pass, unboxed arrays, a parallel fold, an incremental view —
and you still get the answer the naive code would give.

## The pipeline: elaborate → optimize → lower

```
 Clojure form
     │  ELABORATE        wandler.surface.*   (registered verbs → kernel ops)
     ▼
 kernel term  (an ansatz CIC Expr — the IR *is* the proof object)
     │  OPTIMIZE + CERTIFY   wandler.optimize.*  (search proposes; the kernel certifies)
     ▼
 kernel term  (faster, with a proof  optimized ≡ original)
     │  LOWER (codegen)   wandler.runtime    (lowering table → ordinary Clojure)
     ▼
 (fn [..] ..)   — a plain Clojure function in the var
```

- **Elaborate.** `(a/defn order-total [os] (reduce + 0 (map :amount os)))` becomes the
  kernel term `List.foldl Nat.add 0 (List.map … os)` — `map`/`filter`/`reduce` →
  `List.map`/`List.filter`/`List.foldl`, `group-by`/`join` → `Map.group_by`/`Map.join`.
  The intermediate representation **is** a kernel `Expr`, not a bespoke AST. That is the
  trick the rest depends on: optimization is term rewriting, and "this rewrite is correct"
  is a proposition the kernel can check.
- **Optimize.** The two passes fuse into one `List.foldl` with the projection inlined into
  the step — deforestation justified by the `List.foldl_map` law, *proved*, not a
  heuristic. Each adopted rewrite produces a proof term `optimized = original`.
- **Lower.** The certified term is codegen'd to a plain `(fn [os] …)` calling a handful of
  `wandler.runtime` ops (`amapl afilter afoldl apfoldl unfold-take`) plus `clojure.core`.

## The three seams into ansatz

Wandler is **not** a fork of ansatz — it is an additive integration through three
extension points ansatz exposes. `wandler.core/install-registries!` fills all three; that
is the entire act of "becoming wandler":

```clojure
(defn install-registries! []
  (coll/install!) (rec/install!) (rel/install!)   ; SEAM 1 — surface vocabulary
  (rt/install!)                                    ; SEAM 3 — runtime lowering
  (reset! a/optimize-hook optimize-hook)           ; SEAM 2 — the certified optimizer
  :installed)
```

1. **SEAM 1 — the surface elaborator registries.** `wandler.surface.*` registers term and
   macro elaborators through `ansatz.surface.api` (Lean's `elab_rules` shape). They turn
   Clojure verbs into kernel terms: `collections` (`map`/`filter`/`reduce`/`for`),
   `relational` (`group-by`/`join`/`distinct`/`sort`), `records` (malli-typed maps),
   `strings`, `option`, and `streams`. The vocabulary is a *closed, growing* set —
   compositional inside it, a clean rejection at its edge (`(w/vocabulary)` is the table).
2. **SEAM 2 — `a/optimize-hook`.** `core/optimize-hook` is the certified optimizer, invoked
   by ansatz inside `a/defn`'s `define-verified` *before the Clojure var exists*. It calls
   `wandler.optimize/optimize-body`, records the report under the kernel constant's name
   (the source for `explain`/`plan`), and returns the optimized term. Bind `*optimize*` to
   `false` to pass terms through untouched.
3. **SEAM 3 — `a/codegen-registry`.** `wandler.runtime/install!` points ansatz's
   codegen-registry at `lower` for every head in the `lowering-table`. `register-lowering!`
   is the open extension point: a vocabulary or user adds a head→Clojure-form lowering
   without editing the core, and it is auto-installed. (`install!` additionally calls
   `kmap/install!` and `algebra/install!` for the env-dependent pieces; `install-streaming!`
   and `install-laws!` layer the mode lattice and the proven law DAG on top.)

The seams are *registries*, so vocabularies, laws, and backends are additive. Ansatz never
changes; wandler is data poured into its extension points.

## The trust boundary — translation validation

This is the core idea, so it gets room. The optimizer is a search: recognizers, a cost
model, an e-graph, heuristics. **None of that is trusted.** What is trusted is exactly one
thing — the kernel's re-check of the proof the search emits.

```
        proposes (UNTRUSTED)                  certifies (TRUSTED)
   ┌────────────────────────────┐       ┌────────────────────────────────┐
   │  wandler.optimize.*:       │       │  ansatz CIC kernel:            │
   │  recognizers, cost model,  │  ──►  │  TypeChecker.check on the      │
   │  e-graph, FAQ strategies   │       │  proof  optimized ≡ original   │
   └────────────────────────────┘       └────────────────────────────────┘
```

The gate is `wandler.optimize.certify/verified-rewrite?`. It builds the goal `@Eq T orig
term`, closes it over the pipeline's free variables, and runs the kernel's **strict**
`TypeChecker.check` on the proof — re-checking *every* application argument (the same
strictness that admits a Mathlib declaration), not the lenient `inferType`. Then
`certify/optimize` is sound *by construction*:

```clojure
(if (or ok (not (:changed? res)))
  (assoc res :verified? ok)
  ;; unverifiable change → reject it, keep the original
  {:term term :proof nil :changed? false :verified? true})
```

If a proposed rewrite's proof does not type-check, the change is **dropped and the original
term kept**. There is no path by which a wrong rewrite becomes a wrong program; the failure
mode is "missed optimization", never "miscompilation". And the proof is *per program* — a
translation validation, not a once-and-for-all compiler-correctness theorem. `:verified?
true` in `(w/explain …)` means a kernel proof object `optimized ≡ naive` type-checked.

> **✓ proven.** Every `:verified? true`, every `optimized ≡ naive`, is an L0 fact a machine
> checked. The optimizer can be arbitrarily clever or arbitrarily buggy; only its output
> proof matters, and that is re-checked by the kernel from scratch.

### The trust ledger

Not everything is kernel-proven, and wandler keeps a hard line between what it **proves**
(L0) and what it **trusts** (L2), never blurring the two:

| Proven by the CIC kernel (L0) | Trusted boundary (L2) |
|---|---|
| Fusion (`fused ≡ naive`, the `List.*` deforestation laws) | Foreign engine results — `datahike.q`, stratum (admitted as **typed axioms** via `register-foreign!`) |
| FAQ join factorization / filter pushdown / drive-direction reorder (`wandler.laws.*`) | Measured selectivity & cardinality (the JIT's *input*) |
| The ∂ increment laws (bilinear join `Zproduct_product_rule`, linear `Mode.diff_async_dist`) | The clock — when async deltas arrive |
| Productivity (`Strm A` vs `List A` typing) | Floating-point probability weights (`inference.*` / WMC) |
| Monoid laws → parallel-fold licence (`wandler.algebra`) | Monte-Carlo / external #P solvers (Giry expectation, model counts) |

`wandler.exec.mode/references-axiom?` flags any term that leans on an L2 axiom, so a leaf is
classified `:verified` (codegen'd from a kernel term) or `:trusted` (a black box). An L2
input can make wandler choose a *slower* correct plan or feed it *wrong data*; it can never
make a verified pipeline compute a different function than the code you wrote.

## The module map

| Namespace(s) | What it owns |
|---|---|
| `wandler.core` | the front door — `install!` / `install-streaming!` / `install-laws!`, `run`, `explain`, `plan`, the JIT loop (`optimize-measured`) |
| `wandler.surface.*` | **SEAM 1** — the elaborator vocabulary (collections, relational, records, strings, option, streams, malli refinements) |
| `wandler.optimize.*` | **SEAM 2** — the certifier (`certify`), the cost model (`cost`), CSE (`cse`), the e-graph (`egraph`), FAQ/physical strategies (`faq`, `physical`), and the plan lens (`plan`) |
| `wandler.laws.*` | the **proven** relational law DAG — `faq`, `groupby`, `reorder`, `grace`, `semiring`, `relational` — each `check-constant`-verified, installed by `install-laws!` |
| `wandler.exec.*` | the mode lattice + lowering — `mode`, the ∂ pass + Z-set engine (`zset`, `dbsp`), the push live graph (`live`), the physical/array backends (`physical`) |
| `wandler.jit.*` | the measure→replan loop — `estimate`, `pgo`, `swap` (hot-swap a re-optimized plan) |
| `wandler.infer` / `wandler.inference.*` | malli schema **induction** from data (`induce-types!`); the inference structures (semiring sum-product, WMC, Giry) |
| `wandler.algebra` | the `WSemiring`/monoid registry + `monoid-licence` (the parallel-fold gate) |
| `wandler.bridge.*` | **trusted** external-engine adapters — `datahike`, `stratum`, `spindel` |
| `wandler.runtime` | **SEAM 3** — the codegen lowering table + the specialized unboxed/parallel runtime ops |

## The mode dispatch — the source type picks the lowering

A verified pipeline is *one logical object*; *how* it executes is a separate choice, and it
is read off the **type of its source**, not chosen by hand. `wandler.exec.mode/mode-of-type`
traces a kernel type's head constant to a mode (no unfolding — `Strm`/`Zset`/`List` stay
visible):

```clojure
(def head->mode {"List" batch, "Array" batch, "Strm" async, "LSeq" async, "Zset" diff …})
```

The mode is a point in a small lattice (after *Build Systems à la Carte* × Rhine clocks):
`:diff` (batch ⊑ differential), `:sched` (sync/pull ⊑ async/push), `:clock`. A pipeline's
mode is the `lub` of its sources; `route` then selects the γ-lowering:

- **`:batch-fuse`** — over `List`s: the fused, codegen'd function (the §1–§4 path).
- **`:incremental`** — each `List A` source is retyped `Zset A`; the **∂ pass**
  (`differentiate`) lowers the *same certified relational skeleton* into a Z-set/DBSP pull
  view, emitting a per-stage certificate that cites the kernel law licensing each op.
- **`:async` / `:async-incremental`** — each source is `Strm (Zset A)`; a push-driven live
  graph (`wandler.exec.live`).

`wandler.core/run` is the one front door over this — `:batch` runs the optimized term;
`:incremental`/`:async` retype the sources and differentiate the *naive* term (the
un-fused skeleton the differentiator can read). Crucially, `naive ≡ optimized` is
kernel-certified and each ∂ stage carries its own increment law, so **the route never
changes the trust story** — no re-elaboration, no re-proof. The depth (the ∂ functor's chain
rule, the linearity conditions, the honest non-linear edge) is **STREAMING.md**.

> **⚠ trusted edge.** The differential algebra at each tick is proven; the *clock* (when
> async deltas arrive) is the trusted, real-world part. Likewise a foreign source admitted
> via `register-foreign!` is a typed axiom leaf — the ∂ structure *around* it stays
> certified, the leaf itself is `:trusted`.

## Relationship to ansatz and external engines

**Ansatz is the substrate** (a dependency, never modified): the CIC kernel, the `a/defn`
front end, the `ansatz.surface.api` elaborator framework, and an **imported** Lean `Init`
library — `List.map`, `Nat.add`, the recursors are Lean's verbatim definitions (admitted
from a `lean4export` dump), so every `Init` theorem about them is directly usable, which is
what the fusion laws cite. Wandler's *owned* layer is small: the finite `Map`
(`{ List (K×V) // NodupKeys }`, `wandler.kmap`), the `WSemiring`/monoid algebra, and the
relational/FAQ laws — each its own `check-constant`-verified contribution.

**External engines are trusted boundaries.** `wandler.bridge.*` (datahike, stratum,
spindel) and any `register-foreign!` fn are admitted as **typed axioms**: opaque, named,
typed `dom → cod`, with an unverified body. A pipeline may use such a leaf; the structure
around it stays certified (the ∂ laws are payload-independent), but the leaf is reported
`:trusted`. That is the honest line — wandler proves the *plumbing*, and is explicit about
every black box the plumbing connects.

## Where to go next

- **[README](../README.md)** — the index and the 30-second quickstart.
- **[TUTORIAL.md](TUTORIAL.md)** — the gradual-typing ladder, every example REPL-validated:
  plain Clojure → inferred type → explicit type (and the join disappears) → modes → JIT.
- **[OPTIMIZER.md](OPTIMIZER.md)** — what the search actually does: the cost model, the FAQ
  factorization laws, the e-graph, CSE, the physical planner.
- **[STREAMING.md](STREAMING.md)** — the mode lattice, the ∂ pass, Z-sets/DBSP, the
  productivity gate, and the linearity conditions (where incremental maintenance stays exact).
- **[JIT.md](JIT.md)** — the measure→replan loop (`optimize-measured`) and verified hot-swap.
- **[PROGRAMMING_MODEL.md](PROGRAMMING_MODEL.md)** — the algebraic structures the laws live
  in (semiring/relational core, the DBSP differential, the optic/measure layers).
- **[REFERENCE.md](REFERENCE.md)** — the complete verb vocabulary and the honest edge cases.
- **[BENCHMARKS.md](BENCHMARKS.md)** — what the verification actually buys, measured.
```
