# Wandler — a verified data-transformation runtime

> *Wandler* (German: **transducer / converter**) — an **experimental** verified runtime for
> ordinary Clojure data pipelines. You write `map` / `filter` / `reduce` / `group-by` / `join`;
> wandler optimizes them, and a proof kernel checks every rewrite before it runs.

> ⚠️ **Experimental research software.** Early-stage — APIs and proofs are still evolving and it is
> not production-hardened. Expect rough edges.

Wandler is built on [`ansatz`](https://github.com/replikativ/ansatz) — the Lean4-in-Clojure proof
kernel + DSL. **Ansatz formulates and proves; Wandler transforms and optimizes.**

Under the hood, your pipeline is elaborated to a term in ansatz's CIC kernel (the same kind of kernel
that checks Lean 4 / Mathlib), **optimized by certified rewriting**, and lowered back to fast Clojure.
Every adopted rewrite carries a machine-checked proof that `optimized ≡ original` — *translation
validation*, checked per program by that kernel. The optimizer's search is untrusted; only the
certificate is, so a bad rewrite is rejected, never miscompiled. The payoff: because the kernel proved
your fused pipeline equals the obvious one, wandler is free to *run* the fast one — a single pass, an
eliminated join, an incremental view, a parallel fold — and you still get the answer the naive code
would give. **Verification licenses the fast representation.**

**New here? Start with the [Tutorial](docs/TUTORIAL.md)** — it walks one pipeline up
a gradual ladder (no types → inferred types → explicit types) and then through every
feature, with every example validated end-to-end. The quickstart below is the 30-second
version.

## Quickstart

Wandler's complete law set needs full Lean Init. Import an Init NDJSON export
once into a fresh directory using the current Ansatz store format:

```sh
clj -J-Xmx8g -M -m ansatz.import .wandler/stores/init path/to/init.ndjson init
```

The export used by the test suite is available as `init.ndjson.gz` on the
[Ansatz 0.2.68 release](https://github.com/replikativ/ansatz/releases/tag/0.2.68).
Decompress it before importing. The published store index currently offers Mathlib;
it does not offer a standalone `init` download. Zero-argument `(a/init!)` loads
bundled medium Init, which does not contain Wandler's complete law prerequisites.

```clojure
(require '[ansatz.core :as a] '[wandler.core :as w] '[malli.core :as m])
(a/init! ".wandler/stores/init" "init") ; full Init, imported in current format
(w/install!)            ; batch + relational surface
(w/install-streaming!)  ; the incremental / async / Strm modes
(w/install-laws!)       ; the proven FAQ optimization-law DAG
```

Ordinary Clojure — verified, fused, certified, compiled:

```clojure
(a/defn big-squares [xs :- (List Nat)] Nat
  (reduce + 0 (map (fn [x] (* x x)) (filter (fn [x] (< 10 x)) xs))))

(big-squares [3 5 12 7 20 1])             ;=> 544          ; 12² + 20²
(:stages-after (w/explain 'big-squares))  ;=> [foldl]      ; three passes fused into one
(:verified? (w/explain 'big-squares))     ;=> true         ; kernel proved fused ≡ naive
```

Give it record types, and the optimizer doesn't just fuse — it **factorizes**: a
group-by-over-join is rewritten so the join is never built (O(N²) → O(N)), carried by
a proof:

```clojure
(m/=> rev-by-region
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]
             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]]
   [:sequential :int]])

(a/defn rev-by-region [custs orders]
  (map (fn [g] (reduce + 0 (map (fn [[c o]] (:amount o)) g)))
       (vals (group-by (fn [[c o]] (:region c))
                       (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders)))))

(:rewrites (w/explain 'rev-by-region))  ;=> [:groupby-reduce-join :hoist-index]   ; join eliminated, 6→4 passes
```

No schema to hand? Read it off a data sample — `(w/induce-types! #'f sample)` infers
the malli schema, and the same-named `a/defn` picks it up. The **same** verified
pipeline also runs incrementally over change streams (`w/run … :mode :incremental`) and
re-plans itself against measured data (`w/optimize-measured`). See the
[Tutorial](docs/TUTORIAL.md) for all of it.

## The stack

```
   Clojure surface             (a/defn revenue [orders :- (List …)] …
   map/filter/reduce/             (reduce + 0 (map :amt (filter premium? orders))))
   group-by/join/records/             │
   transducers                        │  ELABORATE   (SEAM 1 — term/macro elaborator registries,
                                      ▼               lean4's elab_rules / macro_rules)
   kernel IR = CIC term        List.foldl + 0 (List.map amt (List.filter premium? orders))
   (the term IS the plan)             │
                                      │  OPTIMIZE    (SEAM 2 — a/optimize-hook:
                                      │               simp fusion + cost search + relational laws)
                                      ▼
                              term′ + PROOF: term = term′   ◀── the kernel CERTIFIES (yes/no)
                                      │
                                      │  LOWER       (SEAM 3 — a/codegen-registry:
                                      ▼               unboxed scans, parallel monoid fold, hash joins)
   fast Clojure                an ordinary fn
```

Integration with ansatz is **three additive seams** — no fork, no carve. ansatz alone
still runs base `a/defn`; ansatz + wandler is the full pipeline. The optimizer that
proposes a rewrite is *untrusted* — only the kernel's check of its proof matters, so a
rewrite that doesn't preserve meaning is dropped, never shipped.

## Trust ledger

| level | meaning | enforced by |
|---|---|---|
| **L0** | kernel-certified — an algebraic law proven as a CIC term | the kernel's `check-constant` (the path that admits Mathlib) |
| **L1** | trusted lowering of a proven-equal term | runtime/codegen implementation and differential tests |
| **L2** | trusted oracle — numeric/external, *not* a CIC proof | measured selectivity, WMC counts, floating-point weights, external engine planners, the async clock |

L0 highlights: pipeline fusion (`map∘filter → filterMap`, fold fusion); relational
pushdown + semijoin (`List.elem_filter_eq_index_probe`); aggregation-through-join
factorization (the **FAQ frame rule**, **semiring-generic** — one proof certifies
counting (`Nat`), boolean provenance (`Bool`, ∨/∧), and tropical shortest-path
(`ℕ∞`, min/+)); the DBSP increment laws (bilinear join, linear filter, sum
homomorphism) and Z-set group laws; the parallel-fold licence (the associativity proof
*is* the fork-join soundness certificate). An inaccurate cost estimate can select a
slower certified plan. Correct execution also
depends on the lowering, foreign-engine contracts, and runtime guards; the rewrite proof
does not independently verify those implementations. Measured impact: [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md) (FAQ
factorization: 4× → 22× and widening, same certified answer).

## Documentation

**[The documentation index](docs/README.md)** organizes everything by topic. The short path:

1. **[Tutorial](docs/TUTORIAL.md)** — the gradual ladder (no types → inferred → explicit) then every feature; the runnable spine.
2. **[Reference](docs/REFERENCE.md)** — the verb vocabulary, type-annotation forms, idioms, and the honest limits.
3. **The engine** — [`Architecture`](docs/ARCHITECTURE.md) (the three seams · trust boundary · module map) · [`Optimizer`](docs/OPTIMIZER.md) (fusion · the FAQ factorization family · cost model) · [`Streaming`](docs/STREAMING.md) (Z-sets · the ∂ pass · DBSP · the linearity edge) · [`JIT`](docs/JIT.md) (measured replanning + runtime hot-swap) · [`Engines`](docs/ENGINES.md) (datahike/stratum integration · end-to-end cross-engine planning).
4. **The model** — [`Inference`](docs/INFERENCE.md) (sum-product over a semiring · variable elimination · WMC · the FinDist monad) · [`Programming model`](docs/PROGRAMMING_MODEL.md) (malli→type functor · dependent types · the semiring view · the gradual ladder) · [`Benchmarks`](docs/BENCHMARKS.md).

## Layout

The verified engine lives under `wandler.*`; `wandler.core` is the public front door. A
compact map (full version in [`ARCHITECTURE.md`](docs/ARCHITECTURE.md)):

| prefix | role |
|---|---|
| `wandler.core` | the front door: `install!` / `install-streaming!` / `install-laws!`, `run`, `explain`/`plan`, `optimize-measured` |
| `wandler.surface.*` | SEAM 1 — the Clojure verb vocabulary → kernel terms (collections · records · relational · malli · streams) |
| `wandler.optimize` + `.optimize.*` | SEAM 2 — `certify` (the kernel gate) · `cost` · `physical` · `faq` · `egraph` · the term↔plan lens |
| `wandler.laws.*` | the proven law DAG — FAQ frame family · semijoin/reorder · grace-hash · fusion; strict admission |
| `wandler.runtime` · `wandler.algebra` · `wandler.core.*` | SEAM 3 — lowering (unboxed scans, hash joins) + the parallel-fold monoid core |
| `wandler.exec.*` | the execution modes: `zset`/`dbsp*` (incremental) · `live`/`fork` (async push) · `mode` (the lattice + ∂ pass) |
| `wandler.jit.*` | the JITs: planning (`estimate`/`pgo`) + runtime hot-swap (`swap`/`stream`) |
| `wandler.inference.*` | semiring readings of the same core (semiring · dist · wmc · giry · lens) |
| `wandler.bridge.*` · `wandler.backend.*` | external engine adapters (datahike · spindel · stratum) + native/columnar backends — optional deps |

## Status

The verified optimizer, surface, and execution engines are the single canonical
implementation under `wandler.*`. Every adopted rewrite is independently kernel-
`check-constant`-certified; a law that fails to admit degrades to a missed
optimization, never a miscompile. The **FAQ frame rule is semiring-generic** (counting /
boolean / tropical carriers ship), `mode/execute` picks the lowering from the source type
(batch fuse · pull-incremental · async push), and the surface vocabulary is data.

Wandler pins Ansatz **0.2.115**. `:local-ansatz` exercises the sibling checkout.
Ansatz now uses a versioned CBOR store: older stores need re-importing; there is no
in-place migration. The full integration suite needs the full Init export (see Tests).
Validation: **429 tests / 1945 assertions**, zero failures/errors against the
published dependency; the sibling Ansatz checkout also passes the full suite.

## Tests

```
clj -M:test                 # full Init store or NDJSON fixture under test-data
clj -M:test:logicng         # + the LogicNG WMC path
WANDLER_REQUIRE_STORE=1 clj -M:test  # fail if full Init is unavailable
clj -M:local-ansatz:test    # compatibility with ../ansatz HEAD
clj -M:local-raster:test -n wandler.raster-test  # current optional numerical adapter
clj -J-Xmx8g -M bin/smoke-init.clj .wandler/stores/init init  # public bootstrap
```

## License

Copyright © 2026 Christian Weilbach. Distributed under the [Apache License 2.0](LICENSE).
