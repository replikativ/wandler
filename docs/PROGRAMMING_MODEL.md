# The Wandler programming model — four structures, one certified core

> Companion to [`CORE.md`](CORE.md) (the runtime architecture). This document is the
> *conceptual* spec: what algebra the system is, and why the same verified core serves
> batch query optimization, incremental view maintenance, optics, and probabilistic
> inference. Every claim below is implemented by a named namespace and gated by the
> kernel; this doc points at the code rather than restating proofs.

Wandler is a **verified monoidal category** carrying four interacting structures. The
bet — and the thing the kernel checks — is that they *cohere*: the same pipeline can be
read through any structure and the readings agree up to a kernel-checked equality.

| # | structure | reading of a pipeline | home |
|---|---|---|---|
| 1 | **semiring / ring** | sum-of-products aggregate | `wandler.inference.semiring` |
| 2 | **differential / comonad** | incremental delta (DBSP) | `wandler.exec.dbsp*`, `wandler.exec.zset` |
| 3 | **lens / optic** | the backward direction | `wandler.inference.lens` |
| 4 | **measure** | a weighted distribution | `wandler.inference.{dist,wmc,giry}` |

The sections are numbered so the cross-references scattered through the source
(`PROGRAMMING_MODEL.md §N`) resolve here.

## §1 — Overview: the certified core

A pipeline is elaborated to a CIC kernel term (ansatz). The optimizer rewrites the term
by *certified rewriting*: every adopted rewrite carries a kernel proof `optimized ≡
original`, re-checked per program by `wandler.optimize.certify/verified-rewrite?`
via independent `env/check-constant`. The search is untrusted; only the certificate is.
This is *translation validation*, and it is what lets all four structures share one
optimizer — a structure-specific rewrite is legal exactly when its proof type-checks.

## §2 — Structure 1: the semiring core

`Rel A S := A → S` over a semiring `S` is the unifying object (`wandler.inference.semiring`).
A query is a sum-of-products in `S`; choosing `S` chooses the interpretation:

- `S = Nat` (`+`, `·`, 0, 1) → **counting / SUM** aggregates.
- `S = Bool` (`∨`, `∧`, ⊥, ⊤) → **existence / provenance**.
- `S = ℕ∞` tropical (`min`, `+`) → **shortest-path / optimization** (`wandler.laws.tropical`).

**Transducers are the product; reducers are the sum.** A `map`/`filter`/`mapcat`
pipeline is the product side (deforestation/fusion); a `reduce`/`foldl` is the sum side
(monoid aggregation). The two compose, and the carrier registry
(`wandler.laws.semiring`) lets the physical optimizer instantiate one *semiring-generic*
law per carrier rather than re-proving per type.

## §3 — Sum-product optimization & FAQ factorization

The headline win is **aggregation-through-join factorization**: a `Σ` over a `Map.join`
factors into per-key bucket sums without materializing the pair list — the FAQ frame
rule. It is proven once, generically over any `WSemiring`, as
`Map.foldl_join_frame_generic` / `Map.foldl_join_sum_factor_generic` (the pre-aggregated
O(distinct-keys) index), and routed by carrier registry rows. See
[`SPILL_AND_FAQ_PLAN.md`](SPILL_AND_FAQ_PLAN.md) for the spill/index strategy ladder, and
`wandler.laws.faq` for the proofs.

## §4 — The optimizer as certified rewriting

`wandler.optimize` is the search; `…/certify` is the gate; `…/cost` is the resource
model; `…/physical` picks the realization. A rewrite is adopted iff
`verified-rewrite?` *and* it lowers `cost`. The e-graph layer (`…/egraph`) and CSE
(`…/cse`, a zeta/`let` defeq — certificate is `Eq.refl`) widen the search without
widening the trust base.

## §5 — Cost model

`wandler.optimize.cost` costs *trees* and *lets* (tree/binder-aware,
descriptor-driven), so the planner rewards sharing and can price a backend push-down.
The op-cost table is the engine seam. See [`COST_MODEL_REDESIGN.md`](COST_MODEL_REDESIGN.md).

## §6 — Physical planning

`wandler.optimize.physical` + `wandler.exec.physical` choose the realization over
the **plan lens** (`wandler.optimize.plan`, the single term↔plan IR): in-memory hash
join, nested-loop, grace-hash spill, or the pre-aggregated index — each certified equal
to the naive plan. Boundedness can route bounded data to a zero-alloc backend
(`wandler.backend.raster`).

## §7 — Engines behind one spec

External engines (datahike, stratum, spindel) are *trusted oracles* behind a typed API
spec; only the algebraic certification layer is kernel-checked. The plan lens is the α/γ
bridge that lets the same certified query lower to different engines
(`wandler.bridge.*`).

## §8 — The malli → type functor

One total functor `F(schema) = Subtype Value(γ)` lifts malli schemas to refinement types
(`ansatz.malli` / `ansatz.surface.schema`), so `defn → a/defn` keeps your schema and the
planner reads it to factor an aggregating join.

## §9 — Records & refinement

`[:map …]` arguments become refinement records (Subtype: read/write/discharge), giving
O(1) field access plus the relational laws over named projections.

## §10 — Runtime lowering

Verified terms lower to fast Clojure (`wandler.runtime`): unboxed scans, hash joins, and
the law-gated licences (`wandler.algebra`) — e.g. a kernel-proven associative monoid is
the *certificate* that licenses a parallel fork-join fold.

## §11 — Modes: batch · incremental · async

`wandler.exec.mode` + `mode-laws` form a mode lattice; `mode/execute` picks the lowering
from the *type* (batch fuse / pull-incremental / push live graph), and a `∂` pass mixes
them in one certified pipeline.

## §12 — Structure 3: lenses / optics (the backward direction)

`wandler.inference.lens` is the well-behaved corner of inversion: a lens between a whole
and a part composes hierarchically, with the get/put laws kernel-proven (the product-lens
brick). This is the *backward* reading of a pipeline — how an update to an output
propagates to an input — dual to the forward semiring reading of §2.

## §13 — Structure 2: differentiation & incremental view maintenance

The differential reading (`wandler.exec.dbsp*`, `wandler.exec.zset`,
`wandler.dbsp-stream`) maintains a view *incrementally*: `∂(filter)` is linear,
`∂(join)` is the bilinear product rule, deletions ride Z-sets (`A → Int`). The stream
operators `z⁻¹ / D / I` and the chain rule are proven, with `D∘I = id`. This is also
where the FAQ optimizer integration lands (§3): an aggregating query lowers to a verified
physical plan, cross-validated against the runtime semiring engine — one query, two
engines, one answer.

The **coherence audit** tracks the remaining `∂` debt:
- **B5** — `∂` over an abstract abelian group / a guarded `Strm` (the modal-FRP corner).
- **S2** — `∂` uses *only* the abelian-group axioms, so it generalizes off `Int` to any
  group-carried Z-set.

## §14 — Structure 4: measure (probabilistic inference)

The same semiring core, read with a measure, is probabilistic inference:
`wandler.inference.dist` (FinDist as the monad view of `Rel A S` — return/bind = unit /
sum-product), `wandler.inference.wmc` (weighted model counting, pluggable enumeration /
BDD backend), and `wandler.inference.giry` (the measure monad). Probabilistic inference =
the same sum-product planner with a weighted carrier.

## §15 — Certified coherence: the bet

The four structures are not four programs — they are four *readings* of one verified
core, and the kernel checks that they agree where they overlap (semiring ↔ measure via
WMC; forward ↔ backward via the lens laws; batch ↔ incremental via `∂`/DBSP). That
certified coherence — not any single optimization — is the thesis.
