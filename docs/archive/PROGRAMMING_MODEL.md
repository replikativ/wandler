# The programming model — four structures, one certified core

Wandler's identity is a **verified monoidal category carrying four algebraic
structures**, with the coherence between them machine-checked. You program in
ordinary Clojure; the structures are what the optimizer reasons *with* and what the
kernel certifies.

```
                    one certified core (the CIC kernel + Init)
                                   │
        ┌──────────────┬───────────┴──────────┬──────────────────┐
   1. semiring /   2. differential /     3. lens /          4. measure
      ring             comonad               optic              (probability)
   (aggregation,    (incremental view     (the backward       (inference as
    FAQ, joins)      maintenance, DBSP)    direction)          sum-product)
```

The aspiration is **certified coherence**: each structure is a set of laws, and the
places where they compose are candidates for a kernel obligation rather than an
untested interaction. This is realized to different degrees today (see the
[trust ledger](ARCHITECTURE.md#the-trust-ledger)): the **semiring/relational core and
the DBSP differential are kernel-proved (L0)**; the **measure (inference) and the
optic-composition layers are partly trusted / runtime-witnessed (L2)**. The structures
are not bolted on — they are the algebra the per-program proofs are written in, and the
shared core is what makes their composition tractable to certify.

## The core — sum-product over a semiring

A query is, abstractly, a **sum-product expression over a semiring**. `reduce`/`+` is
the sum; `map`/`*`/`join` is the product. This single framing is why so much is
expressible and optimizable uniformly:

- **Aggregation** (`group-by` + `reduce`) is a fold over a monoid; one
  `foldl`-invariant law gives count / sum / max / exists / distinct, each
  kernel-proved, *without* needing the monoid's own axioms.
- **FAQ factorization** — pushing an aggregation through a join so the product is
  never materialized — is a semiring law (`Map.foldl_join_factor`), so it works
  generically for sum/count/max, not per-operator. See [PLANNER.md](PLANNER.md).
- **Probabilistic inference** is the *same* sum-product read over a probability
  semiring: variable elimination is exactly the FAQ elimination order. See
  [INFERENCE.md](INFERENCE.md).

The owned algebra is `WSemiring` / `WAddMonoid` (a minimal fragment tailored to the
FAQ shape) plus an AC-normalizer grounded in Lean's real `Std.Associative` /
`Std.LawfulIdentity` instances — so reassociation cites genuine `Std` machinery, not
ad-hoc axioms.

## Structure 2 — differentiation (incremental view maintenance)

The ring/comonad structure is the **derivative** of a query: given the change to the
input, compute the change to the output, without recomputing. This is DBSP. Linear
operators (filter, sum) have a trivial increment; the join is bilinear (the certified
product rule). The `∂` pass lowers a batch plan to its incremental form and cites the
licensing law per stage. See [STREAMING.md](STREAMING.md) for the runtime story and
the linearity boundary.

## Structure 3 — lenses / optics (the backward direction)

Where the semiring runs a query *forward* (data → result), the optic structure runs
*backward* (result-edit → data-edit). The **first-projection product lens has its
round-trip laws kernel-proved** (`Lens.fst_PutGet` / `Lens.fst_GetPut`, both `Eq.refl`);
lens *composition* is provided as a runtime combinator with a runtime round-trip check,
not yet a kernel composition law. This is the direction a write-through view or a
bidirectional transform needs — the proven projection laws are the L0 anchor; general
compositional lawfulness is on the L2 side for now.

## Structure 4 — measure (probabilistic inference)

The measure structure reads the semiring carrier as *weights*. A `Rel A S` (relation
with semiring-valued provenance) is a monad — `return`/`bind` are unit and
sum-product — and its `FinDist` view is a finite distribution whose marginal agrees
with weighted model counting. Inference is therefore not a separate engine: it is the
core sum-product over a probability semiring, with the same FAQ elimination doing
variable elimination. WMC backends (enumeration, BDD) plug in behind a seam. See
[INFERENCE.md](INFERENCE.md).

## The bridge from data — the malli → type functor

You don't write kernel types; you write malli schemas, and a **total functor** turns
each schema into a refinement (dependent) type: `F(schema) = Subtype Value(γ)`. `:map`
becomes a record, `:or`/`:enum` close via Value-refinement, range constraints
(`[:int {:min 0}]`) become `Subtype` predicates that the planner *reads* — a
functional-dependency in the schema licenses the scope-quotient factorization, a key
constraint licenses the relational laws. This is the sense in which **the type drives
the plan**; see [DEPENDENT_TYPES.md](DEPENDENT_TYPES.md).

The schema can also be *inferred* from example data (range refinement → sound
selectivity), so the gradual path is: run untyped → infer a schema → the schema
sharpens the algorithm. See [GRADUAL.md](GRADUAL.md) and [the Tutorial](TUTORIAL.md).

## Why one core

Keeping all four structures over a single certified core is what lets them *compose* —
a differential-of-an-aggregation, a measure-over-a-join, a lens-into-a-group-by. Each
composition is a place a normal system would have an untested interaction; here the
shared core makes it a *candidate* for a kernel obligation. That obligation is
discharged today for the relational/differential core and is the design goal for the
measure/optic layers (see the [trust ledger](ARCHITECTURE.md#the-trust-ledger)). The
payoff is the slogan: *verification licenses the fast representation* — once the
algebra is proved, the runtime is free to be fast.

## See also

- [ARCHITECTURE.md](ARCHITECTURE.md) — how the core is built and where the trust boundary sits.
- [PLANNER.md](PLANNER.md) — the semiring laws as optimizer recognizers.
- [INFERENCE.md](INFERENCE.md) · [STREAMING.md](STREAMING.md) · [DEPENDENT_TYPES.md](DEPENDENT_TYPES.md).
