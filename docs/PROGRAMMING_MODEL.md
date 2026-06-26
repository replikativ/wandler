# The programming model — the formal core

Wandler lets you write an ordinary Clojure data pipeline, elaborates it to a term in
a dependently-typed kernel (the CIC kernel that also admits Lean 4 / Mathlib),
**optimizes** it by rewriting — keeping only rewrites that carry a machine-checked
proof `optimized ≡ naive` — and **lowers** it to fast Clojure. This document is the
*algebra* under that surface: how a malli schema becomes a kernel type, what those
types buy the planner, and the one structure (a sum-product over a semiring) that
unifies relational aggregation and probabilistic inference.

The reading discipline throughout is the **trust ledger** (see [ARCHITECTURE.md](ARCHITECTURE.md)):
a `> **✓ proven**` box marks something a kernel proof object guarantees; a
`> **⚠ trusted**` box marks a boundary wandler does *not* prove (a measured statistic,
a floating-point weight, a foreign engine). The exact carriers (counting `Nat`,
existence `Bool`) are proven; the probabilistic/measure weights are trusted. Keeping
the two visibly apart is the whole point.

The [Tutorial](TUTORIAL.md) walks the same ground from the outside (runnable REPL
output); this doc gives the formal account behind it.

## The malli → type functor

You never write kernel types directly. You write a malli schema and a mapping turns it
into a kernel type. The mapping lives in `wandler.surface.malli`, in two directions:

- **EXPORT** — `type-expr->malli` : a verified function's CIC type → a malli schema
  (for runtime contract checking and generative testing of the compiled runtime).
- **IMPORT** — `malli->type-expr` : a malli schema → a CIC type, with `:map` becoming a
  right-nested `Prod` record and refinements becoming `Subtype` predicates.

The import direction is the one that drives the planner. The scalar core is exact:
`:int → Int`, `:boolean → Bool`, `:string → String`, `:double → Float`, and crucially
`[:int {:min 0}] → Nat` and `[:map …]` → a record model (`malli-record` returns
`{:keys :index :field-types :rec-type}` — the column/type information a query planner
needs). Range constraints become dependent refinements:

```clojure
;; [:int {:min 18}]  ↦   Subtype Nat (fun v => 18 ≤ v)     (ksubtype-nat)
;; [:string {:min 1}] ↦  Subtype String (fun s => 1 ≤ s.length)
;; [:set X]          ↦   Subtype (List X) (fun l => List.Nodup X l)
```

This is the same `m/=>` you already see in the tutorial. The §3 `rev-by-region` schema —

```clojure
[:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]
           [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]]
 [:sequential :int]]
```

— compiles each `[:map …]` argument to a record type whose fields are `Nat` (from
`[:int {:min 0}]`), and the field keys/positions are what let the optimizer turn the
customers-⋈-orders join into a scatter (`:groupby-reduce-join`).

> **⚠ trusted (honesty note).** The functor is **not total**: a CIC type with no malli
> mapping exports to `:any` (with a warning, `*warn-unknown?*`), and a malli form with
> no kernel mapping (e.g. `[:re …]` regex refinements) throws on import. The covered
> subset — scalars, `:map`/`:tuple`/`:sequential`/`:maybe`/`:set`, and `:int`/`:string`
> range refinements — is what's proven-out today; everything else is a clean rejection,
> not a silent approximation. "Total functor" in earlier drafts was aspirational.

## Dependent types in practice — what a refinement buys

A `Subtype T P` is a value of `T` carrying a proof of `P`. The payoff is that the
optimizer can *read* that proof and delete work. The engine is `wandler.surface.refine/prove-const`:
given a filter predicate `p : T → Bool`, it decides whether `p` is **constantly true**
(`∀x:T, p x = true` — drop the filter) or **constantly false** (`∀x:T, p x = false` —
the pipeline is empty), and returns a *kernel proof term*, consumed once at optimization
time. It tries proof candidates cheapest-first:

1. **definitional** (`rfl-proof`) — `fun x => Eq.refl Bool b`, valid when `p x` reduces
   to `b` (e.g. `(>= x 0)` over `Nat`).
2. **refinement subtyping** (`subtype-property-proof`) — when the predicate reads a
   `Subtype.val`, its carried `.property` discharges `k ≤ v` directly via
   `Nat.ble_eq_true_of_le` (and `subtype-negation-proof` for the always-false case).
3. **omega** (`omega-proof`) — materialize the refinement as a hypothesis, bridge the
   `Bool` comparison to its `Prop`, and close with the `omega` decision procedure — the
   systematic F\*/Liquid-Haskell-style discharge.

Each candidate is admitted only if it survives strict `.check` (not the lenient
`inferType`), so the planner never "verifies" a filter elimination that the later
`a/defn` admission would reject. `prove-monotone` likewise proves that an update
function preserves a refinement (`∀w, P w → P (f w)`), which is what makes a
range-refined field safe to write through (`inc`/`+k` keep `18 ≤ age`).

> **✓ proven.** Filter elimination, distinct-removal over a `:set` (the `List.Nodup`
> refinement licenses `nodup_eraseDups`), and refinement-preserving writes are each
> backed by a kernel proof term over the value's `Subtype.property`. The type literally
> drives the plan: a constraint in the schema is a theorem the optimizer gets to use.

## The gradual ladder — formally

The tutorial's spine is "no types → inferred → explicit, same body, more guarantees."
Formally these are three ways the *same elaborated term* acquires a *typing context*,
and the typing context is what unlocks rewrites.

- **No types.** A plain Clojure `defn`. Wandler is not involved — no term, no proof, no
  plan. The body is just data flowing through `clojure.core`.

- **Inferred** (`wandler.infer/induce-types!`). Show a representative sample; malli's
  `mp/provide` recovers the *structure* and `field-profile` adds the *value-level*
  refinements `mp/provide` omits, split into two honest lanes:
  - the **guarded-sound lane** — unique-key / FD candidates. A collision-free field on a
    sample is only a *candidate* key (a high-cardinality non-key can look unique), so it
    flows to `wandler.adaptive`, which certifies the rewrite under the key *and* guards
    the key at the runtime boundary, deopting if violated. A wrong guess costs a missed
    optimization, never a wrong answer.
  - the **advisory-prior lane** — numeric ranges, ndv, small domains. These are
    one-sidedly-too-tight (a sample never exceeds the true domain), so they feed the cost
    model as *priors* (`cost-priors`), fused with measured evidence. A wrong prior costs
    speed, never correctness, because the kernel still certifies whatever plan is chosen.

  The enriched profile round-trips back into a malli schema (`refined-schema`) and is
  *registered* under the function name, so a subsequent `a/defn` with the same body in
  the same namespace picks up the kernel types with no new machinery.

- **Explicit** (`:-` binders or `m/=>`). The same elaboration, but now *you* state the
  refinements — and the point of writing them by hand is **control**: declaring
  `[:int {:min 0 :max k}]` ranges sharpens selectivity, which steers the physical
  strategy (pre-aggregated index, grace-hash spill, drive-direction reorder).

`wandler.gradual` is the front door over the planner that makes the ladder legible:
`gradient` runs the planner at increasing annotation tiers and reports what each tier
*unlocks*; `coach` empirically probes which annotation would unlock which rewrite. The
invariant across the whole ladder: **richer annotations change only the plan, never the
result** — every tier returns a kernel-certified `optimized ≡ original`.

> **✓ proven.** At every rung the adopted plan carries `:verified? true`. The ladder is
> a monotone increase in *optimization*, certified at each step; it never trades
> correctness for types.

## The semiring view — aggregation and inference are one sum-product

The unifying claim: a query is a **sum-product over a semiring** `S`. `reduce`/`+` is the
sum (`⊕`); `map`/`*`/`join` is the product (`⊗`). Swap `S` and the *same* operators
compute different things. `wandler.inference.semiring` makes this concrete with
`Rel A S := A → S` (a relation as a finite map element→weight) and operators
(`rel-add`, `rel-mul`, `rel-join`, `rel-sum`) generic over `S`:

| semiring | `⊕` / `⊗` | computes | carrier |
|---|---|---|---|
| `counting` | `+` / `*` | query cardinalities, Z-set weights | `Nat`/`Int` (exact) |
| `existence` | `∨` / `∧` | reachability, set membership | `Bool` (exact) |
| `tropical` | `min` / `+` | shortest paths | `Float` |
| `probability` | `+` / `*` | finite distributions (`FinDist`) | `ℝ≥0` (float) |
| `provenance` | `∪` / pairwise-`∪` | the Boolean formula for exact inference | DNF set-of-sets |

The FAQ engine (`faq`, `factor-join`, `factor-marginalize`, `elimination-order`) runs a
query as `⊕_{eliminated} ⊗_{factors}`, eliminating one variable at a time. The
**elimination order is the plan** — it determines cost, not the result, *for a
commutative semiring* — and this is the precise sense in which database query
optimization and probabilistic variable elimination are the same problem.

What is actually **proven in the kernel** here is the *algebra that licenses* that claim,
for the exact carriers:

- `Bool.absorptive` — `∨ a (∧ a b) = a` (proved by `Bool.casesOn`). This is the
  datalog° POPS recursion-safety certificate: an absorptive semiring converges under
  recursion. `fixpoint` is *gated* by it (`recursion-safe?`) — it refuses a
  non-absorptive semiring (counting: `1 + 1·1 = 2 ≠ 1`, so a recursive count diverges).
- `Semiring.bool_distrib` — `a ∧ (b ∨ c) = (a∧b) ∨ (a∧c)`, the FAQ factorization core.
- `Semiring.bool_or_comm` / `Semiring.bool_and_comm` — the elimination-order independence.

For **counting**, the optimizer's actual factorization plan is certified by
`Map.foldl_join_sum_factor` (the pre-aggregated FAQ index) and `Map.foldl_join_factor`
(push an aggregation through a join) — proved over `Nat`, and what `wandler.optimize.faq`
rides to lower a counting query to a verified physical plan. The aggregation monoids these
laws reassociate over are the owned `WAddMonoid` / `WSemiring` prelude structures, whose
linearity laws (`sum_map_split`, foldl-over-append, …) are proved in `wandler.core.monoid`
by structural induction and normalized by `ac_rfl` against genuine `Std.Associative` /
`Std.LawfulIdentity` instances (`wandler.laws.ac`).

> **✓ proven (exact carriers).** `Bool.absorptive`, `Semiring.bool_distrib`, the Bool
> commutativities, and the `Nat` factorization laws are kernel theorems (each cached and
> re-checked by `install!`). The counting/existence semirings are exact; the recursion
> gate is a *theorem*, not a documentation table (contrast the datahike/Scallop POPS
> matrix).

> **⚠ trusted (honesty note).** The generic `faq`/`fixpoint` *engine* in `semiring.clj`
> is plain Clojure — its soundness for `Bool` is *backed by* the proven laws above, but
> the engine code itself is not kernel-checked the way the optimizer's `Nat` factorization
> plan is. Treat the FAQ engine as a research surface for arbitrary semirings; the
> *certified* path is the relational optimizer for `Nat`/`Bool`.

## The measure structure — inference as the same sum-product

Read the semiring carrier as *weights* and the relational algebra becomes a monad
(`wandler.inference.dist`): `fin-return sr a = {a 1̄}` and
`fin-bind sr m f = ⊕_a m(a) ⊗ (f a)`. Two instances fall out by picking the semiring:
`FinSet` over `existence` (finite nondeterminism / the powerset monad) and `FinDist` over
`probability` (the distribution monad). `faq` is then exactly "do the `⊕`-combines in a
cost-chosen order" — variable elimination *is* marginalization. Inference is not a
separate engine; it is the core sum-product over a probability semiring.

Exact marginals need care: naive `(prob, +, ×)` double-counts shared variables. So the
implemented path is the datahike PROBLOG split — run the **provenance** semiring to a
Boolean formula (the certified algebraic part), then **weighted-model-count** the formula
(`wmc`) to get the marginal.

> **⚠ trusted.** WMC is `#P`-hard; the in-repo `wmc` is exact by enumerating
> `2^|facts|` assignments (production swaps in a knowledge-compilation backend —
> LogicNG/Ganak). It operates on floating-point probabilities. **Every probabilistic
> weight is L2 trusted.** What is L0 is the *symbolic* part — the provenance algebra and
> the semiring laws; the numbers that come out are a trusted evaluation. The continuous
> analogue (the Giry monad) is explicitly an oracle boundary, not a kernel object.

## The four structures — design vs. guarantee

It is tempting to present wandler as a verified monoidal category carrying four
algebraic structures with machine-checked coherence between them. That framing is the
**design direction**; here is the honest accounting of what each structure actually has:

1. **Semiring / ring** (aggregation, FAQ, joins). **Proven** for the exact carriers, as
   above — this is the load-bearing, certified structure.
2. **Differential / comonad** (incremental view maintenance, DBSP). The `∂` pass lowers
   a batch plan to its incremental form; per the streaming layer each stage cites a
   kernel law (linear filter, bilinear join product rule, sum homomorphism). This is the
   second structure with kernel proofs — see [STREAMING.md](STREAMING.md) for the laws
   and the linearity boundary (where incremental maintenance stops being exact).
3. **Lens / optic** (the backward direction). The first-projection product lens has its
   round-trip laws **proven** — `Lens.fst_PutGet` and `Lens.fst_GetPut`, both `Eq.refl`
   (`wandler.inference.lens`). But lens *composition* (`lens-comp`) is a runtime
   combinator with a runtime round-trip witness (`round-trips?`), **not** yet a kernel
   composition law. The projection laws are the L0 anchor; general compositional
   lawfulness is L2 / directional.
4. **Measure** (probabilistic inference). The symbolic part rides structure 1; the
   numeric part is trusted, as above.

> **⚠ trusted (honesty note).** "Four structures with machine-checked **coherence**" is
> aspirational. What is certified today is structure 1 (semiring/relational core) and
> structure 2 (the DBSP differential), plus the *projection* laws of structure 3. The
> *compositions between* structures — a differential-of-an-aggregation, a lens-into-a-
> group-by — are where a normal system would hide an untested interaction; keeping all
> structures over one CIC core makes each composition a *candidate* for a kernel
> obligation, but most of those obligations are design goals, not discharged theorems.
> Do not read this section as a guarantee of cross-structure coherence.

The one slogan that *is* fully earned: **verification licenses the fast representation.**
Once the algebra of a single structure is proved, the runtime is free to pick the fast
form — a one-pass fold, an unboxed array, a parallel fork-join, an incremental view —
because the kernel checked it computes the same function as the obvious code.

## Where to go next

- [TUTORIAL.md](TUTORIAL.md) — the gradual ladder from the outside, with runnable output.
- [ARCHITECTURE.md](ARCHITECTURE.md) — elaborate → optimize → lower, and where the trust
  boundary sits (the full trust ledger).
- [OPTIMIZER.md](OPTIMIZER.md) — the semiring/relational laws as optimizer recognizers
  (fusion, filter pushdown, join factorization, reorder).
- [STREAMING.md](STREAMING.md) — the differential `∂` structure and the linearity
  conditions for incremental maintenance.
- [JIT.md](JIT.md) — measure-then-replan: trusted statistics steering a certified plan.
- [INFERENCE.md](INFERENCE.md) — the semiring view made runnable: variable elimination as the
  certified factorization, the carriers, WMC, and the FinDist/Giry monad.
- [ENGINES.md](ENGINES.md) — datahike/stratum as trusted axioms, and a marginal computed across
  two databases by the same certified elimination.
- [REFERENCE.md](REFERENCE.md) — the verb vocabulary and the honest edge cases.
- [BENCHMARKS.md](BENCHMARKS.md) — what the verification actually buys, measured.
- [README](../README.md) — the 30-second version and the install layers.
