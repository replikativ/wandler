# Probabilistic inference & cross-engine queries

The thesis of this document: **database query optimization and exact probabilistic
inference are the same problem** — a sum-product over a semiring — and wandler's
relational optimizer, read at the right carrier, *is* an inference engine. Variable
elimination is the aggregation-through-join factorization; join order is elimination
order; the kernel proof that a factored plan equals the naive one is the
variable-elimination certificate.

Code: `wandler.inference.{semiring,dist,wmc,giry}`. Tests: `inference_test`,
`dist_test`, `dist_laws_test`, `wmc_test`, `cross_engine_inference_test`.

---

## 1 — One carrier, many readings

A *semiring* `(S, ⊕, ⊗, 0̄, 1̄)` is all the optimizer needs: `⊗` combines along a path
(a join), `⊕` aggregates alternatives (a fold/marginal). Swap the carrier and the
*same* plan computes a different quantity (`wandler.inference.semiring`):

| semiring        | `⊕`     | `⊗`   | a query computes…                |
|-----------------|---------|-------|----------------------------------|
| `counting`      | `+`     | `·`   | number of satisfying rows / paths |
| `existence`     | `∨`     | `∧`   | reachability / boolean satisfiability |
| `probability`   | `+`     | `·`   | a marginal probability            |
| `tropical`      | `min`   | `+`   | shortest path / Viterbi (MAP)     |
| `min-max-prob`  | `max`   | `min` | bottleneck / fuzzy                |
| `provenance`    | `∨`     | `∧`   | the boolean lineage formula (→ WMC) |

The carrier's algebraic laws (`Semiring` in the kernel) are what make a rewrite sound,
so they are kernel-checked once and reused for every reading.

---

## 2 — Factors, FAQ, and variable elimination (the runtime engine)

A **factor** `{:vars #{…} :rel {assignment → weight}}` is a semiring-annotated relation
over named variables. A query is `⊕_{eliminated} ⊗_{factors} fᵢ`. Variable elimination
`⊗`-joins the factors that mention a variable and `⊕`-marginalizes it out, one variable
at a time (`wandler.inference.semiring`):

```clojure
(factor [:a :b] {{:a 0 :b 0} 0.3, {:a 0 :b 1} 0.7, …})   ; a semiring-annotated relation
(factor-join sr f1 f2)            ; ⊗ — merge on shared vars, multiply weights
(factor-marginalize sr :v f)      ; ⊕ — sum a variable out
(elimination-order keep factors)  ; a min-degree PLAN (least-mentioned var first)
(faq sr keep factors)             ; run the whole query, plan once, any semiring
```

`faq` plans once and runs over **any** semiring — counting (path counts), tropical
(shortest path), existence (reachability), probability (marginals) — by swapping `sr`.
The elimination **order** is the plan: it determines cost, not the result (for a
commutative semiring, by `⊕`/`⊗` commutativity and `⊗` distributing over `⊕`). This is
the exact point where join-order optimization and inference coincide:

> **join order = elimination order.**

---

## 3 — The monad reading: FinSet and FinDist

`wandler.inference.dist` reads the same `Rel A S` as a **monad** — a branching
computation is a finite weighted map `outcome → weight`, and `return`/`bind` are the
semiring's unit / sum-product:

```
fin-return sr a   = {a 1̄}                 -- Dirac point
fin-bind  sr m f  = ⊕_a  m(a) ⊗ (f a)      -- run each branch, ⊗-scale, ⊕-combine
```

Pick the semiring to pick the monad:

- **FinSet** = `existence` — finite nondeterminism / the powerset monad
  (`singleton`/`fset-bind`/`to-set`). Demo: graph reachability by binding the step
  relation.
- **FinDist** = `probability` — the finite distribution monad
  (`bernoulli`/`uniform`/`dist-return`/`dist-bind`/`expectation`/`prob`/`normalize`).
  Demo (`dist_test`): four Bernoulli edges + boolean reachability give
  `P(1→9) = 0.776`, which **agrees with the provenance → WMC route** — the same answer
  by two paths, monad ≡ sum-product, cross-validated.

The monad needs only `⊗` (a monoid, to scale a path); the *query* (marginal /
expectation) needs `⊕` — and `faq` is exactly "do the `⊕`-combines in a cost-chosen
order", i.e. variable elimination.

---

## 4 — Two elimination engines, two trust levels

Variable elimination exists here at **two levels**, and it is important to be precise
about which is which — `wandler.inference.semiring/faq-certificate` names the kernel
theorems behind each carrier and tags it `:algebra` or `:execution`:

- **`:algebra` — the runtime `faq` engine** (§2, value-level over `{assignment→weight}`
  maps). It is *multi-factor and multi-variable*, with an `elimination-order` planner, and
  it is **sound because the `Semiring` laws are proven** — `Semiring.bool_distrib` (⊗
  distributes over ⊕) and `⊕`/`⊗` commutativity make order affect cost, not result. But
  the *execution* is ordinary Clojure: it is trusted to apply the proven algebra
  correctly; it does not emit a per-run kernel certificate. This is the engine the WMC /
  dist / `semiring_test` stack runs on.
- **`:execution` — the optimizer's factorization plan** (`wandler.optimize.faq`). When a
  query is a kernel term, `opt/optimize-cost` rewrites a single aggregating-join
  elimination and **re-checks `factored ≡ naive` with `check-constant` per program**
  (`Map.foldl_join_factor` / the pre-aggregated `Map.foldl_join_sum_factor`). This is a
  genuine per-run certificate, but currently for *one* elimination step at a time, over
  `Nat`/`Bool` carriers.

The cross-engine capstone (§5) and `inference_test` ride the **`:execution`** path — they
do **not** call `semiring/faq`. The bridge between the two is `wandler.inference.certify`:
`certified-eliminate` is a drop-in for `(factor-marginalize sr v (factor-join sr f1 f2))` that
compiles the join-and-marginalize into a kernel term, certifies it with `optimize-cost`
(`Map.foldl_join_factor`), runs it, and decodes the result back into a `{:vars :rel}` factor —
so a single elimination step of the `:algebra` engine becomes per-run `:execution`-certified, with
the result proven equal to `semiring/faq`'s (`inference_certify_test`).

`certify/chain-certificate` composes a multi-step elimination into **one** `check-constant`-verified
theorem `∀ sources, whole-naive ≡ whole-factored`, threading each step's output factor into the next
*purely as a kernel term* (`Map.entries`) — no trusted runtime hand-off. The composition is `Eq.trans`
of `congrArg (next step's naive fn) (congrArg Map.entries prev-proof)` with the previous factored term
substituted in, so the whole elimination chain carries a single end-to-end kernel certificate. A factor
is described by a *layout* (`:row-type` + a per-variable projection), and an elimination produces the
output factor's layout, so a multi-variable (composite-key) intermediate threads into the next step like
any base factor — chains with composite intermediates compose to one admitted theorem
(`inference_certify_test`).

`certify/certify-faq` is the engine front-end: ingest a factor graph (`{:vars :rel}` factors), derive the
min-degree elimination order (`semiring/elimination-order`, override with `:order`), build and compose the
steps via `certify-graph`'s **live-factor fold**, run the composed factored plan by codegen, and return the
result factor — a certified drop-in for `(semiring/faq carrier keep order factors)` whose result equals
`faq`'s value-for-value and is backed by one `check-constant`-verified whole-graph theorem
(`certify-faq-chain-matches-semiring-faq`). It is **carrier-parametric** — `counting` (`Nat`), `existence`
(`Bool`, ∨/∧ reachability), `tropical` (`ENat` = ℕ∞, min/+ shortest path), and `probability` (`Float`, +/×
unnormalized marginals), each cross-validated against `semiring/faq` — because the factorization law
`Map.foldl_join_factor` is monomorphic at `Sort 1` and so op- and carrier-agnostic; the weight codec
(`:enc`/`:dec`/`:zero-val`) is the only carrier-specific piece. The `Float` carrier is sound **even though
Float is not a lawful semiring**: `Map.foldl_join_factor` is *order-preserving* (the join is a `flatMap`;
the factored fold visits the same elements in the same order), so `factored ≡ naive` holds because the two
folds are bit-identical, not by any commutativity/associativity reorder. (Reorder-based plans — join
reorder, the pre-aggregated index — do still need a lawful carrier, so they stay `Nat`/`Bool`/`ENat`.)
Normalizing a Float marginal to a probability is the trusted L2 division, as for counts.

The live-factor fold generalizes the linear chain to any **chain / tree / forest / star** graph: each live
factor carries a provider triple `{:nv :fv :proof}` (a naive-provider term, a factored-provider term, and a
proof `nv ≡ fv`), each elimination is certified in isolation over fresh fvars — arity 1 (`marginalize-one`,
no join, refl), arity 2, or arity ≥3 (a left-nested multi-way `Map.join` chain, every join factored
join-by-join by `try-fold-factor*`) — and the results compose by substituting providers under congruence
(`combine`), so a variable shared by 3+ factors composes to one admitted theorem just like a chain
(`certify-faq-star-arity3-multiway` — the result is the full cross product of the survivors). A **loop** —
eliminating a variable whose factors *also* share another variable — is handled by a **natural join** on the
composite key (the shared variable is equated, not cross-producted); since `Map.foldl_join_factor` is
key-agnostic, the composite-key join still factors join-by-join (`certify-faq-loop-natural-join`,
`certify-faq-four-cycle`). So `certify-faq` is a complete certified variable-elimination engine for any
**connected** discrete factor graph; a disconnected graph (a final cross-product join) is the one shape it
leaves out, and treewidth is a *cost* limit (a loopy elimination is correct but its intermediate factor can
be large), not a correctness one.

Two more pieces are genuinely kernel-proven regardless of path: the monad **left-unit law**
`bind (return a) f = f a` for the weighted-list carrier
(`dist_laws_test/wlist-unit-laws-are-proven`), and the `Semiring` laws themselves
(`semiring/install!`).

**The numbers are a trusted L2 seam.** Concrete real-valued probabilities are evaluated at
runtime; normalizing counts to a probability is a division. Two backends supply them:

- **WMC** (`wandler.inference.wmc`) — weighted model counting over the provenance formula,
  pluggable: `wmc-enumerate` always present, plus a **LogicNG BDD** backend under the
  `:logicng` alias. A correlated query (`correlated_query_test`) shows why it matters:
  naive independence gives the wrong marginal where WMC is exact.
- **Giry** (`wandler.inference.giry`) — the continuous measure monad as a sampler-based
  `expectation` (the one piece that leaves Init-only). `of-findist` lifts a discrete
  FinDist into Giry and the expectations agree.

So the discrete *structure* is proven (single-step per-run, or whole-query at the algebra
level), the numeric evaluation is a trusted oracle, and the **coherence** between readings
— semiring ↔ measure via WMC, FinDist ↔ Giry via `of-findist` — is checked where they
overlap.

---

## 5 — The cross-engine capstone (Tutorial Rung 7)

`cross_engine_inference_test` puts it together: a factor graph
`Region — Channel — HighValue` whose two factors live in **different engines** —
`φ₁(Channel, Region)` in a datahike `:memory` database, `φ₂(Channel, HighValue)` in a
stratum columnar dataset — and the marginal query `P(HighValue)`.

The factors share `Channel`, so eliminating it is a `Σ` over a **join on Channel**,
which factorizes — the optimizer fires `:fold-factor`, certifies `factored ≡ naive`, and
the result term contains no `Map.join`: the `Region × Channel × HighValue` joint is never
built. The certificate is **engine-agnostic at the source boundary**, so the same proof
covers factors drawn from two databases; each source then lowers to *its* engine's read.

```bash
clj -M:datahike:stratum:test -n wandler.cross-engine-inference-test
#   P(HighValue=yes) = 0.5938   — certified VE, cross-validated == brute-force joint
```

Counts keep the proof at `Nat` (the structure is what's certified); normalizing to a
probability is the trusted numeric step. Because neither engine can join across the
other's boundary, the naive answer must materialize the joint in app memory — which the
factored plan never does, so the speedup *widens* as the data grows (the timed
`cross-engine-ve-scales` deftest; the larger `cross_engine_capstone` reaches 4×→16×).

---

## 6 — Where this sits

This is **Structure 4 (measure)** of the four-structure programming model
([`PROGRAMMING_MODEL.md`](PROGRAMMING_MODEL.md) §14), grounded in the FAQ factorization
([`PROGRAMMING_MODEL.md`](PROGRAMMING_MODEL.md) §3) and the engine bridges
([`PROGRAMMING_MODEL.md`](PROGRAMMING_MODEL.md) §7). The headline is not any single
number but the identity itself: **one verified sum-product core, read as query
optimization and as exact inference, over data wherever it lives.**

`certify-faq` is now a complete certified variable-elimination engine for any **connected**
discrete factor graph — chain / tree / forest / star / **loop** (the last via a natural join
on the composite key), keeping a *factor* per step, over the counting / existence / tropical /
probability(`Float`) carriers, min-degree ordered — each one kernel-certified whole-graph
theorem `∀ sources, whole-naive ≡ whole-factored`. Open edges: a **disconnected** graph (a
final cross-product join), **treewidth** as a *cost* limit (a loopy elimination is correct but
its intermediate factor can be large — not a correctness gap), and a *lawful*-carrier-only
reorder layer (join reorder / pre-aggregated index need commutativity, so they stay
`Nat`/`Bool`/`ENat`, not `Float`).
