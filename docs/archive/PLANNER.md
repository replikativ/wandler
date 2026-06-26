# The planner — certified rewriting

The optimizer and the physical planner are the *same engine* working in two cost
dimensions. Both propose a rewrite; both certify it with the kernel before adopting
it. The difference is only what the cost model rewards.

## Rewriting as the optimization primitive

A wandler program is a kernel term. To optimize is to rewrite the term into a
cheaper equivalent and *prove the equivalence*. The driver, for each candidate
rewrite `term → term'`:

1. builds the proof term `term' ≡ term` (by instantiating a proven law, or composing
   several via `Eq.trans`/congruence);
2. runs `cert/verified-rewrite?` — the kernel's strict `check-constant` on that proof;
3. adopts `term'` **only if** the proof checks *and* the cost model says it is cheaper.

`(w/explain 'f)` returns the result: `{:verified? :changed? :rewrites :stages-before
:stages-after :cost}`. `(w/plan-str 'f)` renders the before/after pass list and the
laws used. A program always either improves-and-certifies or is left exactly as
written — there is no uncertified middle state.

## The recognizer set

Recognizers are pattern-matchers that spot an optimizable shape, instantiate the
relevant proven law, and gate on cost + certificate. The ones wired into the default
driver:

| Recognizer | Shape → rewrite | Law(s) |
|------------|-----------------|--------|
| **Deforestation / fusion** | `map g (map f xs)` → `map (g∘f) xs`; `filter∘filter`; `foldl∘map` → one fused fold | `List.map_map`, `filter_filter`, `foldl_map` (all `Init`) |
| **filterMap fusion** | `map f (filter p xs)` → one `filterMap` pass | `List.map_filter_filterMap` |
| **Filter→join pushdown** | `filter (p∘fst) (join …)` → `join (filter p xs) …` | `Map.filter_join_pushdown` |
| **Aggregation-through-join (FAQ)** | `Σ over (h ∘ join xs ys)` → factor so the `|xs|·|ys|` product is never built — O(N²) → O(N) | `Map.foldl_join_factor` (semiring-generic: count/sum/max) |
| **Group-by-over-join** | `map (reduce⊕0 ∘ map h) (vals (group-by key (join …)))` → a **scatter** (reduce-by-key) that never materializes the join | `Map.groupby_reduce_join_factor` |
| **Semijoin** | nested-loop `filter (elem …)` → hash-index probe | `lookup_group_by` |
| **Join reorder** | index the smaller side (cost-driven) | `Map.join_length_comm` (the count instance of the aggregate Fubini — `Perm`-free) |
| **CSE / let-sharing** | hoist a duplicated subterm into a `let` | a `zeta` defeq — the certificate is `Eq.refl` |

New laws and recognizers register without touching the core; a recognizer returns a
`{:term :proof :rw …}` map and the driver does the certification.

### Worked example — group-by-over-join

```clojure
;; the malli signature gives custs/orders their record types (without it the
;; element types are unconstrained and elaboration leaves unsolved metavariables)
(m/=> revByRegion
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]
             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]]
       [:sequential :int]])
(a/defn revByRegion [custs orders]
  (map  (fn [g] (reduce + 0 (map (fn [[c o]] (:amount o)) g)))
        (vals (group-by (fn [[c o]] (:region c))
                        (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders)))))
```

```
plan revByRegion
  naive:  map → foldl → map → map → group_by → join   (6 passes)
  fused:  map → foldl → foldl → group_by              (4 passes)
  laws:   :groupby-reduce-join, :hoist-index
  proof:  optimized ≡ naive (kernel-certified)
```

The `Map.join` node is gone: the optimizer recognized "per-group sum over a join"
and rewrote it to a scatter — the `|custs|·|orders|` product is *never built* — then
the result is differential-tested to match the brute-force per-region revenue. The
factorization is commutativity-free (the scatter prepends into buckets in the same
order `group-by` does, so the per-key equation closes definitionally).

## The cost model

Cost is computed over the term tree (`wandler.optimize.cost`) — binder- and
let-aware, descriptor-driven (an op-cost table is the per-engine seam). Cardinality
flows datahike-style: a static propagation seeded by the input sizes and a
**pluggable selectivity** (`:selectivity`) — which can be a constant, a measured
profile, or a JIT-fed estimate. A load-bearing invariant: the per-element step
lambdas of a SOAC are *not* counted, so a factorization that removes a product
genuinely reads as cheaper.

The cost model is what makes a *neutral* rewrite (same number of passes) get adopted
only when it actually pays — filter→join pushdown, for instance, is SOAC-neutral and
only wins under a selectivity that shrinks the join input.

## Physical planning — the chunked-array model

Below the logical plan sits a physical seam: the same certified term can be executed
by different backends over a uniform representation — **a transducer over unboxed
column-array chunks**. The monoid certificate that licenses the parallel fold is the
same one that licenses chunkability. Concrete physical choices the planner makes,
each certified:

- **Pre-aggregated index** (separable SUM): build an O(distinct-keys) index once
  instead of scanning the product — gated on `ndv` (number of distinct values).
- **Grace-hash / spill**: a certified external-join fallback when an in-memory build
  would exceed a memory budget.
- **Drive-direction / reorder**: index the smaller relation (DP join order over the
  cost model).
- **Backends**: the chunk kernel is pluggable — `raster` (numeric, zero-alloc columns),
  `stratum`, `spindel` — under the same plan lens.

See [BENCHMARKS.md](BENCHMARKS.md) for measured numbers — FAQ factorization is
provably O(N²)→O(N), and the loop-invariant-hoist shape measured 592–4106× on the
tested inputs.

**External engines are trusted oracles.** When a plan lifts onto datahike / stratum,
that engine's planner is *not* re-verified by the kernel — its API is admitted as a
set of typed axioms (`register-foreign!`), and `references-axiom?` flags any term that
leans on one. So a cross-engine query is certified *up to* the foreign engine's spec:
the algebraic glue is kernel-proven, the external oracle is part of the TCB. See the
[trust ledger](ARCHITECTURE.md#the-trust-ledger).

## Search beyond greedy

The greedy certify-as-you-go driver is the default. An **e-graph** layer
(`wandler.optimize.egraph`, `:use-egraph?`) does equality-saturation: it grows a
congruence closure of equivalent terms and extracts the min-cost one, then certifies
the chosen path. The e-matcher works under binders (for the semijoin laws). This is
the road to non-local reorderings the greedy driver can't reach.

## See also

- [PROGRAMMING_MODEL.md](PROGRAMMING_MODEL.md) — the algebra the laws are stated in.
- [DEPENDENT_TYPES.md](DEPENDENT_TYPES.md) — how the *type* sharpens the plan (carrier
  choice, FD scope quotient, relational-law licensing).
- [INFERENCE.md](INFERENCE.md) — FAQ variable elimination as the same sum-product engine.
