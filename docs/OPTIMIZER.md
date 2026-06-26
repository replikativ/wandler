# The certified optimizer

You write an ordinary Clojure pipeline in `a/defn`. Wandler elaborates it to an ansatz CIC
kernel term, **optimizes** that term by rewriting it, and lowers the result to fast Clojure. The
twist is the middle step: every rewrite the optimizer keeps carries a kernel proof
`optimized ≡ original`, re-checked by the same kernel that admits Mathlib. The optimizer itself is
**untrusted** — it searches, proposes, and may be wrong; the kernel is the only thing that decides
whether a proposal ships. This is translation validation, in Lean's `@[csimp]` discipline.

This document is how a written pipeline becomes a faster, still-correct one. The entry point is
`wandler.optimize.optimize-body` (called from the `a/defn` hook in `wandler.core/optimize-hook`);
the soundness gate is `wandler.optimize.certify/verified-rewrite?`.

## Term-as-IR, simp-as-certifier

There is no separate IR. The elaborated kernel term **is** the plan, and the rewriter is ansatz's
ported `simp`. A rewrite step has two halves:

1. **Propose.** `certify/optimize-term` runs `simp` over the term with an oriented lemma set,
   returning `{:term result :proof p :changed?}` where `p` is a kernel term of type
   `original = result` (nil when nothing fired, i.e. `rfl`).
2. **Certify.** `certify/verified-rewrite?` independently builds the goal `@Eq T original result`,
   closes it over the local context (`close-over-lctx`), and runs the kernel's **strict**
   `TypeChecker.check` on the proof — re-checking every application argument, the same strictness
   that admits a Mathlib declaration — then confirms `.isDefEq` of the proof's type and the goal.

`certify/optimize` wires these together: if the proof does not strict-verify, the change is
**rejected** and the original term returned unchanged. So the optimizer can never emit an
unverified plan — a partial `simp` normalization whose congruence proof fails the strict `.check`
is dropped, not shipped.

> **✓ proven (L0).** `verified-rewrite?` uses `TypeChecker.check` (not the lenient `inferType`),
> closes over `lctx`, and confirms the proof proves exactly `original = result`. A `nil` proof is
> accepted only when `original` and `result` are identical.

> **⚠ trusted (L2).** Nothing in this layer. The recognizers, the cost model, and the e-graph are
> all untrusted search — a bug in any of them can only produce a *missed* optimization or a
> *rejected* proposal, never a wrong-but-accepted one.

Multi-step rewrites compose by `Eq.trans` (`faq/compose-trans`, with `nil` proofs as identities):
`orig ≡ fused ≡ factored` is one certified step. Every composite proof is re-checked as a whole.

## Fusion

The base optimization is confluent SOAC deforestation — collapsing a `map`/`filter`/`fold`
pipeline into a single pass. `certify/fusion-lemmas` is the oriented Init lemma set, each LHS→RHS
strictly removing one intermediate list:

```
List.map_map         map g (map f l)        → map (g∘f) l
List.filter_filter   filter p (filter q l)  → filter (q && p) l
List.foldl_map       foldl f i (map g l)    → foldl (f∘g-step) i l
List.foldl_filter    foldl f i (filter p l) → foldl (if p then f else id) i l
List.map_id          map id l               → l
List.map_flatMap / flatMap_map / filter_flatMap / foldl_flatMap / foldr_flatMap
List.map_filterMap / filterMap_map / filterMap_filterMap / filterMap_flatMap
```

Because each rule removes a list, the set is confluent — `simp` drives it to a normal form. The
`map f (filter p l) → filterMap …` law (`install-filtermap-fusion-law!`, an Init-only proof from
`filterMap_eq_map` + `filterMap_filter`) is added per-body so `map∘filter` fuses to one pass too.

This is what makes `big-squares` collapse:

```clojure
(a/defn big-squares [xs :- (List Nat)] Nat
  (reduce + 0 (map (fn [x] (* x x)) (filter (fn [x] (< 10 x)) xs))))

(:stages-after (w/explain 'big-squares))  ;;=> [foldl]   ; three passes → one
```

Named helpers fuse across their boundaries too: `certify/with-unfold-lemmas` synthesizes a
definitional `<helper>.eq_unfold` rule (proof `Eq.refl`) for each user `a/defn` applied in the
body, so a pipeline split across `step1`/`enrich`/… fuses as if written inline. The unfold lemmas
are definitional and the result is re-verified, so they cannot affect soundness; `optimize-body`
keeps an inlining rewrite only if the honest `soac-cost` (counted through the inlined body, via
`cost/soac-cost-deep`) strictly dropped.

## The FAQ factorization family

Fusion removes intermediate *lists*; it cannot remove a *join*. The headline optimizations do —
they instantiate proven laws that rewrite an aggregate-over-a-join into a per-key scatter that
**never materializes the |L|·|R| product**. This is the FAQ (Functional Aggregate Query) win:
O(N²) → O(N), and because the rewrite carries a proof, the asymptotic improvement is itself
certified equal to the brute-force semantics.

Each recognizer in `wandler.optimize.faq` matches a structural shape, instantiates a law by name,
reads the law's RHS as the optimized term, and gates adoption on `verified-rewrite?` **and** a
strict `pipeline-cost` drop. The recognizers and the proven laws (in `wandler.laws.faq` /
`wandler.laws.groupby_join`) they apply:

| Recognizer | Proven law | What it does |
|---|---|---|
| `try-groupby-reduce-join` | `Map.groupby_reduce_join_factor` | per-group SUM over a join → scatter (the join is eliminated) |
| `try-fold-factor` / `try-fold-factor*` | `Map.foldl_join_factor` | any `foldl` over `Map.join` → per-key nested fold; `*` iterates to a fixpoint (multi-way joins) |
| `try-count-factor` | `Map.count_join_factor` | `length` over a join → sum of per-key bucket lengths |
| `try-join-reorder` | `Map.join_length_comm` | swap which side is indexed (the Perm→Eq bridge for count queries) |
| `try-pre-agg-index` | `Map.foldl_join_sum_factor_generic` | separable SUM `Σ g(y)` → probe a pre-summed index (held O(distinct keys)) |
| `try-frame-index` | `Map.foldl_join_frame_generic` | separable two-sided weight `f(x)·g(y)` → frame rule (`f≡1` is `pre-agg`) |
| `try-frame-index-cond` | `Nat.cond_and_mul_split_generic` + frame | a separable guard `P(x)∧Q(y)` splits per side, then the frame |
| `try-frame-index-keyfactor` | `Map.foldl_keyfactor_float_generic` + frame | a key-factor `w(kf x)·g(y)` floats into the per-key index (FD-scope quotient) |
| `try-grace-hash` | `List.flatten_chunk` + `Map.foldl_join_blockfold` | spill: process the build side in budget-sized `List.chunk` blocks |
| `try-hoist-invariant` | `List.sum_map_mul_const` / `_const_mul` | 1-variable elimination: pull an x-free factor out of a sum |
| `try-sum-product-factor` | factor-pull simp set + e-graph fallback | `Σx Σy (h x·k y)` → `(Σx)(Σy)`, no join, O(n·m)→O(n+m) |

Filter/distinct elimination (`wandler.optimize.filter_elim`) folds into the same cascade:
`try-filter-elim` drops a filter the element type proves redundant, `try-distinct-elim` /
`try-keyed-distinct-elim` / `try-groupby-elim` drop `eraseDups`/group-by over a `Nodup`-refined
(declared `:set` / unique-key) relation — each sound only given the declared refinement, and each
gated by `verified-rewrite?`. The semijoin and filter-pushdown laws
(`List.elem_filter_eq_index_probe`, `List.elem_not_filter_eq_index_probe`,
`Map.filter_join_pushdown`) live in the `cost/cost-rewrites` reorder pool.

The laws are themselves theorems re-proven thinly through the `a/deftheorem` tactic surface
(induction + `simp` + controlled `rw`) and `check-constant`-verified as they are admitted (see
`wandler.laws.faq/install!`, cached per-process). The keystone `Map.foldl_join_factor` exposes the
join via `rw [Map.join_eq]` then `simp [List.foldl_flatMap List.foldl_map]`; the frame family
chains `factor → foldl_congr → foldl_add_init → const_mul_pull → bucket_sum_preagg`.

This is `rev-by-region` — the join stage **disappears**:

```clojure
(println (w/plan-str 'rev-by-region))
;;=> plan rev-by-region
;;     naive:  map → foldl → map → map → group_by → join   (6 passes)
;;     fused:  map → foldl → foldl → group_by              (4 passes)
;;     laws:   :groupby-reduce-join, :hoist-index
;;     proof:  optimized ≡ naive (kernel-certified)
```

And `spend3` — a three-way join where **both** joins are eliminated by iterating the same law:

```clojure
(w/explain 'spend3)
;;=> {:verified? true, :rewrites [:fold-factor :hoist-index],
;;    :stages-before [foldl map join join],
;;    :stages-after  [foldl foldl foldl group_by group_by], ...}
```

Note the *pass count rises* while the *cost drops* — eliminating the quadratic join is the win,
not the op count. That distinction is exactly what the cost model exists to see.

## The cost model + physical strategy

`soac-cost` (a flat SOAC op count) drives confluent fusion: fewer passes is cheaper. But it cannot
tell a `filter` that runs *before* a join (small input) from one *after* it (large input) — both
are one op. So the FAQ and reorder decisions gate on a cardinality model,
`cost/pipeline-resources`, which propagates `{:size :time :memory}` through the pipeline
(datahike's `estimate.cljc`, made static):

- **`:time`** — elements processed. `filter` shrinks by selectivity; `flatMap`/`join` expand;
  `foldl`/`length` collapse to a scalar. `pipeline-cost` is this projection — the adopt gate.
- **`:memory`** — peak working set. Streaming ops add nothing; `Map.join` carries its build-side
  index O(|build|); sort/group carry their buffer. This is the dimension the **physical strategy**
  gates on.

The per-op transforms live in an open registry (`op-cost-registry`, extend via
`register-op-cost!`) so an engine can declare how its operation moves cardinality. `Map.join`'s
output uses the textbook equi-join estimate `|L|·|R|/ndv` when distinct-key count is known, else a
`min(|L|,|R|)·fanout` default; the indexed (build) side pays `join-build-weight` (2.0) per element,
so indexing the *smaller* side is cheaper — which is exactly the certifiable `try-join-reorder`.

The driver `faq/optimize-cost-driver` chooses the physical plan after a FAQ law fires:

- **In-memory hash** (`:in-memory-hash`) — `hoist-invariant-indices` lifts the loop-invariant
  `Map.group_by` index build out of the row loop into a β-redex above the fold, so it is built once,
  not per row (O(N), not O(N²)). β-equivalence means the existing certificate still holds.
- **Pre-aggregated index** (`:pre-agg-index`) — when an `:ndv` oracle reports distinct-keys ≪
  |build|, hold each bucket pre-summed (DuckDB `PerfectHashAggregate`-style gating).
- **Nested-loop** (`:nested-loop`) — when the held index exceeds an explicit `memory-budget`,
  `Map.bucket_content` turns it into a per-row filter (O(bucket) memory, no held index), composed
  with the factorization proof.
- **Grace-hash** (`:grace-hash`) — spill the build side into budget-sized blocks; correctness is
  independent of block size, only the peak-memory guarantee depends on it.

Among the index/spill candidates the default is a fixed precedence ladder; `*cost-arbitrate*`
swaps it for a min-`plan-score` choice (cardinality `:time` + an over-budget memory penalty), with
divergences logged to `plan-arbitration-log` for measurement. Either way the choice is
kernel-certified.

> **⚠ trusted (L2).** Selectivity and cardinality are *inputs*, not facts. The static defaults
> (`{:eq 0.1 :range 0.33 :neq 0.9}` by comparator head, sharpened to an exact domain rate when the
> element type carries a `Subtype Nat` range via `cost/refinement-selectivity`) are heuristics; a
> measured profile (`:selectivity`, `:sizes`, `:ndv`) overrides them. A wrong estimate can pick a
> *slower* plan — it can never pick a *wrong* one, because the plan still carries its proof. The
> measure→replan loop that supplies real numbers is the JIT (forward-ref **JIT.md**).

## The e-graph search

The greedy driver commits to one cost-rewrite at a time, each of which must lower cost *in
isolation* — so it misses combinations where a rewrite is individually cost-neutral but jointly
enables a cheaper plan. `wandler.optimize.egraph/saturate-and-extract` is the search layer that
finds those: equality saturation over the **non-confluent** law set (`default-laws` = the
loop-invariant `hoist-laws` + the relational `reorder-laws`), reusing ansatz `grind`'s e-graph
(`grind.egraph` / `grind.ematch` / `grind.proof`) directly.

Each round runs two moves, composed by `Eq.trans`: (1) an e-graph cost pass iterated to its own
fixpoint — internalize with under-binder descent, E-match all laws, recursively extract the
cheapest equivalent term; (2) a `simp` fuse/normalize. Extraction ranks by a lexicographic
`ecost` (`soac-depth-cost` ≫ `soac-invariant-cost` ≫ `pipeline-cost`) so it prefers hoisting an
inner fold out of a step-λ — the per-element-recompute win the flat `pipeline-cost` deliberately
cannot see (it does not descend step-λs, to keep the factorization gates intact).

It is wired but **off by default** (`*use-egraph*` / `:use-egraph?`) — saturation is heavier than
the greedy driver. Today its load-bearing use is the `try-sum-product-factor` fallback for the
η-collapsed `Σx Σy (x·y)` identity shape, where the `simp` pull cannot fire; it runs on the
`Nat.zero`-normalized term (the syntactic e-matcher needs the spelling `simp`'s `isDefEq` did not)
and the resulting proof is re-verified against the original.

> **✓ proven (L0).** Soundness is unchanged: the e-graph is an untrusted oracle that only decides
> *which* term to keep. Extraction is restricted to materialized in-class members, so grind's
> `mk-eq-proof` always exists, and every round is re-checked by `verified-rewrite?`.

## `explain` / `plan-str` — the user-facing window

The optimizer records its report per fn (`wandler.core/reports`); two readers expose it:

- `(w/explain 'fn)` — `:verified?`, `:changed?`, `:rewrites` (the laws that fired), and the SOAC
  `:stages-before` / `:stages-after` + `:passes-before` / `:passes-after`.
- `(w/plan-str 'fn samples)` — a datahike-explain-style render (naive vs fused stages, the laws,
  the certificate line), optionally profiling cardinality/selectivity/runtime over `samples`.

`optimize/explain` additionally narrates the physical strategy chosen and the memory reasoning.
The honest reading of any report: `:verified? true` is an L0 fact a machine checked
(`optimized ≡ naive`); the pass counts and the strategy choice are the untrusted search's account
of *why*.

## Where to go next

- **TUTORIAL.md** — the validated `big-squares` / `rev-by-region` / `spend3` walk-throughs whose
  real outputs are quoted above.
- **ARCHITECTURE.md** — the full engine: elaborate → optimize → lower, and where this layer sits.
- **REFERENCE.md** — the verb vocabulary the surface elaborates into the terms this optimizes.
- **PROGRAMMING_MODEL.md** — the four algebraic structures (semiring / ∂ / lens / measure) the FAQ
  laws are one face of.
- **STREAMING.md** — how the optimizer's fused per-step term re-embeds coinductively (∂ commutes
  with the optimizer).
- **JIT.md** — the measure→replan loop that supplies the trusted selectivity/cardinality inputs.
- **BENCHMARKS.md** — what the factorization actually buys, measured.
- **README.md** — the project overview and the trust ledger in one page.
