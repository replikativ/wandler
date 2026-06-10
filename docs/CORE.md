# Wandler — Architecture

> *Wandler* is the verified data-transformation runtime built on **ansatz** (a Lean-4-style CIC
> kernel in Clojure). You write ordinary Clojure data pipelines; they are elaborated to kernel
> terms, **optimized by certified rewriting**, and lowered to fast Clojure — and the same core can
> be read as a relational query, a counting/datalog/shortest-path engine, a probabilistic-inference
> engine, an incremental (DBSP) view, or a bidirectional view, by changing the *algebraic structure*
> it is interpreted in.
>
> This document is the architecture spec for the clean **`wandler.core`** rebuild (Option B). It is
> grounded in the existing `research`-branch code; file references are to that code.

---

## 0. The one idea

There is **one logical core**: a pipeline term over `List`/`Map` combinators, interpreted in a
**semiring** `S`. Everything else is a *reading* of that core:

```
                                  read at semiring S …
        ┌───────────────────────────────────────────────────────────────┐
        │  Bool (∨,∧)        →  relational query / set semantics         │
        │  Nat  (+,×)        →  counting / cardinality                   │
        │  Bool (∨,∧) + fix  →  datalog reachability                    │
        │  Tropical (min,+)  →  shortest path                           │
        │  Provenance (∪,⊗)  →  lineage → (via WMC) probability         │
        │  Prob  (+,×)       →  FinDist / expectation                   │
        └───────────────────────────────────────────────────────────────┘
                                  … run in mode M …
        ┌───────────────────────────────────────────────────────────────┐
        │  List / Box        →  batch (fused)                           │
        │  Zset (A→Int)      →  incremental (DBSP, with deletions)      │
        │  Strm              →  async / reactive                        │
        └───────────────────────────────────────────────────────────────┘
```

and the **single optimization principle** is: **join-order = variable-elimination-order = the plan.**
A relational join reordering, a datalog evaluation order, and a probabilistic variable elimination
are *the same rewrite* on the core, justified by the *same* semiring laws (⊕/⊗ commutativity +
distributivity).

The **kernel's only job is to say yes/no** to "the optimized term equals the original." It never
knows what an optimizer, a planner, or a probability is.

---

## 1. The stack (compile pipeline + trust boundary)

```
   Clojure surface            (a/defn revenue [orders :- (List …)] …
   map / filter / reduce /     (reduce + 0 (map :amt (filter premium? orders))))
   group-by / join / records          │
                                       │  ELABORATE  (elaborator-registry — SEAM 1)
                                       ▼
   kernel IR  =  CIC Expr      List.foldl + 0 (List.map amt (List.filter premium? orders))
   (the term IS the IR)                │
                                       │  OPTIMIZE   (*optimize-hook* — SEAM 2)
                                       │    simp fusion + cost search + (e-graph)
                                       │    + physical strategy as certified rewrites
                                       ▼
                              term'  +  PROOF : term = term'     ◀── kernel CERTIFIES (one-way)
                                       │                              (.check + isDefEq;  L0)
                                       │  LOWER      (codegen-registry — SEAM 3)
                                       ▼
   fast Clojure               (afoldl + 0 …)  /  (apfoldl + …) parallel  /  unboxed long[]
                                       │
                                       ▼  eval → a native fn
```

**Trust levels** used throughout:

| | meaning | enforced by |
|---|---|---|
| **L0** | kernel-certified — an algebraic law proven as a CIC term | Java `TypeChecker.check` / `env/check-constant` (the path that admits Mathlib) |
| **L1** | sound by construction — codegen of a proven-equal term; falls back to the proven body if it can't lower | `define-verified` invariant |
| **L2** | trusted oracle — numeric/external, *not* a CIC proof | WMC solvers, Giry integrator, datahike planner, measured selectivity |

The optimizer's **search** is untrusted; only the **certificate** is L0. A bad rewrite is rejected, never miscompiled.

---

## 2. The kernel boundary — one-way, a pure certifier

The dependency is strictly **runtime → kernel**. Kernel namespaces (`ansatz.kernel.*`) require
nothing from the optimizer/planner/relational/inference layers.

```
   wandler runtime  ───requires───▶  ansatz kernel        (one direction only)
   (optimize, plan, codegen, laws)   (expr, env, tc, simp)

   optimizer hands the kernel:   a GOAL  @Eq T orig term      and a PROOF
   kernel answers:               .check(proof) ∧ isDefEq(typeof proof, goal)  →  yes / no
```

- The soundness gate is `optimize/verified-rewrite?`: it closes goal+proof over the local context,
  builds `(TypeChecker. env)` with 50 M fuel, and calls **`.check`** (strict — re-checks every
  application argument, like Lean's `check`) then `.isDefEq`. **Not** the lenient `inferType`.
- Relational laws are **ordinary theorems** admitted via the same `env/check-constant` path as any
  Mathlib declaration. The kernel treats `Map.join_comm` exactly like `Nat.add_comm`. There is **no
  optimizer-specific kernel extension** — this is Lean's `@[csimp]` discipline (an optimized form is
  admitted only with a kernel-checked proof it equals the original; the optimizer merely *decides*).

⚠️ **Footgun to preserve awareness of:** both Clojure `tc/infer-type` and Java `TypeChecker.inferType`
are *lenient* (assume well-typed input). Only `.check` / `check-constant` are authoritative. Every
soundness gate must use the strict path. (See `lenient-check-audit-findings`.)

---

## 3. Optimizer + planner (the same engine, two cost dimensions)

**The IR is the kernel `Expr` itself** — there is no separate plan IR. `ansatz.plan` is a *read-only
lens* (`term->plan`/`plan->term`, round-tripping via a stashed `::raw` head+args), used for `explain`
and as the α/γ bridge view — not for rewriting.

**The rewriter is `simp`.** `optimize-term` builds oriented simp-lemmas from a curated law set + a
discrimination-tree index, and `simp/simp-expr-result` does matching/congruence/fixpoint driving
**and returns the equality proof** `orig = result`.

```
   optimize-cost(term)                                       ── greedy, cost-gated, certified ──
     │  apply confluent FUSION set        (always; map_map, filter_filter, foldl_map, filterMap…)
     │  then greedily try each COST-rewrite:
     │     adopt rwᵢ  ⟺  verified-rewrite?(term, rwᵢ)   ∧   pipeline-cost(rwᵢ) < pipeline-cost(term)
     │  + direct paths for permutative/shape laws simp would canonicalize away:
     │     try-pre-agg-index → try-grace-hash → try-count/fold-factor → try-join-reorder → hoist/spill
     │  compose all adopted steps with Eq.trans
     ▼
   { term' , proof : term = term' , verified? , rewrites , cost }

   optional: *use-egraph?*  swaps greedy for EQUALITY SATURATION (grind e-graph as an untrusted
             search oracle: saturate with all laws, extract-min-cost, certify the kept term).
```

**Cost model — three nested static notions, all heuristic (affect search quality, never soundness):**

- `soac-cost` — count of SOAC ops (proxy for passes/allocations).
- `pipeline-cost` / `pipeline-resources` — **datahike's cardinality estimator made static**: propagates
  `{:size :time :memory}` (filters shrink by selectivity, joins expand by fanout, folds collapse to 1;
  memory tracks the held build-side index). **This is the gate the driver uses**, so a SOAC-neutral
  *reorder* (filter→join pushdown) is adopted for its cardinality win.
- **selectivity** — static head-comparator table (`:eq 0.1`, `:range 0.33`, …) by default; overridable
  by a **measured/JIT profile** (`measure-selectivity`) or an engine's **`:estimate`** (`:sizes`,
  `:ndv` distinct-key oracle). This is the one knob where L2 numbers tune an L0-safe search.

**Physical strategy is *not* a separate planner** — it is fused into `optimize-cost` as additional
**certified rewrites**, gated by the `:memory`/`:ndv` cost dimensions:

```
   ndv ≪ build-mem      →  PRE-AGGREGATED FAQ INDEX   (Map.foldl_join_sum_factor; O(distinct keys))
   index > mem-budget   →  GRACE-HASH (spill)         (Map.foldl_join_blockfold + List.chunk)
   else                 →  AGGREGATION-THROUGH-JOIN   (Map.count/foldl_join_factor)  ── never materialize L×R
                          + JOIN REORDER / drive-dir  (Map.join_comm → join_length_comm, Perm→Eq)
   idx-mem ≤ budget     →  IN-MEMORY HASH  (hoist Map.group_by above the fold, build once, O(N))
   idx-mem > budget     →  NESTED-LOOP     (Map.bucket_content, per-row filter, no held index)
```

Each emits a proven-equal kernel term; **codegen lowers `group_by`/`join`/`foldl`/`lookup` verbatim**
— the planner chooses the plan *as a term*, codegen blindly emits it.

**The certified relational law alphabet** (proven Init-only in `relational/proofs.clj` + `rel_laws.clj`,
applied by name in `optimize`):

| law | what it licenses |
|---|---|
| `map_map` / `filter_filter` / `foldl_map` / `map_id` | classic SOAC fusion (Init) |
| `List.map_filter_filterMap` | map∘filter → **single pass** |
| `Map.filter_join_pushdown` (left/right) | push σ below ⋈ |
| `List.elem_filter_eq_index_probe` | nested-loop member → **hash semijoin** (+ anti-join) |
| `Map.count_join_factor` / `Map.foldl_join_factor` | **aggregation through join** (count / general monoid) |
| `Map.join_comm` → `Map.join_length_comm` | join commutativity / **drive-direction** (via `Perm`→`Eq` bridge) |
| `Map.foldl_join_sum_factor` | **pre-aggregated FAQ index** (separable SUM, O(distinct keys)) |
| `Map.foldl_join_blockfold` + partition chain | **grace-hash spill** |

---

## 4. Execution engine (codegen) — verification licenses the fast representation

`ansatz->clj` recursively lowers a kernel term to Clojure, dispatched on expr-kind then head-constant.
The headline: **a kernel proof unlocks a runtime representation an ordinary compiler can't assume.**

```
   kernel type / proof                 runtime representation                  why it's sound
   ─────────────────────               ─────────────────────                  ──────────────
   Nat / Int  (Int64 trust)        →   primitive long (BigInt fallback)       gen-tested faithfulness
   List                            →   lazy seq (stays lazy) / vector         observational equality
   Map {AList // NodupKeys}        →   real Clojure hash-map (O(1) get)       NodupKeys ⇒ no dedup
   Prod                            →   [fst snd] vector                       erased Subtype.val/mk
   N-ctor inductive                →   tagged [cidx field…] vector            recursor → native dispatch
   record (Subtype)                →   defrecord, direct .field read          verified field type

   λ over ^long param + ^long ret  →   IFn$LL invokePrim  (ZERO boxing)       prim-tag both ends
   reduce ⊕ id   (⊕ proven Monoid) →   apfoldl → fork-join ccr/fold           assoc+identity = certificate
       … over a long[] ≥ 131072    →   fold-longs-parallel (unboxed ∥)        per-chunk from identity
   map g ∘ foldl f                 →   one fused step (f acc (g x))           List.foldl_map proof
   affine chain (K maps)           →   λx. A*x+B   (2 ops, not 2K)            left_distrib/mul_assoc/funext
```

**Parallel-monoid fold (the lean-reducers idea, in core).** `monoid-fold-op` recognizes a `List.foldl`
whose step is a registered op `⊕ ∈ {Nat.add, Nat.mul, Int.add, Int.mul}`, whose `init` is `⊕`'s
identity, **and whose associativity+identity theorems are present in the env** — the *presence of the
proof is the licence*. It then emits `apfoldl`, which:
- `long[]` + `IFn$LLL` step + ≥131072 elts → **`fold-longs-parallel`** (unboxed *and* fork-join: split
  into `min(cores, n/grain)` chunks, each reduced **from the identity** in a `future`, partials merged
  by `⊕`);
- vector → `clojure.core.reducers/fold` (combinef = `([] init)([l r] (⊕ l r))`);
- non-monoid / wrong identity → sequential `afoldl` (e.g. `reduce + 1` is **not** parallelized).

**`define-verified` invariant (L1):** if the optimized term can't lower, codegen silently falls back to
the original proven-equal body. **The optimizer can only change speed, never results.**

---

## 5. The algebraic structures (the heart)

Wandler is a **verified monoidal category carrying four structures**, and the *bet* is the **certified
coherence between them**. Each structure is either **CORE** (in `wandler.core`, Option B) or an
**EXTENSION tier**.

```
                              ┌──────────────────────────────┐
                              │   SEMIRING  (S, ⊕, ⊗, 0̄, 1̄)  │   relational sum-product
                              │   Rel A S = A → S            │   ⊕ = ∃/union   ⊗ = ⋈/product
                              └──────────────┬───────────────┘
              ⊗ is a monoid │                │                │ ⊕ is a monoid
        ┌─────────────────────┘              │                └─────────────────────┐
        ▼                                    ▼                                       ▼
   MONOID                              MEASURE / inference                     RING / GROUP
   (parallel fold,                     FinDist ─▶ WMC ─▶ Giry                  Z-set (A→Int)
    marginalize)                       (L0)     (L2)   (L2)                    DBSP, deletions
   CORE                                EXTENSION  (prob-log, outside kernel)   EXTENSION
                                             │
                      COMONAD / stream ──────┘ (mode lattice, ∂)              LENS / optic
                      batch ▷ diff ▷ async                                    get/put, backward
                      EXTENSION                                               EXTENSION
```

### 5.1 Semiring (CORE) — `semiring.clj`
- Kernel structure `Semiring S := { zero one : S, add mul : S→S→S }` (a real `a/structure`), with
  instances `Semiring.Bool` (existence) and `Semiring.Nat` (counting) admitted as kernel constants —
  so the planner is *generic over S*.
- Runtime instances: `existence` (Bool ∨/∧), `counting` (ℕ/ℤ +/×), `tropical` (min/+, shortest path),
  `probability` (ℝ≥0 +/×), `min-max-prob` (fuzzy), `provenance` (Green–Tannen DNF, ∪/⊗).
- **Sum-product unification:** `rel-add`/`rel-mul`/`rel-join`/`rel-sum` are *generic over `S`* — the
  same code is a counting join, an existence join, a fuzzy join, by swapping `sr`.
- **FAQ / variable elimination:** a `factor = {:vars :rel}`; `factor-join` (⊗), `factor-marginalize`
  (⊕-out), `elimination-order` (min-degree). **The elimination order is the plan** — it sets cost not
  result, justified by ⊕/⊗ comm + distributivity. This *is* `join-order = elimination-order`.
- **Recursion (datalog)** is gated on **absorption** (`recursion-safe?`): the kernel theorem
  `Bool.absorptive` (`∨ a (∧ a b) = a`) is the certified version of datalog/Scallop's POPS matrix.
- L0 certificates: `Bool.absorptive`, `Semiring.bool_{or,and}_comm`, `Semiring.bool_distrib`.

### 5.2 Monoid (CORE) — `dist_laws.clj`
The semiring's **⊗ is the monad's monoid; its ⊕ is the parallel-fold / marginalize monoid.** Monad
laws are proven *generic over the ⊗-monoid* (laws-as-hypotheses): `WList.left_unit`
(`bind (return a) f = f a`, needs `one_mul`), `WList.right_unit` (needs `mul_one`); associativity
deferred (needs `mul_assoc` + flatMap-congruence the kernel lacks). The same associativity is the
certificate for fork-join parallelization (§4).

### 5.3 Measure / inference (EXTENSION — prob-log, *outside* the kernel) — `dist.clj`, `wmc*.clj`, `giry.clj`
A graded stack, the trust boundary running through it:
```
   FinDist (discrete)        FinSet/FinDist = Kleisli view of Rel A S          L0  (exact finite sums)
        │   fin-bind = ⊕_a m(a) ⊗ (f a)   (law of total probability)
        ▼
   WMC (correlated discrete) provenance DNF  ──count──▶  probability           L2  (#P-hard, external)
        │   :enumeration (exact, reference) · :logicng (BDD) · :ganak/:d4
        ▼
   Giry (continuous)         measure = sampler; expectation = ∫ (Monte-Carlo)  L2
```
- **Why outside the kernel:** WMC is `#P`-hard and done by compiled/external solvers; Giry's
  `expectation` is a numeric integral. Neither is a CIC proof — the *formula* is L0, the *count* is L2.
- **Why WMC at all (the load-bearing example):** when a fact appears in multiple derivation paths, the
  naïve `(prob,+,×)` product **double-counts** (0.234, wrong); WMC over the provenance formula is exact
  (0.219) because the DNF records the sharing. When paths are disjoint, product = WMC (the 0.776 case),
  and **FinDist agrees with provenance→WMC** — "the monad ≡ sum-product."
- **Trust discipline:** compiled backends are **differentially cross-checked against `:enumeration`**
  (≤18 facts, throw on >1e-6 disagreement). `Giry.of-findist` lifts discrete into continuous and the
  expectations agree — discrete is the L0 sub-object of the L2 measure.

### 5.4 Ring / differential — DBSP (EXTENSION) — `dbsp.clj`
A **different mode over the same relational core**: Z-sets `List(A×Int)` form an **abelian group**
(negative weight = retraction → deletions). Proven L0: the **product rule** `Map.join_count_product`
(`δ(L⋈R) = δL⋈R ⊞ L⋈δR ⊞ δL⋈δR`, semi-naive datalog increment), `Zset.weight_append` (weight is a
group homomorphism → DBSP Thm 5.4, linear ops incrementalize uniformly for insert *and* delete),
`List.sum_filter_incr` (modular `(Q1∘Q2)^Δ`).

### 5.5 Comonad / stream + Lens / optic (EXTENSIONS) — `mode.clj`, `lens.clj`
- **Mode lattice** (`batch ▷ diff ▷ async`): differentiation is *comonadic* (context = history),
  async is *monadic*, combining them is a *distributive law* (Uustalu–Vene; Bahr modal FRP).
  `mode-of-type` reads the kernel type **head constant** (`List→batch`, `Zset→diff`, `Strm→async`) and
  `route` picks the γ-lowering. The `∂` pass differentiates a subterm to Z-set increments (chain rule
  `∂(g∘f)=∂g∘∂f`) emitting a per-op certificate; the one kernel law `Mode.diff_async_dist` proves a
  linear operator commutes with stream integration ∫.
- **Lens** (the backward/read-write direction): product-lens round-trip laws proven
  (`Lens.fst_PutGet`, `Lens.fst_GetPut`); records' `(:k r)`/`(assoc r :k v)` *are* this field lens;
  delta-lenses are the bidirectional twin of the DBSP ∂.

---

## 6. Lifting external engines (datahike / stratum)

The bridge is an **optional α/γ adapter** over the plan lens. **The external engine's planner is a
trusted oracle behind a typed API spec; the kernel certifies only the algebraic rewrites.**

```
   engine logical IR  ──α (:lift)──▶  ansatz PLAN ──plan->term──▶  kernel TERM
   {:op :scan/:filter/:join}                                            │ optimize-cost  (CERTIFIED)
                                                                        ▼
   engine physical    ◀──γ (:lower)──  ansatz PLAN ◀──term->plan──  TERM'  + proof TERM = TERM'
   (datahike :entity-join /                                          verified? = (plan ≡ original)
    stratum PSIMDFilter,PSortedMerge)
```

- An engine is a **data-only adapter** `{:detect? :lift :lower :estimate}` registered via
  `register-engine!`; wandler has **no hard dependency** (adapters `requiring-resolve` their engine in
  a `try`). The engine's API contract is admitted as **typed axioms** (a deliberate, opt-in,
  property-tested TCB *beyond* the kernel).
- **datahike** (Datalog/Datomic triple-store over a durable PSS index) gets a genuinely **dependent**
  API spec: `Datahike.q : (db) → (f : FindSpec) → Result f`, where `Result` is a type-level function by
  large elimination — so `q db (fscalar tint) : Nat`, `q db (fcoll tint) : List Nat`. Its bridge does
  **decorrelation**: a correlated subquery (N per-row queries) α-rewrites to **one** `Map.join`, then
  aggregation-through-join factorizes it — kernel-certified.
- **stratum** (SIMD columnar OLAP engine, Postgres-wire) gets predicate *compilation* (`[col op arg] →
  Nat.blt/ble/beq` Bool lambdas) and lowers to `PSIMDFilter`/`PSortedMerge`.
- **One logical domain, interchangeable backends** is demonstrated: `users` from datahike + `orders`
  from stratum are joined+aggregated, optimized **once** in the kernel IR, then **each source
  γ-lowers to its own engine** — the proof is independent of which engine runs which piece. This is the
  α/γ "optimize in the certified middle, execute on any backend" story.
- **The cost handshake** (`datahike :estimate → optimize :selectivity/:sizes`) is *plumbed* in the cost
  model (`pipeline-cost` is datahike's `estimate.cljc` made static), but the datahike adapter does not
  yet emit a live `:estimate` fn — sizes are passed by hand in tests. **A clean bridge API should close
  this** (fetch from `datahike.query.estimate/estimate-pattern` into the `:estimate` slot).

---

## 7. The `wandler.core` boundary (Option B) and the seams

**Core = Rings 0–2** (the certified relational data-pipeline runtime): the `collections` surface +
records/relational/kmap + the optimizer (optimize/egraph/plan/faq-plan) + the proven laws + the
parallel-monoid fold codegen. **One surface (`collections`).** The parallel-reducer *capability* is in
core; the transducer *syntax* (lean-reducers `Reducer`/`FoldSpec`/`Par`/`Algebra`) is the first tier.

**Additive integration via three seams in ansatz's `define-verified`** (NOT a carve):

```
   ansatz.core/define-verified  =  elaborate ─▶ check ─▶ optimize ─▶ codegen
                                       │           │        │           │
                                   SEAM 1       (kernel)  SEAM 2      SEAM 3
                                elaborator-     L0 check  *optimize-   codegen-
                                registry                  hook*       registry
                                (EXISTS)                  (new ~5 ln)  (new)
                                       ▲                     ▲           ▲
   wandler installs:           collection elaborators    the certified  collection lowering
                               (map/filter/-> …)         fusion pass    (amapl/afoldl/apfoldl)
```

ansatz **alone** = base `a/defn` runs (Nat/Int, no collections, no fusion). ansatz **+ wandler** = the
full pipeline. This dissolves the carve artifact `pipeline.clj` (2107 lines) into seam-fillers.

**Tier order off `research`:** (1) reducers/transducers (lean-reducers) · (2) edn dynamic data ·
(3) modes (DBSP/stream) · (4) inference (semiring·dist·wmc·giry) · (5) bridges · (6) regex/gradual/lens.

---

## 8. Cleanup targets for the rebuild (tangles found in `research`)

These are the things to *fix while porting*, not carry over:

1. **Physical strategy is welded into one giant `optimize-cost`** (deeply nested `cond` mixing algebraic
   reorders, hoisting, spill, proof composition). → physical planning as its own module *over* the
   certified algebraic layer.
2. **`faq_plan` reaches into `ansatz.core` (`a/env`, `ansatz->clj`) + `semiring`** — couples the planner
   to the runtime/codegen and a specific frontend. → depend on seams, not internals.
3. **`rel_laws/build-all` mutates the global `ansatz-env` atom** (`swap!`/`reset!` race). → a pure
   `env → env` law installer.
4. **`plan.clj` is advertised as the α/γ engine bridge but is read-only.** → wire it (it's the
   interchangeable-backend story).
5. **Two parallel monoid mechanisms:** the codegen `monoid-fold-ops` hardcoded 4-op table vs the generic
   `reducers/MonoidSpec`. → unify on the lean-reducers `MonoidSpec` (laws-as-fields).
6. **Bridge API warts:** the `:lift` arity disagrees with `bridge/optimize-plan`'s call convention; n-ary
   joins and non-Nat columns are hard-wired to demo shapes; the datahike `:estimate` slot is unfilled.
7. **Lenient-vs-strict checker** coexistence (§2) — keep every gate on `.check`/`check-constant`.

---

## 9. REPL with ansatz (the dev experience)

Because integration is "register elaborators + install laws + set hooks" (not a build dance), a `:dev`
alias can boot the whole stack:

```clojure
;; dev/user.clj
(defn go []
  (require '[ansatz.core :as a] '[wandler.core :as w])
  (a/load-init!)        ; or (a/init-store! "init") for the full Init
  (w/install!)          ; register collection elaborators + the optimize hook + the laws
  :ready)
;; clj -M:dev  →  (go)  →  write (a/defn …) pipelines, (w/explain …), run them
```

---

### Appendix — trust ledger

| L0 (CIC-proven) | L2 (trusted / numeric) |
|---|---|
| every relational law (§3 table); fusion; pushdown; semijoin; FAQ factorization; join_comm | measured / JIT selectivity profiles |
| `Bool.absorptive`, `Semiring.bool_{or,and}_comm/distrib`; `WList.{left,right}_unit` | WMC counts (enumeration ref · LogicNG BDD · Ganak/d4) — diff-checked ≤18 facts |
| all DBSP increment + Z-set group laws; `Mode.diff_async_dist`; `Lens.fst_{PutGet,GetPut}` | Giry `expectation` (Monte-Carlo / integrator) |
| FinDist exact finite sums; Int64 faithfulness (gen-tested) | `Datahike.q` / `register-foreign!` leaves (typed axioms); external engine planners |
