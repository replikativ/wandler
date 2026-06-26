# Architecture — the engine

Wandler is a compiler with a proof obligation. A Clojure pipeline is turned into a
dependently-typed kernel term, rewritten into a faster equivalent, and lowered
back to Clojure — and **every rewrite it keeps is accompanied by a proof, checked
by the kernel, that the rewrite preserves meaning.**

## The pipeline

```
 Clojure form
     │  ELABORATE        wandler.surface.*  (registered surface verbs → kernel ops)
     ▼
 kernel term  (an ansatz CIC Expr — the IR is the proof object)
     │  OPTIMIZE + CERTIFY   wandler.optimize.*  (search proposes; the kernel certifies)
     ▼
 kernel term  (faster, with a proof  optimized ≡ original)
     │  CODEGEN          wandler.runtime  (lowering table → ordinary Clojure)
     ▼
 (fn [..] ..)   — a plain Clojure function in the var
```

The intermediate representation **is** a kernel term, not a bespoke AST. That is
the whole trick: optimization is term rewriting, and "the rewrite is correct" is a
proposition the same kernel that admits Mathlib can check.

## The trust boundary — the kernel is a one-way certifier

```
        proposes (UNTRUSTED)                certifies (TRUSTED)
   ┌────────────────────────────┐     ┌──────────────────────────────┐
   │  the optimizer's search:   │     │  ansatz CIC kernel:          │
   │  recognizers, cost model,  │ ──► │  check-constant on the       │
   │  e-graph, heuristics       │     │  proof  optimized ≡ original │
   └────────────────────────────┘     └──────────────────────────────┘
```

Only the certificate is trusted. The search can be arbitrarily clever or buggy:
a proposed rewrite whose proof does not type-check is **rejected and discarded**,
and the original (or a previously-certified) term is kept. There is no path by
which a wrong rewrite becomes a wrong program — the failure mode is "missed
optimization", never "miscompilation".

Concretely the gate is `cert/verified-rewrite?`, which builds the proof term
`optimized ≡ original` and runs the kernel's `check-constant` on it (the *strict*
checker that re-checks every application argument — not the lenient `inferType`).
This is **translation validation**: the proof is per-program, not a once-and-for-all
compiler-correctness theorem.

## The trust ledger

Not everything in wandler is kernel-proven, and the docs are explicit about which
layer each capability sits in:

| Layer | What's in it | Trust |
|-------|--------------|-------|
| **L0 — CIC-proven** | the fusion/relational/aggregation laws, the FAQ frame rule, the DBSP linear + bilinear increment laws, the first-projection product-lens round-trip (`Lens.fst_{PutGet,GetPut}`, both `Eq.refl`) | machine-checked by the kernel per program |
| **L2 — trusted / external** | WMC model counts (external #P solvers), Giry expectations (Monte-Carlo), a foreign engine's planner (`datahike.q`, stratum — admitted as **typed axioms** via `register-foreign!`), measured selectivity profiles | sound *up to* the external component's spec; part of the TCB |

So a pure relational/streaming pipeline is fully certified; a probabilistic or
cross-engine query is certified *up to* its trusted oracle. `references-axiom?` flags
any term that leans on an L2 axiom. The four-structure programming model (next doc)
spans both layers — the semiring/relational core and the DBSP differential are L0; the
measure (inference) and the optic-composition laws are partly L2 / runtime-witnessed.
See [PROGRAMMING_MODEL.md](PROGRAMMING_MODEL.md) for which is which.

## The three seams

Ansatz exposes three extension points; `(w/install!)` fills all three, which is
how an unmodified ansatz becomes wandler:

1. **Surface** (`wandler.surface.*`) — registered elaborators that turn Clojure
   verbs into kernel terms. `map`/`filter`/`reduce` → `List.map`/`List.filter`/
   `List.foldl`; `group-by`/`join` → `Map.group_by`/`Map.join`; `for` is intercepted
   *before* Clojure's macroexpander and rewritten to `map`/`mapcat`/`filter`.
   See [SURFACE.md](SURFACE.md).
2. **Optimizer** (`wandler.optimize.*`) — the certified rewrite search and cost
   model. See [PLANNER.md](PLANNER.md).
3. **Runtime** (`wandler.runtime`) — the lowering table: each kernel head (`List.foldl`,
   `Map.join`, `List.reverse`, …) maps to a fast Clojure form.

The seams are *registries*, so a vocabulary or a backend can add a verb, a law, or
a lowering without editing the core — e.g. `register-lowering!` adds a codegen entry
and auto-installs it into ansatz's codegen-registry.

## The kernel environment

Wandler runs over an **imported** Lean `Init` library: ansatz parses a `lean4export`
NDJSON dump and admits each declaration as the literal Lean term. So `List.map`,
`Nat.add`, `List.foldl`, the recursors — these are *not* reimplemented; they are
Lean's definitions verbatim, and every `Init` theorem about them is directly usable
(this is what the fusion laws cite). The store is a lazy persistent-sorted-set
(LMDB-backed) loaded on demand in ~40 ms. Wandler's *owned* layer is small: the
finite `Map` (`{ List (K×V) // NodupKeys }`), the `WSemiring`/`WAddMonoid` algebra,
and the relational/FAQ laws — see [the alignment note](#alignment-with-lean).

## Codegen and the runtime — verification licenses the fast representation

The certified term is lowered to a plain Clojure `(fn …)`. The runtime is small —
codegen emits five `wandler.runtime/*` ops into the generated code (`amapl afilter
afoldl apfoldl unfold-take`) plus ordinary `clojure.core` calls; a sixth, `lower`, is
the private dispatcher that *does* the emitting (it never appears in a compiled `fn`).
The fast paths are gated by proofs:

- **Fusion is structural.** `(reduce + 0 (map (fn [x] (* x x)) xs))` lowers to a
  single `apfoldl` with the square inlined into the fold step — one pass, no
  intermediate sequence. The deforestation is the `List.foldl_map` law, certified,
  not a heuristic.
- **Unboxed primitives.** Over a `long[]`/`double[]` input, `amapl`/`afilter`/`afoldl`
  run tight primitive loops calling the element fn via `invokePrim` — **zero boxing**.
  Type hints are *induced from the kernel type*: `Nat`/`Int` → `^long`, `Float`/`Real`
  → `^double`, on both the params and the return position, so Clojure compiles the
  step to a primitive `IFn$LL`/`IFn$LLL` arity.
- **Parallelism is a certificate.** A fold whose operator is a *kernel-proved
  associative monoid with identity* lowers to a fork-join `apfoldl`. The associativity
  proof **is** the parallelization licence.
- **The fast data structure.** A finite `Map` is verified as `{ AList // NodupKeys }`
  but lowered to a Clojure hash-map (O(1) probe); a join verified correct never
  materializes the product.

One subtlety worth knowing: the optimizer's fusion can leave an op **point-free**
(used as a function value, under-applied) — e.g. `map∘map` fusion over a windowed
pipeline leaves `List.reverse α` without its collection argument. Lowerings for such
ops *eta-saturate* (emit `(fn [g] (reverse g))` when under-applied) rather than
assuming full application. This is why windowed analytics compose; see [STREAMING.md](STREAMING.md).

## Portability

The generated function is dialect-agnostic — it is just function calls + `fn`/`let`/`if`,
and the `clojure.core/*` half is fully portable (ClojureScript has all of it; `^long`
hints are harmless metadata there). The only JVM-specific piece is `wandler.runtime`
itself (primitive arrays, `IFn$LL`, fork-join). Each of its emitted ops already has a
portable fallback branch (`amapl`→`mapv`, `afoldl`→`reduce`), so a `runtime.cljc` shim
would make emitted functions run unchanged on ClojureScript / Babashka / native — the
*compiler* (kernel, elaborator, optimizer) stays JVM and runs at build time.

## Alignment with Lean

Because `Init` is imported verbatim, wandler's foundational vocabulary is *definitionally*
Lean's, and theorem-borrowing over those constants is direct. The owned layer (the
`Prod`-keyed `Map` vs mathlib's `Sigma`-keyed `AList`, the `WSemiring` fragment vs
mathlib's `Semiring`, the FAQ/Perm-congruence laws Lean develops only at the `Multiset`
quotient) is bespoke by design — it is the project's own contribution and is each
kernel `check-constant`-verified. The split is structural, not accidental: same CIC
kernel, verbatim `Init`, bespoke algebra.

## See also

- [PLANNER.md](PLANNER.md) — what the optimizer actually does.
- [PROGRAMMING_MODEL.md](PROGRAMMING_MODEL.md) — the algebraic structures the laws live in.
- [The trust ledger and dev REPL](../README.md) — running it yourself.
