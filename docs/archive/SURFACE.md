# The surface — what Clojure you can write

You write ordinary Clojure. The surface layer (`wandler.surface.*`) elaborates a
useful subset to kernel terms; everything below is **differential-tested** — each
verb is compiled through `a/defn` *and* checked against `clojure.core` on the same
input, so a lowering that diverges shows up as a value difference, not just a proof
failure (see `test/wandler/transducer_breadth_test.clj`).

A function enters the verified world with a signature — either a malli `m/=>` form
or an inline `[xs :- (List Nat)]` binder:

```clojure
(require '[malli.core :as m] '[ansatz.core :as a] '[wandler.core :as w])
(w/install!)

(m/=> bigsq [:=> [:cat [:sequential [:int {:min 0}]]] [:sequential :int]])
(a/defn bigsq [xs]
  (->> xs (filter (fn [x] (< 2 x))) (map (fn [x] (* x x)))))

(bigsq [1 2 3 4])      ;; => (9 16)   — verified, fused, certified, compiled
(w/explain 'bigsq)     ;; => {:verified? true, :rewrites [...], ...}
```

## The vocabulary

`(w/vocabulary)` returns the live registry. The core verbs, grouped:

### Map / filter / fold

| Verb | Lowers to | Notes |
|------|-----------|-------|
| `map` `mapv` | `List.map` → `amapl` | unboxed `long[]`/`double[]` aware |
| `filter` `filterv` `remove` | `List.filter` → `afilter` | `remove` ≡ `filter (complement p)` |
| `mapcat` | `List.flatMap` | `(fn [x] [x x])` vector literals work |
| `map-indexed` | `List.mapIdx` | `f : Nat → α → β` |
| `reduce` | `List.foldl` → `afoldl` / `apfoldl` | parallel fork-join when the op carries a proven monoid licence |
| `apply` | `reduce ⊕ id⊕` | `(apply ⊕ coll)` for a monoid ⊕ (`+`→0, `*`→1, `max`→0) |
| `reductions` | `List.scanl` | running aggregate |

`reduce` infers the accumulator type from the *step*, so `(reduce + 0 …)` over `Int`
folds in `Int`. A bare binary verb as the step is eta-expanded to the expected arity,
so `(reduce max 0 xs)` / `(reduce min … xs)` work (kernel-const ops `+`/`*` stay bare
so the parallel-fold recognizer still fires).

### Slicing, windowing, sampling

| Verb | Lowers to | Notes |
|------|-----------|-------|
| `take` `drop` `take-while` `drop-while` | `List.take` … | `take` over a stream is the *window* |
| `drop-last` | `List.dropLast` | drops the final element |
| `partition-all` | inlined verified fold | n-chunks, keeps the short tail (n=0 → one chunk) — a **tumbling window** |
| `partition` | `filter (length≡n) ∘ partition-all` | drops the incomplete final chunk |
| `take-nth` | inlined verified fold | every k-th element — **downsampling** |
| `interpose` | `List.intersperse` | |
| `reverse` `concat` `nth` `first`/`second`/`last`/`rest` | `List.*` | `nth` is the 3-arg (default) form |

`partition-all` / `partition` / `take-nth` have no `Init` primitive (Lean's chunking
lives in Batteries). Rather than re-derive a counter-resetting structural recursion
(which the recursion machinery rejects), they are **inlined as non-recursive `foldl`
encodings** with the element type spliced in — so they kernel-verify and SOAC-lower
with no termination obligation, and compute the same values as `clojure.core`. See
[STREAMING.md](STREAMING.md) for the windowing use cases.

### Relational

| Verb | Lowers to | Notes |
|------|-----------|-------|
| `group-by` | `Map.group_by` | key type from the fn's codomain; needs `DecidableEq` |
| `join` | `Map.join` | hash probe O(n); the optimizer may reorder / factor / push down |
| `vals` `keys` `count` | `List.map snd/fst`, `length` | over a group-by/join result |
| `distinct` `dedupe` `sort` `sort-by` | `List.eraseDups` … | `sort` needs a `Bool` comparator |
| `frequencies` | foldl + AList bump | extrinsic accumulation |
| `some` `every?` `contains?`/`member` | `List.any`/`all`/`elem` | membership normalizes to the semijoin shape |
| `zip` `interleave` | `List.zip`, `mapcat`-over-zip | two collections |

### Control & comprehensions

| Form | Handling |
|------|----------|
| `let` (incl. multi-binding) · `if` · `cond` | direct |
| `->` `->>` | pure form rewrite (threading) |
| `for` comprehensions | intercepted **before** Clojure's `for` macro and rewritten to `map`/`mapcat`(cartesian)/`filter`(`:when`)/`let`(`:let`) |
| `even?` `odd?` `mod` `quot` `max` `min` `inc` `dec` | type-directed Nat ops |

A `for` example — multiple generators are a cartesian product:

```clojure
(a/defn pairs-sum [xs :- (List Nat)] Nat
  (reduce + 0 (for [x xs y xs] (* x y))))   ;; ≡ (Σx)·(Σy); the optimizer can even factor it
```

### Records & EDN

Idiomatic record ops over your malli `[:map …]` schemas compile and kernel-verify:
`assoc`/`update`/`get`/`get-in`/`select-keys`, keyword access `(:k r)`, nested
destructuring `(fn [[c o]] …)` over `Prod`. There is also a dynamic **EDN `Value`**
universe (`int?`/`get`/`<`/`==` over heterogeneous data) that lowers and runs at
runtime. See [DEPENDENT_TYPES.md](DEPENDENT_TYPES.md) and the Cookbook.

## Honest limits

The surface is a *subset*. Known gaps (clean rejections, not silent wrong answers):

- **`keep`** (an `Option`-producing fn) is **not** registered — it elaborates through
  `List.filterMap` in principle, but the surface→`Option` bridge isn't wired, so the
  verb is intentionally rejected today. Spell it `(map f …)` then `(filter some? …)`.
- **`for` modifiers** beyond `:when`/`:let` (`:while`, and a `:when` that references a
  preceding `:let` binding) are not modelled.
- **Recursion** with a *resetting* counter (e.g. a faithful `toChunks`) is rejected by
  the structural/WF machinery — the inlined encodings above sidestep it.
- **Nat truncation**: under a `[:int {:min 0}]` (= `Nat`) signature, subtraction
  truncates at 0 (`0 - x = 0`). Faithful to `Nat`, but it diverges from Clojure's
  integers — use an `Int` carrier if you need signed subtraction.

When a verb isn't supported it fails *transparently* at elaboration with an
actionable message, never by miscompiling.

## See also

- [Cookbook](COOKBOOK.md) — the copy-paste idiom set and the three install levels.
- [Streaming & modes](STREAMING.md) — windows, sampling, and the execution modes.
- [Architecture](ARCHITECTURE.md) — how a verb becomes a certified, lowered function.
