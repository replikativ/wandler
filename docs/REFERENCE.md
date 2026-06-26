# Wandler — Reference

The lookup doc: **which verb, what does it lower to, what's the gotcha.** You write ordinary
Clojure inside an `a/defn`; wandler elaborates it to a term in the ansatz CIC kernel, optimizes
it with a machine-checked proof that the optimized pipeline equals the one you wrote, and lowers
it to fast Clojure. This page enumerates the closed verb vocabulary, the type-annotation forms,
the verified idioms, and — load-bearing for trust — the **clean rejections**.

The surface is a *type-directed staged elaborator over a closed vocabulary* (Lean's
`elab_rules`, not abstract interpretation): inside the vocabulary verbs compose freely; at its
edge a verb it doesn't know is a transparent error, never a silent miscompile. The single source
of truth is `src/wandler/surface/vocabulary.clj`; ask it live with `(w/vocabulary)`.

> **Trust ledger.** A verb's **structure** (the kernel denotation, the fusion/factorization
> proof) is L0 — checked by the CIC kernel. A verb's **runtime lowering** is L1 — a hand-written
> Clojure function trusted to implement its denotation (e.g. `afilter`, `clojure.core/group-by`,
> the runtime `Map` is a `hash-map`). The lowering table below names that L1 boundary per verb;
> measured selectivity, foreign-engine results, and async clocks are the L2 boundary (TUTORIAL
> §trust-ledger). The *equality between naive and optimized* is always L0.

Setup (see TUTORIAL §0):

```clojure
(require '[ansatz.core :as a] '[wandler.core :as w] '[malli.core :as m])
(a/init! "test-data/init-store" "init")
(w/install!) (w/install-streaming!) (w/install-laws!)
```

> **Numbers.** Element type `Nat` is the kernel's arbitrary-precision natural, so results print
> with an `N` suffix (`16N`, `(6N 15N …)`). It's an ordinary integer; prose drops the `N`.

---

## The verb vocabulary

### Collections · element pipelines (`:core`)

These fuse: a `map`→`filter`→`reduce` chain collapses to a single `foldl` pass, proved equal.

| verb | meaning | lowers to (kernel op → runtime) | gotchas |
|---|---|---|---|
| `map` / `mapv` | elementwise transform | `List.map` → `amapl` (unboxed `long[]`/`double[]` aware) | `mapv` ≡ `map` (verified bodies are eager); over a `Strm` routes to `smap` |
| `filter` / `filterv` | keep where pred | `List.filter` → `afilter` | **List only** — a raw stream is rejected (window first) |
| `remove` | drop where pred | `List.filter (not∘p)` → `afilter` | inline-fn body is negated in place; a named pred is eta-expanded |
| `mapcat` | concat-map, `f : α→List β` | `List.flatMap` → `mapcat` | |
| `map-indexed` | `f : Nat→α→β` | `List.mapIdx` → `map-indexed` | |
| `reduce` | fold, acc type from the step | `List.foldl` → `afoldl`; `apfoldl` (parallel fork-join) under a monoid licence | over an infinite `Strm` → **productivity-gate reject** |
| `apply` | fold with a monoid `⊕` | `List.foldl ⊕ id⊕` → reduce | `+`→0 `*`→1 `max`→0; **`apply min` unsupported** (no `Nat` identity) — spell `(reduce min …)` |
| `reductions` | running scan | `List.scanl` → reductions; `Strm.scan` over a stream | |
| `into` | eager realize | the desugared SOAC pipeline | **`(into [] xform? coll)` only** — vector target |
| `transduce` | xform + rf | reduce over the desugared pipeline | xform must be an **inline** `(comp (map f) (filter p) …)` literal |
| `sequence` | as `into` | the desugared pipeline | same inline-xform rule |
| `count` | size | `List.length` / `Map` entries / `vsize` → count | |
| `take` / `drop` | prefix / suffix | `List.take` / `List.drop` | over a `Strm`, `take` is the **window** (Strm→List) |
| `take-while` / `drop-while` | conditional prefix | `List.takeWhile` / `List.dropWhile` | |
| `take-nth` | every k-th | inlined foldl over a `(counter,kept)` Prod | the SOAC pipeline |
| `drop-last` | drop final elem | `List.dropLast` | 1-arg only |
| `partition-all` | tumbling window | inlined chunk-foldl | keeps the short tail; `n=0` → one chunk |
| `partition` | tumbling window | `filter (length≡n) ∘ partition-all` | **drops** the incomplete final chunk |
| `range` | source | `List.range n`; `(range)` → `Strm.range` (infinite) | 0-arg form needs streaming installed |
| `nth` | indexed get | `List.getD` → nth | **3-arg `(nth coll i default)` only** (2-arg needs a bounds proof) |
| `reverse` `concat` `interpose` | list rearrange | `List.reverse` / `List.append` / `List.intersperse` | `concat` n-ary nests as append |
| `first` `second` `rest` `last` | head/tail | Prod→`fst`/`snd`; List→`head?`/`tail`/`getLast?` (Option) | on a List these return an `Option` |
| `inc` `dec` | `Nat` succ/pred | `Nat.succ` / `Nat.sub x 1` (truncated) | `dec` is `max 0` truncated |
| `->` `->>` | thread | pure form rewrite | macro-shaped (no runtime) |

### Two-input verbs (`:core`)

| verb | meaning | lowers to | gotchas |
|---|---|---|---|
| `zip` | pair two Lists | `List.zip` → `(map vector a b)` | truncates to the shorter |
| `interleave` | alternate two Lists | `List.flatMap (Prod→[fst snd]) (zip a b)` | |

### Relational (`:core`) — needs `(w/install-laws!)` to factorize

| verb | meaning | lowers to | gotchas |
|---|---|---|---|
| `join` | equi-join on key fns | `Map.join` → group-by + hash probe O(n); optimizer reorders/factors, certified | key fns compiled with element types injected |
| `group-by` | bucket by key fn | `Map.group_by` → `clojure.core/group-by` | key type from `f`'s codomain; needs `DecidableEq` |
| `member` | membership | `List.elem` → index probe (after `filter∘member` → certified semijoin rewrite) | the canonical spelling |
| `contains?` | membership | normalizes to `List.elem` | `(contains? ys x)` or `(contains? (set ys) x)` |
| `some` | `∃` / membership | `List.any` / `List.elem` | `(some #{x} ys)` normalizes to membership |
| `every?` | `∀` | `List.all` → every? | |
| `distinct` | dedup all | `List.eraseDups` | needs `DecidableEq` |
| `dedupe` | dedup consecutive | `List.eraseReps` | |
| `sort` | ascending | `List.mergeSort` | needs a **Bool** comparator (`Nat.ble`/`<T>.ble`) |
| `sort-by` | by key | `List.mergeSort` with key comparator | key type from keyfn codomain |
| `keys` / `vals` | Map projections | `List.map fst/snd (Map.entries m)` | over a `group-by` result |
| `frequencies` | count map | foldl + AList put-bump | extrinsic AList |
| `->map` | Map → Clojure map | `Map.entries` → identity (runtime Map IS a hash-map) | |
| `aempty` / `aput` / `aget` | extrinsic assoc-list map | `AList.empty`/`put`/`get` → `{}`/`assoc`/`get` | `aget` is 3-arg with default |

### Records (`:core`) — over `def-record` / malli `:map` schemas

| verb | meaning | lowers to | gotchas |
|---|---|---|---|
| `assoc` | set field(s) | `<T>.mk` with field replaced (overwrite-eliminated) | over a `Value`, `vput` chain |
| `update` | apply fn at field | `<T>.mk` with `f` applied | refined fields **re-prove** their refinement |
| `get-in` / `assoc-in` / `update-in` | nested path | nested proj / `<T>.mk` rebuild | path is a literal vector |
| `select-keys` | project | a **synthesized** record `<T>__a_b` | builds a new defrecord |

### EDN / `Value` (`:edn`) — dynamic data

| verb | meaning | lowers to | gotchas |
|---|---|---|---|
| `get` | `Value` access | `vget (Value.vkw k) v` → get | records fall back to keyword projection |
| `int?` (+ `string?` `boolean?` `keyword?` `nil?` `map?` `vector?` `set?` `double?` `float?` `some?` `any?`) | type predicate | `vint?`/`vstr?`/… | **`Value` receivers only** (named error otherwise) |

### Streaming (`:streams`) — needs `(w/install-streaming!)`

`map`/`take`/`range`/`reductions` are the *same verbs*, routed by the source type. The
stream-specific dispatch:

| routed verb | meaning | lowers to | gotchas |
|---|---|---|---|
| `map` over `Strm`/`LSeq` | productive stream map | `Strm.smap` / `LSeq.smap` → compose / lazy map | one-in-one-out; stays a stream |
| `take` over `Strm` | the **window** (Strm→List) | `Strm.take` / `Stream.unfoldTake` | the only way to make an infinite source finite |
| `reductions` over `Strm` | running scan | `Strm.scan` | |
| `range` (0-arg) | infinite source | `Strm.range` | typed `Strm Nat`, not `List Nat` |

---

## Type annotations

| form | where | example |
|---|---|---|
| `:- T` on a binder | element-typed args | `[xs :- (List Nat)]`, `(fn [x :- Nat] …)` |
| return type after the arg vector | `a/defn` | `(a/defn f [xs :- (List Nat)] Nat …)` |
| `m/=>` malli signature | record streams (registered by name) | `(m/=> rev [:=> [:cat [:sequential [:map [:cid :int]]]] :int])` |
| `(w/induce-types! #'f [sample…])` | let the data infer the schema | runs `f` on the sample, registers a malli `:=>` |

`induce-types!` returns the inferred malli schema and registers it under the fn name; a
relational body that uses `join` is registered with an explicit `:ret` (e.g.
`(w/induce-types! 'rev-by-region [sc so] :ret :int)`). Declaring `[:int {:min 0 :max …}]`
ranges sharpens the planner's selectivity estimates (which physical strategy it picks).

---

## Idioms / recipes

Each block is a real verified `a/defn`; `;;=>` lines are REPL output (from TUTORIAL).

**Fused element pipeline** — three passes prove down to one `foldl`:

```clojure
(a/defn big-squares [xs :- (List Nat)] Nat
  (reduce + 0 (map (fn [x] (* x x)) (filter (fn [x] (< 10 x)) xs))))
(big-squares [3 5 12 7 20 1])             ;;=> 544
(:stages-after (w/explain 'big-squares))  ;;=> [foldl]
```

**Group-by over a join** — `install-laws!` makes the join vanish (scatter, O(c+o)):

```clojure
(a/defn rev-by-region [custs orders]
  (map (fn [g] (reduce + 0 (map (fn [[c o]] (:amount o)) g)))
       (vals (group-by (fn [[c o]] (:region c))
                       (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders)))))
;; plan: join stage is GONE — laws :groupby-reduce-join, :hoist-index
```

**Windowed aggregate** — `partition-all` + `map` of a `reduce`:

```clojure
(a/defn win-sum [xs :- (List Nat)] (List Nat)
  (map (fn [w] (reduce + 0 w)) (partition-all 3 xs)))
(win-sum [1 2 3 4 5 6 7 8 9 10])          ;;=> (6 15 24 10)
```

**Monoid → parallel fold** — `reduce +`/`apply +` earns the associativity proof = the
parallelization certificate:

```clojure
(a/defn total [xs :- (List Nat)] Nat (apply + xs))
(total [3 1 4 1 5 9])                     ;;=> 23
```

**Two-input** — `zip` two lists into a dot product:

```clojure
(a/defn dot [as :- (List Nat) bs :- (List Nat)] Nat
  (reduce + 0 (map (fn [p] (* (first p) (second p))) (zip as bs))))
((dot [1 2 3 4]) [10 20 30 40])           ;;=> 300
```

**Incremental view** — the same `a/defn`, differentiated (DBSP Z-set deltas):

```clojure
(let [r (w/run (a/env) 'prem-rev :mode :incremental)]
  (vec ((:run r) deltas)))                ;;=> [0 100 100 130 30]  (incl. a retraction)
```

**JIT measure** — profile selectivity on a sample, re-plan, re-certify:

```clojure
(:profile   (w/optimize-measured 'big-orders [low]))   ;;=> {"…" 0.01}
(:verified? (w/optimize-measured 'big-orders [low]))   ;;=> true
```

**Windowed incremental** — `dbsp/ivm` maintains `f` over window-batches, monoid-combined:

```clojure
(require '[wandler.exec.dbsp :as dbsp])
(dbsp/ivm big-spend + 0 [[120 50 200] [30 150] [300 99] [101]])  ;;=> 871
```

**Infinite source** — `(range)` is a `Strm`; `take` is the window:

```clojure
(a/defn first5-doubled [] (List Nat)
  (take 5 (map (fn [x :- Nat] (* x 2)) (range))))
@first5-doubled                           ;;=> [0 2 4 6 8]
```

---

## Honest limits

These are **clean rejections** — transparent elaboration errors, never a silent miscompile.
That the edge is explicit is the point.

| you wrote | what happens | why / do instead |
|---|---|---|
| `keep` | `Unknown: keep` (unregistered) | Clojurians use it with a nil-punning predicate (*produce* an Option via nil); the Option layer *consumes* Option by narrowing, not produces. Use `filter` + `map`. |
| a let-bound / symbol transducer in `into`/`transduce` | `Unsupported transducer:` | the xform is parsed **syntactically**; it must be an inline `(comp (map f) (filter p) …)` literal, not a value bound elsewhere |
| `(into #{} …)` / non-vector target | `Only (into [] xform? coll) is supported` | vector target only |
| `(remove p)` in a transducer with a named pred | `remove currently requires an inline (fn [x] …) predicate` | inline the predicate |
| `apply min` | unsupported | `min` has no `Nat` identity (no `⊤`); spell `(reduce min m0 xs)` with an explicit seed |
| `(nth coll i)` (2-arg) | unsupported | use the 3-arg `(nth coll i default)` — the 2-arg form needs a bounds proof |
| `mod`/division on `Int` | unsupported | `Nat` only for now (the `emod` story is unbuilt) |
| `(reduce f init (range))` / `filter` over a raw `Strm` | **productivity gate**: `not productive — window it first` | `(take n …)` the stream to a `List`, or incrementalize via `wandler.exec.dbsp` (STREAMING.md) |
| `int?` etc. on a non-`Value` | named error | type predicates are `Value`-only receivers |

**Not wandler verbs at all.** Anything outside `(w/vocabulary)`: arbitrary `clojure.core`
(`partition-by`, `split-with`, `juxt`, `iterate`, `cycle`, transients, atoms, side effects,
`println`), lazy infinite folds, host interop. They're not silently miscompiled — the elaborator
reports `Unknown: <sym>`. The vocabulary grows deliberately; check it live, don't assume.

The streaming linearity boundary (when an incremental view stops equaling the batch recompute —
e.g. a fixed-width tumbling window *re-blocks* across batch boundaries, a genuinely different
query) is real and documented; see STREAMING.md and TUTORIAL §5 "The honest boundary".

---

## The inspection API

| call | what it gives you |
|---|---|
| `(w/vocabulary)` | the full verb table as data (the live source of truth) |
| `(w/explain 'f)` | optimizer report: `:verified?` `:changed?` `:rewrites` `:stages-before/after` `:passes-*` |
| `(w/plan 'f [samples])` | datahike-explain-style plan map; with samples also `:n-in/:n-out/:selectivity/:runtime-ms` |
| `(w/plan-str 'f [samples])` | the plan rendered as a human-readable string |
| `(w/run env 'f :mode m)` | execute in a mode: `:batch` (fused, default) · `:incremental` (Z-set pull view) · `:async` (push graph) |
| `(w/optimize-measured 'f [sample])` | the verified JIT: measure filter selectivity, re-plan, re-certify; `:profile` + `:verified?` (`:compare?` adds `:static`) |
| `(w/induce-types! #'f [sample…])` | infer + register a malli schema from data |
| `(dbsp/ivm f combine init windows)` | windowed incremental driver; maintains `f` per window-batch, monoid-combined |

---

## Where to go next

- **[TUTORIAL.md](TUTORIAL.md)** — the gradual ladder: no types → inferred → explicit, every
  example validated end-to-end.
- **[ARCHITECTURE.md](ARCHITECTURE.md)** — the engine: elaborate → optimize → lower, the cost
  model, the physical planner, the mode lattice, the streaming linearity conditions.
- **[OPTIMIZER.md](OPTIMIZER.md)** — the proven law DAG: fusion, join factorization, filter
  pushdown, reorder, semijoin.
- **[STREAMING.md](STREAMING.md)** — the ∂ pass, Z-sets, incremental/async modes, and
  exactly where incremental maintenance stops being exact.
- **[JIT.md](JIT.md)** — `optimize-measured` + the hot-swap: profile steers, kernel guarantees.
- **[PROGRAMMING_MODEL.md](PROGRAMMING_MODEL.md)** — the formalization: the malli→type functor,
  dependent types, the semiring view of aggregation/inference, the gradual ladder.
- **[BENCHMARKS.md](BENCHMARKS.md)** — what the verification actually buys, measured.
- **README** — the one-screen overview and the trust ledger.
