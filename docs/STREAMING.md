# Streaming — incremental views over change deltas (DBSP)

A wandler pipeline is one logical object; running it incrementally is a *lowering* of that
object, not a separate program you write. The mechanism is DBSP: relations are **Z-sets**,
changes are **deltas**, and the incremental view is the **derivative** of the batch query —
maintained without recomputing, and certified equal to the batch recompute at every step. This
doc is the mechanism: the carrier, the operator algebra, how `w/run` reaches it, and the exact
boundary where incremental maintenance stops being possible.

It lives in `wandler.exec.*` — primarily `zset.clj` (the algebra), `mode.clj` (the lowering),
`dbsp.clj` (the windowed driver), and `live.clj` (the async push graph).

## The carrier: a Z-set

A relation is not a set — it's a map `element → signed weight` (`wandler.exec.zset`). Weight
`+1` means "present once", `+2` "present twice", and **`-1` a retraction**. Addition `⊞`
(`z-add`) is pointwise weight-sum, dropping zeros — an abelian group.

```clojure
(z-add {:a 1 :b 2} {:a -1 :c 1})   ;=> {:b 2, :c 1}     ; the :a insert and :a delete cancel
```

That one choice is why deletions are free: a delete is a negative weight flowing through the
*same* algebra as an insert. There is no special "retract" code path — `z-filter`, `z-map`,
`z-join` all just carry the sign.

## Incremental = differential

You hold a materialized view `V` of a query over relations `L`, `R`. A change arrives as a
**delta** `[δL δR]` — Z-sets of weighted changes. The goal: update `V` touching only the
deltas, never recomputing from the full `L`, `R`. Whether you can depends on the operator.

### Linear operators — the increment is the operator on the delta

`z-filter`, `z-map`, and `z-sum` satisfy `op(a ⊞ b) = op(a) ⊞ op(b)`. So their increment is
*just the operator applied to the delta* — DBSP Theorem 5.4. `filter`/`map` preserve weights;
`sum` is `Σ weight·(f e)`, a group homomorphism (so its increment is exact).

```clojure
(z-filter even? {1 1, 2 1, 3 1})   ;=> {2 1}
(z-sum identity {2 1, 4 1})        ;=> 6
```

> **✓ proven.** A linear operator's increment law is what makes it safe to apply to the delta
> alone. Each such stage in a compiled view carries that law in its certificate chain.

### The join is bilinear — the product rule

This is the heart of incremental maintenance (`join-step`). The change to a join is **three
cross-terms**:

```
Δ(L ⋈ R) = δL ⋈ R  ⊞  L ⋈ δR  ⊞  δL ⋈ δR
```

```clojure
(defn join-step [kf lf [L R V] [dL dR]]
  (let [dV (reduce z-add [(z-join kf lf dL R) (z-join kf lf L dR) (z-join kf lf dL dR)])]
    [(z-add L dL) (z-add R dR) (z-add V dV)]))
```

**Only the cross-terms touch the deltas** → O(|δ|·|other| + |δ|²) per step, never the
O(|L|·|R|) full recompute. And the kernel theorem `Zproduct_product_rule` proves those three
terms equal `(L ⊞ δL) ⋈ (R ⊞ δR)`.

> **✓ proven.** `incremental-join` is sound *by construction*: the differential it computes is
> proved equal to the from-scratch join (`batch-join` is the spec it's differential-tested
> against). Insertions and retractions on either side are the same algebra; a deletion is just a
> negative-weight cross-term.

## The query interpreter

`zset/query` turns a pipeline into a runnable incremental view. A query is a **stage vector**:

```clojure
[[:join kf lf] [:filter pred] [:map f] [:sum f]]
```

The base is either a **join** (drive `incremental-join`, fed `[δL δR]` pairs) or a **single
source** (no `:join` — the running integral `∫Δ`, i.e. `reductions z-add`, *is* the view).
Then the linear post-ops `map` over the stream of running views. `zset/explain` prints the
certificate chain — which law makes each stage sound:

```
join :cid=:id ⟶ BILINEAR differential (Zproduct_product_rule): Δview = δL⋈R ⊞ L⋈δR ⊞ δL⋈δR
filter        ⟶ LINEAR (DBSP Thm 5.4)
sum           ⟶ group HOMOMORPHISM
```

> **✓ proven, ⚠ honest failure.** An un-linearizable op that survives into a differential plan
> (a `group-by`/`flat-map` that wasn't factored away) makes `query` **throw with the op name** —
> it never silently mis-maintains a view it can't maintain.

## How `w/run` reaches it

The source *type* picks the mode (`wandler.exec.mode`):

| source type | mode | route |
|---|---|---|
| `List A` | batch | `:batch-fuse` |
| `Zset A` | differential | `:incremental` |
| `Strm (Zset A)` | differential + async | `:async-incremental` |

`lub` composes modes when sub-pipelines disagree (e.g. a static batch dimension joined to an
async fact stream lubs to `:async-incremental`). The **∂ pass** (`differentiate`) lowers the
certified *relational skeleton* into the stage vector above; `auto-impls` codegens the leaf fns
from their kernel terms; `to-zset-query` builds the runner.

One subtlety that is load-bearing: `w/run :incremental`/`:async` differentiate the **naive**
(un-fused) pipeline term, not the optimizer's fused one. The ∂ pass reads canonical
`join / filter / map / sum` stages; the optimizer's fused `filterMap` or factorized `group_by`
aren't those, so differentiating the *optimized* term would not lower. `:batch` keeps the fused
term. `naive ≡ optimized` is kernel-certified, so the route never changes the trust story.

Driving a verified pipeline incrementally, from `docs/TUTORIAL.md` §5:

```clojure
(def deltas
  [[{{:cid 1 :premium 1} 1, {:cid 2 :premium 0} 1} {}]  ; load two customers
   [{} {{:cid 1 :amount 100} 1}]                         ; premium order
   [{} {{:cid 2 :amount 50}  1}]                         ; basic order — filtered out
   [{} {{:cid 1 :amount 30}  1}]
   [{} {{:cid 1 :amount 100} -1}]])                      ; RETRACTION

(let [r (w/run (a/env) 'prem-rev :mode :incremental)]
  (vec ((:run r) deltas)))
;;=> [0 100 100 130 30]      ; == batch recompute at every step, retraction-safe
```

### The async push graph

`:async` lowers to a push-driven dataflow graph (`exec/live`): each stage is a node holding its
running view in a watchable `:out` atom; `(:push! r)` drives a delta in, and each edge
propagates the *output delta* (`new ⊞ negate(old)`) to the next node. Same trajectory as the
pull view, reached event-by-event:

```clojure
(let [r (w/run (a/env) 'prem-rev :mode :async), traj (atom [])]
  (doseq [d deltas] ((:push! r) d) (swap! traj conj @(:out r)))
  @traj)
;;=> [0 100 100 130 30]
```

> **✓ proven, ⚠ one trusted edge.** Every ∂ stage cites a kernel law, so the view is certified
> equal to the batch one. The **clock** — when async deltas actually arrive — is the trusted,
> real-world part; the algebra computed at each tick is proven. (When two sub-streams run at
> different rates, `lub` flags a `::resample` seam — an explicit, certified-safe rate bridge,
> the Rhine insight made concrete.)

## Windowed maintenance: `dbsp/ivm`

For windowed aggregation there is a direct driver. `(dbsp/ivm f combine init windows)` maintains
`f` over a stream of window-batches, combining per-window results with a monoid — so it works
even for a **non-linear** per-window `f`, because each window is its own batch:

```clojure
(dbsp/ivm big-spend + 0 [[120 50 200] [30 150] [300 99] [101]])   ;=> 871   (== batch)

(dbsp/ivm win-load max 0 [[120 50 200] [30 150] [300 99] [101 200 50]])  ;=> 399  (peak window)
(dbsp/ivm win-load +   0 [[120 50 200] [30 150] [300 99] [101 200 50]])  ;=> 1300 (grand total)
```

## The linearity boundary (the honest edge)

Incremental maintenance is exact for the *query you incrementalized* — and not for a different
one that happens to look similar. **Per-batch** windows (each arriving delta *is* a window) are
maintainable. A **fixed-position** tumbling window over the flattened stream is **not** linear:
it reblocks across batch boundaries, so the two answers genuinely differ.

```clojure
(def batches [[10 20] [30 40 50] [60] [70 80 90 100]])

(dbsp/ivm win-load max 0 batches)                                          ;=> 340  (per batch)
(reduce max 0 (map #(reduce + 0 %) (partition-all 3 (flatten batches))))   ;=> 240  (fixed width 3)
```

`340 ≠ 240` is correct, not a bug — re-windowing the concatenation is a different query. A DBSP
view maintains its own query, and `zset/query` refuses to pretend otherwise (it throws on an op
it can't linearize). Knowing where exact maintenance stops is part of using it well.

## Where to go next

- **TUTORIAL.md** §5 — streaming from the user's side, runnable.
- **JIT.md** — how a long-running incremental view re-plans and hot-swaps under changing load.
- **OPTIMIZER.md** — the factorization that turns a `group_by`-over-join into a linearizable
  scatter (so it *can* be maintained).
- **ARCHITECTURE.md** — where the mode dispatch sits in the whole pipeline.
