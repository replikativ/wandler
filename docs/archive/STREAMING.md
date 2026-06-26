# Streaming & modes

Wandler treats a streaming pipeline as the **same logical query** as a batch one —
only the *execution mode* changes, and the mode is chosen by the type of the source.
This doc covers windowing and sampling (which the surface verbs now express), the
batch / async / DBSP-incremental mode lattice, and the one boundary that genuinely
can't be incrementalized.

## Tumbling windows and downsampling

`partition-all` is a tumbling window; `take-nth` is a downsampler. Both are verified,
both fuse, and — the part that took real work — both **compose under an outer
aggregation**:

```clojure
;; per-window peak load over a metrics stream (tumbling window of 5).
;; the `:- (List Nat)` signature is required — without it the element type is
;; unconstrained and elaboration leaves unsolved metavariables.
(a/defn window-peaks [xs :- (List Nat)] (List Nat)
  (map (fn [w] (reduce max 0 w)) (partition-all 5 xs)))

(window-peaks [3 1 4 1 5  9 2 6 5 3  5])   ;; => (5 9 5)
(w/explain 'window-peaks)                   ;; :verified? true
```

A four-stage stream pipeline — **downsample → window → per-window sum → peak** — all
in one certified function:

```clojure
(a/defn peak-load [xs :- (List Nat)] Nat
  (reduce max 0
    (map (fn [w] (reduce + 0 w))
      (partition-all 4 (take-nth 2 xs)))))
;; downsample by 2, window into 4, sum each window, report the peak window load
;; — kernel-certified, matches the brute-force recompute
```

The plan reads sensibly (`window-peaks`: 4 passes → 3, "confluent fusion,
kernel-certified"). Note one engine detail that makes this work: `map∘map` fusion can
leave inner ops (`reverse`, `Nat.max`) **point-free**, and their runtime lowerings
eta-saturate to handle that — see [ARCHITECTURE.md](ARCHITECTURE.md#codegen-and-the-runtime).

## The mode lattice

The *same* query routes to a different physical strategy depending on the **source
type**. `wandler.exec.mode/route-surface` reads the source's kernel type and picks:

| Source type | Mode | Route |
|-------------|------|-------|
| `List α` | batch | `:batch-fuse` |
| `Zset α` (a Z-set of changes) | differential | `:incremental` |
| `Strm (Zset α)` (a stream of changes) | async + differential | `:async-incremental` |

The modes form a join-semilattice under `lub`: `batch` is the bottom (absorbed), and
any streaming source pulls the whole pipeline up. So a **static dimension table joined
against a fact stream** routes by the stream:

```
lub(batch, async)        ⇒ :reactive
lub(async, diff)         ⇒ :async-incremental
lub(batch, async, diff)  ⇒ :async-incremental
```

The `∂` (differentiate) pass lowers a plan to its incremental form and emits a
**certificate** citing the kernel law that licenses each stage's incrementalization:

```
mode: {:diff false …} ⟶[∂]⟶ {:diff true, :sched :async}   route: async-incremental
  join    ★ Zproduct_product_rule + Strm.joinCount2_step
  filter  ★ Mode.diff_async_dist   (obligation: linearity witness)
  sum     ★ Mode.diff_async_dist
```

## DBSP — incremental view maintenance

For a *linear* (or *bilinear*) query, `wandler.exec.dbsp/ivm` maintains the view over
a stream of delta batches and the result **equals the batch recompute** at every step.

- **Linear** (filter, sum, count): the increment is the operator on the delta. `ivm`
  folds the per-batch result with a monoid combine.
- **Bilinear** (join): the certified product rule — `count(join (xs⊎dxs)(ys⊎dys))` is
  the four-term cross product, and only the three terms touching the deltas are
  computed (semi-naive). Deletions are free (negative Z-set weights), so a chargeback
  or an un-follow just retracts.

```clojure
;; a verified per-window aggregate, driven incrementally by DBSP
(a/defn win-agg [w :- (List Nat)] Nat (reduce + 0 w))

(require '[wandler.exec.dbsp :as dbsp])
(def windows [[120 50 200] [30 150] [300 99] [101 200 50]])

(dbsp/ivm win-agg max 0 windows)   ;; => 399  (running PEAK window load)
(dbsp/ivm win-agg +   0 windows)   ;; => 1300 (running TOTAL load)
;; both == the batch recompute
```

This is the natural streaming framing: **each arriving delta is a window**, the
per-window aggregate is a kernel-certified `a/defn`, and the cross-window combine is
any associative monoid (`max`, `+`, …). It works even when the per-window logic is
*non-linear* (the `max`-within-window peak), because each window is processed
independently per batch.

### The linearity boundary (the honest part)

Per-batch windows incrementalize; a **fixed-position tumbling window over the flat
concatenated stream** does not:

```clojure
(def deltas [[10 20] [30 40 50] [60] [70 80 90 100]])  ;; varying sizes

(dbsp/ivm win-agg max 0 deltas)                                 ;; => 340  (each delta = a window)
(reduce max 0 (map win-agg (partition-all 3 (apply concat deltas)))) ;; => 240  (fixed width-3 windows)
;; 340 ≠ 240
```

`partition-all w` over a concatenation *reblocks across batch boundaries*, so it is
not linear — adding a delta can change the trailing partial window and shift
everything. The simple linear `ivm` cannot maintain it; this is a property of DBSP
itself (such windows need dedicated `I`/`D` window operators), **not a wandler
limitation**. The *batch* version computes it correctly and is certified; the
incremental version requires the per-batch reframing above. In short: the windowing
verbs land on the **right** side of the linearity boundary for streaming.

## Cross-engine: one query, many backends

Because a query is a certified term, it can be *lifted* across engines behind one
logical spec. A batch dimension built in datahike can be joined against a fact stream;
a per-step result can be re-embedded coinductively. The mode `lub` composes a
batch-built table with an async fact stream into one certified `:async-incremental`
pipeline — see [the cross-engine capstone](INFERENCE.md#5--the-cross-engine-capstone-tutorial-rung-7).

There is also a **verified hot-swap JIT** (`wandler.jit`): profiling *steers* (it
samples cardinalities and re-plans), but the kernel *guarantees* — every JIT plan is
proved `≡` the original, so swapping the running function is a `reset!`, never a
deopt. The `∂` pass commutes with the optimizer, so a JIT-compiled stream re-embeds
its optimized per-step term coinductively.

## See also

- [SURFACE.md](SURFACE.md) — the windowing/sampling verbs.
- [PROGRAMMING_MODEL.md](PROGRAMMING_MODEL.md#13--structure-2-differentiation--incremental-view-maintenance) — the differential structure (DBSP) as one of the four.
- [Tutorial Rung 5](TUTORIAL.md) — one pipeline, three execution modes.
