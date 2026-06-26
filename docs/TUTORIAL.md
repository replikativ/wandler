# Wandler — Tutorial

You write ordinary Clojure data pipelines. Wandler **elaborates** them to terms in a
dependently-typed kernel (the same CIC kernel that checks Lean 4 / Mathlib),
**optimizes** them by rewriting — where *every* rewrite it keeps carries a machine-checked
proof that the optimized pipeline is equal to the one you wrote — and **lowers** them to
fast Clojure.

The slogan: **verification licenses the fast representation.** Because the kernel has
proved your fused pipeline equals the obvious one, wandler is free to run the fused one
(single pass, unboxed arrays, a parallel fork-join fold, an incremental view) and you still
get the answer you'd get from the naive code.

This tutorial walks up a **gradual ladder**: start from a plain Clojure function with no
types, let the data infer a type, then take control with explicit types — and watch the
guarantees and the optimizations switch on rung by rung. Then we tour the features that ride
on a typed pipeline: the verb surface, incremental streaming, infinite sources, and a verified
JIT. Every code block below was executed; the `;;=>` lines are the real REPL output.

> **A reading note on the boxes.** A **✓ proven** box marks something the kernel guarantees; a
> **⚠ trusted** box marks a boundary wandler does *not* prove (a foreign engine, a measured
> statistic, a floating-point weight). Keeping the two visibly separate is the whole point —
> see the [trust ledger](#the-trust-ledger) at the end.

Contents:
- [0. Setup](#0-setup)
- [1. No types — plain Clojure](#1-no-types--plain-clojure)
- [2. Inferred types — let the data type it](#2-inferred-types--let-the-data-type-it)
- [3. Explicit types — and the join disappears](#3-explicit-types--and-the-join-disappears)
- [4. The verb surface](#4-the-verb-surface)
- [5. Streaming and modes](#5-streaming-and-modes)
- [6. Beyond batch: infinite streams and a verified JIT](#6-beyond-batch-infinite-streams-and-a-verified-jit)
- [The trust ledger](#the-trust-ledger)

---

## 0. Setup

Wandler runs on the `ansatz` kernel and a snapshot of the Lean **Init** library (the base
types: `Nat`, `List`, `Prod`, `Bool`, …). Load the env, then fill wandler's seams.

```clojure
(require '[ansatz.core :as a]
         '[wandler.core :as w]
         '[malli.core :as m])           ; optional: record schemas

(a/init! "test-data/init-store" "init")  ; the Lean Init env (lazy PSS store, ~40ms)

(w/install!)            ; batch + relational surface (verbs, optimizer, runtime)
(w/install-streaming!)  ; the incremental / async / Strm (coinductive) modes
(w/install-laws!)       ; the proven FAQ optimization-law DAG  (cached per-process)
```

Three installs, three layers, each with one job:

| call | gives you | needed for |
|---|---|---|
| `w/install!` | `a/defn` pipelines, fusion, `explain`/`plan` | §1–§4 |
| `w/install-streaming!` | `w/run` incremental/async, `Strm` surface | §5, §6 |
| `w/install-laws!` | join factorization, filter pushdown, reorder | §3 |

`install-laws!` proves a library of relational theorems once; it's cached per process, so a
second call (or a fresh test env) re-checks the cached proof terms in ~20 ms instead of
re-proving.

> **One note on numbers.** Element type `Nat` is the kernel's arbitrary-precision natural,
> so a `Nat` result prints with an `N` suffix (`16N`, `(6N 15N …)`). It's just an integer;
> we drop the `N` in prose for readability.

---

## 1. No types — plain Clojure

Here's a pipeline you've written a hundred times: total the order amounts.

```clojure
(defn order-total [os]
  (reduce + 0 (map :amount os)))

(order-total [{:amount 5} {:amount 9} {:amount 2}])
;;=> 16
```

It runs. That's all it does — it's a plain Clojure function, and wandler isn't involved.
There's no proof that any rewrite of it is correct, and no plan, because wandler doesn't know
the *shape* of the data flowing through. Two passes over the list (one `map`, one `reduce`),
boxed numbers, no parallelism, no guarantees.

The question this tutorial answers: **what would it take to make this same code verified *and*
fast — without rewriting it?** The answer is one thing: a type. The rest of the ladder is just
*how* the type arrives.

---

## 2. Inferred types — let the data type it

You don't have to write the type. Show wandler a representative **sample** of the inputs and it
reads the schema off the data:

```clojure
(w/induce-types! #'order-total [[{:amount 5} {:amount 9}]])
;;=> [:=> [:cat [:sequential [:map [:amount :int]]]] :int]
```

It looked at the sample (`order-total` takes a sequence of `{:amount int}` maps), ran the
function on it to learn the return type (`:int`), and **registered** that malli function schema
under the name `order-total`. Now re-state the *same body* as an `a/defn` — wandler picks up
the registered types automatically:

```clojure
(a/defn order-total [os]
  (reduce + 0 (map (fn [o] (:amount o)) os)))

(order-total [{:amount 5} {:amount 9} {:amount 2}])
;;=> 16          ; same answer…
```

…but everything changed underneath. Ask wandler how it compiled it:

```clojure
(println (w/plan-str 'order-total))
;;=> plan order-total
;;     naive:  foldl → map   (2 passes)
;;     fused:  foldl          (1 passes)
;;     laws:   confluent fusion
;;     proof:  optimized ≡ naive (kernel-certified)

(w/explain 'order-total)
;;=> {:verified? true, :changed? true, :rewrites [],
;;    :stages-before [foldl map], :stages-after [foldl], :passes-before 2, :passes-after 1}
```

The two passes fused into one — the classic transducer fusion — except wandler didn't trust a
rewrite rule, it **proved** the one-pass `foldl` computes the same function as the
`map`-then-`reduce` version, and the kernel checked that proof.

> **✓ proven.** `:verified? true` means a kernel proof object `fused ≡ naive` type-checked.
> That is the entire trust story: the runtime executes the one-pass version *because* the
> two-pass version was proved equal to it. If a rewrite can't be proved, it's dropped and the
> naive plan runs — wandler never ships an unproven optimization.

Same code as rung 0. One sample of data later, it's verified and fused. That's the on-ramp:
**you never wrote a type, and you got a proof and a plan.**

---

## 3. Explicit types — and the join disappears

Inference is the easy way in; writing the type yourself is the way to *control* it — and to
unlock the optimizations that need a relational shape. For a simple element type, annotate the
binder with `:-`; for records, write a malli `m/=>`.

The `:-` form, on a fuse-everything pipeline (filter the big numbers, square them, sum them):

```clojure
(a/defn big-squares [xs :- (List Nat)] Nat
  (reduce + 0 (map (fn [x] (* x x))
                   (filter (fn [x] (< 10 x)) xs))))

(big-squares [3 5 12 7 20 1])
;;=> 544                                  ; 12² + 20²
(:stages-after (w/explain 'big-squares))  ;;=> [foldl]   ; three passes → one
```

Now the payoff that types really buy. Describe two record streams with malli and write the
obvious query — per-region revenue over a customers-⋈-orders join:

```clojure
(m/=> rev-by-region
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]
             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]]
   [:sequential :int]])

(a/defn rev-by-region [custs orders]
  (map (fn [g] (reduce + 0 (map (fn [[c o]] (:amount o)) g)))
       (vals (group-by (fn [[c o]] (:region c))
                       (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders)))))

(println (w/plan-str 'rev-by-region))
;;=> plan rev-by-region
;;     naive:  map → foldl → map → map → group_by → join   (6 passes)
;;     fused:  map → foldl → foldl → group_by              (4 passes)
;;     laws:   :groupby-reduce-join, :hoist-index
;;     proof:  optimized ≡ naive (kernel-certified)
```

The `join` stage is **gone**. Instead of building every customer-order pair and then grouping
them (O(customers × orders)), the proved `:groupby-reduce-join` law turns the whole thing into
a **scatter** — fold each side into the region buckets directly, O(customers + orders). On 40
customers / 600 orders it agrees with the brute-force semantics exactly:

```clojure
(rev-by-region custs orders)
;;=> [837 840 843 833 836]      ; == the for/group-by/sum reference, every region
```

> **✓ proven.** `:groupby-reduce-join` is a theorem with the same standing as a Mathlib lemma:
> the kernel checked that the scatter computes the same map as group-by-over-the-join. The
> asymptotic win is *free* in the sense that matters — you didn't write the index-build, and
> you can't have gotten it subtly wrong, because it's the same function by proof.

This composes: filter the orders before the join and the planner pushes the filter down *and*
factorizes; project through **nested** record fields (`(:region (:geo c))`) and it still fires;
a genuine three-way join eliminates **both** joins:

```clojure
(a/defn spend3 [custs orders prices]
  (reduce + 0 (map (fn [cop] (:price (second cop)))
                   (join (fn [co] (:pid (second co))) (fn [p] (:pid p))
                         (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders)
                         prices))))

(w/explain 'spend3)
;;=> {:verified? true, :rewrites [:fold-factor :hoist-index],
;;    :stages-before [foldl map join join],
;;    :stages-after  [foldl foldl foldl group_by group_by], ...}
```

(The *pass count* can go **up** while the *cost* goes down — a pass count is not the cost
model; eliminating the quadratic join is.)

> **Inference reaches here too.** You can drive the factorization straight from a data sample:
> `(w/induce-types! 'rev-by-region [sample-custs sample-orders] :ret :int)` (a relational body
> that uses `join` is registered by name with an explicit `:ret`), then the same `a/defn` comes
> back `:verified? true` and factorized just the same. The reason to write the schema explicitly
> is **control** — declaring `[:int {:min 0 :max …}]` ranges sharpens the
> planner's selectivity estimates, which steer the physical strategy (pre-aggregated index,
> grace-hash spill, drive-direction reorder). The type → plan story is ALGEBRA.md.

---

## 4. The verb surface

Wandler understands a fixed, growing vocabulary of `clojure.core` collection verbs. Inside it
they compose freely; at its edge it's explicit (a verb it doesn't know is a clean rejection,
not a silent miscompile). A quick tour, each a real verified `a/defn` over `(List Nat)`.

**Comprehensions** — `for` is intercepted before Clojure's macro and lowered to
`map`/`filter`/`mapcat`/`let`:

```clojure
(a/defn pairs-sum [xs :- (List Nat)] Nat
  (reduce + 0 (for [x xs y xs] (* x y))))      ; cartesian product → Σ xy
(pairs-sum [1 2 3 4])                           ;;=> 100   ; (1+2+3+4)²

(a/defn odds-for [xs :- (List Nat)] (List Nat)
  (for [x xs :when (odd? x)] (* x 10)))
(odds-for [1 2 3 4 5])                          ;;=> (10 30 50)
```

A two-source `for` with `:when (= a b)` becomes a real relational join — which the §3 planner
can then factorize.

**Windows and sampling** — `partition-all` (tumbling window) and `take-nth` (downsample)
compose with the aggregation verbs, so per-window analytics is a `map` of a `reduce`:

```clojure
(a/defn win-sum [xs :- (List Nat)] (List Nat)
  (map (fn [w] (reduce + 0 w)) (partition-all 3 xs)))
(win-sum [1 2 3 4 5 6 7 8 9 10])                ;;=> (6 15 24 10)

(a/defn peak-load [xs :- (List Nat)] Nat          ; downsample → window → Σ → peak
  (reduce max 0 (map (fn [w] (reduce + 0 w)) (partition-all 2 (take-nth 2 xs)))))
(peak-load [1 2 3 4 5 6 7 8 9 10])              ;;=> 12
```

**Two-input verbs and monoids** — `zip`/`interleave` join two inputs; `reduce`/`apply` over
`+`/`*`/`max`/`min` recognize the monoid:

```clojure
(a/defn dot [as :- (List Nat) bs :- (List Nat)] Nat
  (reduce + 0 (map (fn [p] (* (first p) (second p))) (zip as bs))))
((dot [1 2 3 4]) [10 20 30 40])                 ;;=> 300   ; dot product

(a/defn lace [as :- (List Nat) bs :- (List Nat)] (List Nat) (interleave as bs))
((lace [1 2 3]) [10 20 30])                     ;;=> (1 10 2 20 3 30)

(a/defn total [xs :- (List Nat)] Nat (apply + xs))
(total [3 1 4 1 5 9])                           ;;=> 23
```

> **Why recognizing the monoid matters.** When the optimizer proves `+`/`0` form an associative
> monoid with identity, it earns the right to lower a `reduce +` to a **parallel fork-join
> fold** — the associativity proof *is* the parallelization certificate. The same proof that
> lets it fuse lets it split the work across cores, without you asking.

The full vocabulary (and the clean-rejection edge cases, like `keep`) is `(w/vocabulary)` and
REFERENCE.md.

---

## 5. Streaming and modes

A verified pipeline is one logical object; *how* it executes is a separate choice driven by the
type of its source. The same `a/defn` runs three ways, and `w/run` is the one front door:

- **`:batch`** — over `List`s: the fused, codegen'd function from §1–§4.
- **`:incremental`** — each source is a stream of **Z-set deltas** (DBSP); `w/run` returns a
  pull view you feed changes to.
- **`:async`** — a push-driven live graph.

The crucial part: wandler does **not** re-derive the incremental version by hand. It runs the
**∂ (differential) pass** over the *same certified relational skeleton*, and each stage of the
incremental view carries its own proof (a linear filter is unchanged under deltas; a join obeys
the bilinear product rule; a sum is a group homomorphism). The route never changes the trust
story.

Take premium-customer revenue — a join, a filter, a sum:

```clojure
(m/=> prem-rev
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:premium [:int {:min 0}]]]]
             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]] :int])

(a/defn prem-rev [custs orders]
  (reduce + 0 (map (fn [[c o]] (:amount o))
                   (filter (fn [[c o]] (< 0 (:premium c)))
                           (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders)))))
```

Run it **incrementally**. A delta is a pair `[Δcustomers Δorders]`; each is a Z-set — a map from
a row to a signed weight (`+1` insert, `-1` retract):

```clojure
(def deltas
  [[{{:cid 1 :premium 1} 1, {:cid 2 :premium 0} 1} {}]  ; t0: load two customers
   [{} {{:cid 1 :amount 100} 1}]                         ; t1: premium cust 1 buys 100
   [{} {{:cid 2 :amount 50}  1}]                         ; t2: basic cust 2 buys 50  (filtered)
   [{} {{:cid 1 :amount 30}  1}]                         ; t3: cust 1 buys 30
   [{} {{:cid 1 :amount 100} -1}]])                      ; t4: RETRACT cust 1's first order

(let [r (w/run (a/env) 'prem-rev :mode :incremental)]
  (vec ((:run r) deltas)))
;;=> [0 100 100 130 30]
```

Read the trajectory: `0` (no orders), `100` (premium order), `100` (the basic order is filtered
out — the view doesn't move), `130` (+30), `30` (the retraction removes the original 100). At
every step the incremental result equals what a full batch recompute would give — **including
the deletion**, which is just a negative weight flowing through the same proved algebra. The
**async** route gives the identical trajectory through a push handle:

```clojure
(let [r (w/run (a/env) 'prem-rev :mode :async), traj (atom [])]
  (doseq [d deltas] ((:push! r) d) (swap! traj conj @(:out r)))
  @traj)
;;=> [0 100 100 130 30]
```

> **✓ proven, ⚠ one trusted edge.** Each ∂ stage cites a kernel law (the join's bilinear product
> rule, the filter's linearity, the sum's homomorphism), so the incremental view is certified
> equal to the batch one. The *clock* — when async deltas arrive — is the trusted, real-world
> part; the algebra computed at each tick is proven.

### Windowed DBSP with `dbsp/ivm`

For windowed aggregation there's a direct incremental driver. `(dbsp/ivm f combine init
windows)` maintains `f` over a stream of window-batches, combining results with a monoid — and
it equals the batch recompute:

```clojure
(require '[wandler.exec.dbsp :as dbsp])

(a/defn big-spend [xs :- (List Nat)] Nat
  (reduce + 0 (filter (fn [x] (< 100 x)) xs)))

(dbsp/ivm big-spend + 0 [[120 50 200] [30 150] [300 99] [101]])
;;=> 871     ; == (big-spend (flatten windows))
```

It works even for a **non-linear** per-window function, because each window is its own batch and
the monoid combines the per-window results — peak load (`max`) and total (`+`) over the same
windows:

```clojure
(a/defn win-load [xs :- (List Nat)] Nat (reduce + 0 xs))
(def w2 [[120 50 200] [30 150] [300 99] [101 200 50]])   ; per-window sums: 370 180 399 351

(dbsp/ivm win-load max 0 w2)   ;;=> 399    (peak window)
(dbsp/ivm win-load + 0 w2)     ;;=> 1300   (grand total)
```

### The honest boundary

Incremental maintenance has a real edge, and wandler doesn't paper over it. *Per-batch* windows
— where each arriving delta **is** a window — are incrementally maintainable. A *fixed-position*
tumbling window over the flattened stream is **not** linear: it reblocks across batch
boundaries, so the two answers genuinely differ:

```clojure
(def batches [[10 20] [30 40 50] [60] [70 80 90 100]])

(dbsp/ivm win-load max 0 batches)                         ; each batch = one window
;;=> 340
(reduce max 0 (map #(reduce + 0 %) (partition-all 3 (flatten batches))))  ; fixed width 3
;;=> 240
```

`340 ≠ 240` is correct, not a bug: re-windowing the concatenation is a *different query*, and a
DBSP view maintains the query you incrementalized. Knowing exactly where incremental maintenance
stops being exact is part of using it well — the linearity conditions are in ARCHITECTURE.md.

---

## 6. Beyond batch: infinite streams and a verified JIT

### Coinductive sources

`(range)` with no argument is an **infinite** stream — typed `Strm Nat`, not `List Nat`. Wandler
routes verbs by that type: `map` stays a stream (productive — one in, one out), `take` is the
*window* that turns a `Strm` into a `List`, and `reductions` becomes a running scan. A
zero-argument `a/defn` is a value; deref it:

```clojure
(a/defn first5-doubled [] (List Nat)
  (take 5 (map (fn [x :- Nat] (* x 2)) (range))))
@first5-doubled
;;=> [0 2 4 6 8]

(a/defn running-sum [] (List Nat)
  (take 6 (reductions + 0 (range))))
@running-sum
;;=> [0 1 3 6 10 15]
```

And the **productivity gate**: an unwindowed `reduce` over an infinite stream would never
terminate, so the *type system rejects it* at elaboration with an actionable message —

```clojure
(a/defn bad-sum [] Nat (reduce + 0 (range)))
;;=> error: `reduce` over an infinite Strm is not productive — window it first
;;          with `(take n …)` (stream → List), or incrementalize it (wandler.exec.dbsp).
```

> **✓ proven (by typing).** Productivity here isn't a lint — it's the difference between
> `Strm A` and `List A` in the kernel. You can't fold an infinite source by accident; you have
> to `take` a window or incrementalize, both of which the surface knows how to do.

### A verified JIT

Wandler's plan is static, but it can also **measure** a real workload and re-plan against it —
and because every adopted rewrite is re-certified, adapting to data can never make the result
wrong. `w/optimize-measured` profiles a pipeline's filter selectivities on a sample and
re-optimizes:

```clojure
(m/=> big-orders [:=> [:cat [:sequential [:map [:rev [:int {:min 0}]]]]] :int])
(a/defn big-orders [orders]
  (reduce + 0 (map (fn [o] (:rev o)) (filter (fn [o] (< 100 (:rev o))) orders))))

(def low  (vec (for [i (range 500)] {:rev (mod (* i 7) 90)})))   ; almost nothing > 100
(def high (vec (for [i (range 500)] {:rev (+ 100 (mod i 50))}))) ; everything >= 100

(:profile   (w/optimize-measured 'big-orders [low]))   ;;=> {"…" 0.01}
(:verified? (w/optimize-measured 'big-orders [low]))   ;;=> true
(:profile   (w/optimize-measured 'big-orders [high]))  ;;=> {"…" 0.98}
```

The measured selectivity (here `0.01` vs `0.98`) feeds the cost model. On a single filter it
just confirms the plan; on a **join** it steers the drive direction — index the side the filter
shrinks — and the re-planned query comes back kernel-certified all the same. (The sample here is
a flat seq of the elements the filters see; this differs from `w/plan`, which takes whole inputs
to time the function — see the docstrings.)

> **⚠ trusted input, ✓ proven output.** The *measurement* is a statistic about your data — a
> trusted, fallible observation. What it steers is a cost decision; whatever plan it picks is
> still proved equal to the original before it runs. Bad statistics can only make the JIT choose
> a *slower* correct plan, never a wrong one. Profile steers, kernel guarantees.

---

## The trust ledger

The single idea under the whole ladder: wandler keeps a hard line between what it **proves** and
what it **trusts**, and never blurs it.

| Proven by the CIC kernel (L0) | Trusted boundary (L2) |
|---|---|
| Fusion (`fused ≡ naive`) | The clock — when async deltas arrive |
| Join factorization / filter pushdown / reorder | Measured selectivity & cardinality (the JIT's input) |
| Incremental ∂ stages (bilinear join, linear filter, sum homomorphism) | Foreign engine results (datahike / stratum / a `register-foreign!` fn) |
| Productivity (`Strm` vs `List` typing) | Floating-point probability weights |
| Monoid laws → parallel fold licence | |

Every `:verified? true`, every `optimized ≡ naive`, every ∂-stage citation is an L0 fact a
machine checked. Every L2 boundary is named and typed, so you always know which is which. An L2
input can make wandler *slower* or feed it *wrong data*; it can never make a verified pipeline
compute a different function than the code you wrote.

That's wandler: **write the obvious pipeline, give it a type — by inference or by hand — and let
the kernel earn the fast one.**

---

### Where to go next

- **REFERENCE.md** — the complete verb vocabulary, idioms, and the honest edge cases.
- **ARCHITECTURE.md** — the engine: elaborate → optimize → lower, the cost model, the physical
  planner, the mode lattice, and the streaming linearity conditions.
- **ALGEBRA.md** — the formalization: the malli → type functor, dependent types, inference as
  semiring sum-product, and the gradual-typing ladder.
- **BENCHMARKS.md** — what the verification actually buys, measured.
