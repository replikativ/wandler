# Wandler in anger — a backend Clojure cookbook

You already write `map` / `filter` / `reduce` / `group-by` / `join` over seqs of maps,
and you keep your shapes in malli. Wandler runs *that* code — verified, optimized, and
compiled — with **no new abstractions to learn and nothing to port**. Change `defn` →
`a/defn`, keep your malli `m/=>`, and call the function. This page is the set of idioms
that are known to work (each one is exercised in the test suite), the three install
levels, and an honest list of what isn't wired yet.

## The three install levels (do this first)

A surprising amount of "type mismatch" / "unsolved metavariables" confusion is just a
missing install. Pick the level you need — each is a one-liner, idempotent:

```clojure
(require '[ansatz.core :as a] '[wandler.core :as w])
(a/init! "test-data/init-store" "init")   ; the kernel env (lazy, ~40ms)

(w/install!)         ; LEVEL 1 — the batch surface: map/filter/reduce/group-by/records/transducers
(w/install-laws!)    ; LEVEL 2 — the proven relational law DAG: join factorization, semijoin, pushdown
                     ;           (needed for the FAQ / aggregation-through-join rewrites to fire)
(require '[wandler.surface.streams :as st]) (st/install!) (st/install-join!)
                     ; LEVEL 3 — the stream surface: (range)/take/scan over infinite sources
```

> If a pipeline elaborates to a cryptic type error, you are almost always one install
> level short. Batch needs L1; a certified `join`/aggregation needs L2; anything with
> `(range)` or windows needs L3.

## Schemas: `m/=>` is a **separate top-level form**

The malli schema registers at *runtime*; `a/defn` reads it at *macro-expansion*. So they
must be two separate top-level forms, schema first — exactly how you'd write them anyway:

```clojure
(m/=> total-spend
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]] :int])

(a/defn total-spend [orders]
  (reduce + 0 (map (fn [o] (:amount o)) orders)))
```

Wrapping both inside one `do` / `let` / wrapper `defn` breaks (the schema isn't registered
when `a/defn` expands). Two top-level forms is the rule.

## Records (your malli maps) — what works

A `[:map …]` arg becomes a refinement record; ordinary keyword access just works. All of
these are verified + compiled:

```clojure
(:amount o)                      ; field access
(:id (:user x))                  ; nested map access
(count (:tags x))                ; a vector-valued field
(filter (fn [x] (:active x)) xs) ; a boolean field as a predicate
(assoc o :amount (+ (:amount o) 1)) ; record UPDATE (returns a new record)
```

Field value types covered: `:int`, `:string`, `:boolean`, `[:enum …]`, `{:optional true}`,
nested `[:map …]`, and `[:sequential …]` (vector) fields.

## Aggregation idioms

```clojure
;; sum / count a column
(reduce + 0 (map :amount orders))

;; per-key aggregation — group-by returns a kernel Map, so go through `vals`:
(map (fn [g] (count g))      (vals (group-by :etype events)))   ; count per group
(map (fn [g] (reduce + 0 g)) (vals (group-by :etype events)))   ; sum per group

;; frequencies (returns a list of [value count] pairs)
(frequencies xs)

;; distinct / sort
(distinct xs)
(sort-by (fn [x] (Nat.sub 100 x)) xs)
```

> Note: `group-by` returns the kernel `Map K (List V)`, not a seq of map-entries — use
> `(vals (group-by …))` for the groups (or `keys` for the keys). The plain-Clojure
> `(map (fn [[k v]] …) (group-by …))` over entries is **not** the supported shape yet.

## Joins + the FAQ factorization (Level 2)

```clojure
(m/=> revenue
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]
             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]] :int])

(a/defn revenue [custs orders]
  (reduce + 0 (map (fn [[c o]] (* (inc (:cid c)) (:amount o)))
                   (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders))))

(w/explain 'revenue)   ; => {:verified? true, :rewrites [:fold-factor :hoist-index], …}
```

With `install-laws!` the planner factors the aggregating join — the `custs × orders`
product is never built — and the certificate proves the factored plan equals the naive
one. The *same* factorization is semiring-generic (counting / boolean / tropical /
probability); see [`INFERENCE.md`](INFERENCE.md).

## Streams (Level 3)

`Strm A := Nat → A` is an infinite source; the type traces stream-vs-list, so the verbs
route statically. `map` rides a stream (productive); `take n` is the window (→ List);
`filter`/`reduce` need a window or an increment first (the type *forces* it):

```clojure
(a/defn win-sq  [n :- Nat] (List Nat) (take n (map (fn [x] (* x x)) (range))))      ; [0 1 4 9 16]
(a/defn win-sum [n :- Nat] Nat        (reduce + 0 (take n (map (fn [x] (* x x)) (range)))))
(a/defn run-sum [n :- Nat] (List Nat) (take n (reductions + 0 (map (fn [x] (+ x 1)) (range)))))

;; filter on a raw stream is a CLEAR error, not a hang:
;; `filter` over an infinite Strm is not productive — window it first with `(take n …)`.
```

The window equals the finite List pipeline (`Strm.take_smap` certifies `take n (map f s) =
List.map f (take n s)`), so the streaming version inherits the batch proof and forces only
the window.

## Idioms that compose freely

`if`, `let`, `->>` threading, `comp`, `inc`/`+`/`*`/`<`, `member` (set membership),
`transduce` (`(transduce (comp (filter …) (map …)) + 0 xs)` fuses to one pass).

## Not wired yet (honest limits)

These are the edges you'll hit; none is a silent wrong answer (you get an error):

- **Streams source only from `(range)`** (a `Nat` source). There's no surface verb yet to
  lift *your own* lazy seq / channel / data feed into a `Strm`/`LSeq`, and **map literals
  `{:k v}` aren't a surface form**, so a stream *of event records* isn't expressible
  through the surface today. (The kernel has `LSeq A := Nat → Option A` for exactly this;
  the surface bridge is the missing piece.)
- **`group-by` over entries**: use `(vals (group-by …))`, not `(map (fn [[k v]] …) …)`.
- **`:map-of`** malli schema is unsupported as a signature type (return a `[:sequential …]`
  of pairs, or use the `vals`/`frequencies` shapes above).
- **Inference is driven by a factor-graph API**, not yet from your malli data directly —
  see [`INFERENCE.md`](INFERENCE.md) (`certify-faq`) for the certified engine and
  `wandler.inference.semiring/faq` for the pure-Clojure runtime version.
- Binder syntax: use `[x :- T]` (the metadata form `^{:- T} x` is not supported).
