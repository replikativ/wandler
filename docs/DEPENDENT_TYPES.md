# Dependent types → planner → execution

How a **malli schema** becomes a **dependent type** in the kernel, and how the
planner *reads that type to license a faster plan that the kernel then certifies*.
This is the load-bearing difference from an ordinary type checker: the type is not
merely checked and erased — it is **used to choose and prove an optimization**.

> One line: *Typed Clojure proves the absence of type errors; wandler proves the
> presence of correct behavior — and only the latter can license optimization.*
> ([`GRADUAL.md`](GRADUAL.md)). This doc is the concrete mechanism for "license."

## 1. A malli schema is a refinement (dependent) type

An ordinary malli function schema — the gradual on-ramp is *keep your malli, change
`defn` → `a/defn`* (load `ansatz.malli`):

```clojure
(require '[ansatz.core :as a] '[malli.core :as m] '[ansatz.malli])
(m/=> revenue
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]   ; Customer
             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]]  ; Order
       :int])
```

Each `[:map …]` argument schema becomes a **named-field record**, and that record
is a **subtype of the dynamic EDN `Value` universe, refined by a proof that the
value conforms to the schema**:

```
Customer  ≅  Subtype Value (λv. conforms γ_Customer v = true)
```

where `γ_Customer` is the malli schema compiled to a total `Value → Bool`
conformance predicate (kernel-verified; see `ansatz.surface.schema`). The
constraint `[:>= 0]` is not a runtime assertion that gets thrown away — it is a
**refinement carried in the type**: a `Customer` is a `Value` *together with the
proof it is a non-negative-int-keyed map*. That pairing (a value + a proof about
it) is precisely a **dependent (Σ/refinement) type**.

Consequences the planner relies on:

- **field reads are O(1) and typed.** `(:cid c)` elaborates to a `proj` node, which
  lowers to a direct `.field`/`nth` after `Subtype.val` erasure — *not* a dynamic
  `vget` map probe. The refinement is what makes the static projection sound.
- **writes re-prove the refinement.** `(assoc o :amount v)` re-establishes
  `conforms γ_Order` for the new field (or is a named error if it can't) — the
  refinement is an invariant, not a one-time check.
- **the element type is a first-class kernel object**, so the optimizer can branch
  on it.

## 2. The type drives the planner — three ways

The planner (`wandler.optimize`) reads the elaborated *type* of a pipeline to pick
a rewrite, then hands the composed proof to the kernel gate
(`cert/verified-rewrite?`). The search is untrusted; only the certificate counts.
Three places the type is load-bearing:

### (a) The element type selects the semiring **carrier**

A separable aggregate over a join — `Σ_{x⋈y} f(x)·g(y)` — factorizes through a
per-key pre-aggregated index by the **FAQ frame rule** (`Map.foldl_join_frame`).
That law is **semiring-generic**: it is proven once over an abstract carrier
`(S, ⊕, ⊗, 0̄)` and *instantiated at the carrier the pipeline's value type names*:

| value type | carrier `(S, ⊕, ⊗, 0̄)` | the query is |
|---|---|---|
| `Nat` | `(Nat, +, ·, 0)` | counting / weighted **SUM** |
| `Bool` | `(Bool, ∨, ∧, ⊥)` | boolean **provenance / reachability** (∃ a matching pair) |
| `ℕ∞` (`ENat`) | `(ℕ∞, min, +, +∞)` | **tropical** — shortest-path / Viterbi DP through the join |

The recognizer reads the carrier `S` off the fold's accumulator binder type, looks
it up in the carrier registry (`wandler.laws.semiring`, into which each carrier's
laws register their row), and emits the generic law instantiated with that
carrier's ops + the kernel proofs of its semiring axioms. Adding a semiring is one
`register!` next to its admitted laws — the optimizer itself is untouched.
*The type is the dispatch key for which proven law applies.*

### (b) The functional-dependency **scope quotient** (the dependent-types win)

When the schema makes a field **functionally determined by the join key**, a factor
reading that field can **float to a cheaper scope**. Example: the left weight
`(inc (:cid c))` reads `:cid`, *which is the join key*. On a `group_by` bucket every
element `y` satisfies `lf y = k` (the key is shared scope across the join), so a
factor that reads the key equals one that reads the constant `k = kf x`. That
equality is a **kernel theorem**, `Map.bucket_key_subst` — a *dependent* fact (it
holds *because* of the bucket's defining refinement, that `lf y = k` on it). It
licenses `Map.foldl_keyfactor_float`: the key-factor is **baked once into the
per-key index** instead of recomputed per matching row — moving work from
`O(|matching rows|)` to `O(|distinct keys|)`.

This is the move an erased type checker structurally cannot make: it requires the
*proof* that the field is key-determined, not just the type.

### (c) Refinements license the **relational laws**

The same refinement machinery gates the rest of the relational library: a key field
of a `DecidableEq` type makes `Map.join`/`group_by`/`lookup` (and thus semijoin,
pre-aggregation, join-reorder) applicable; `NodupKeys`-refined maps license O(1)
probe lowering (`docs/CORE.md §4`: "verification licenses the fast representation").

## 3. Worked example, end to end

Idiomatic Clojure under the malli schema above — a join, then a separable weight
whose **left factor reads the join key** (`a/defn`, plain-map runtime):

```clojure
(a/defn revenue [custs orders]
  (reduce + 0 (map (fn [[c o]] (* (inc (:cid c)) (:amount o)))
                   (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders))))
;; (revenue [{:cid 1 :region 0} {:cid 2 :region 0}]
;;          [{:cid 1 :amount 1} {:cid 1 :amount 1} {:cid 2 :amount 2} {:cid 2 :amount 2}]) ;; => 16
```

What the planner does, certified at each step:

1. **types in:** `custs : List Customer`, `orders : List Order`; the fold
   accumulator is `Nat` ⇒ carrier = `(Nat,+,·,0)`.
2. **recognize:** the op is the separable shape `acc + w(kf(fst p))·g(snd p)` with
   `w = inc`, `kf = :cid`, `g = :amount`; the left factor reads the join key.
3. **rewrite:** apply `Map.foldl_join_frame` (frame the product through the per-key
   index) ∘ `Map.foldl_keyfactor_float` (float `inc∘:cid` into the index) — composed
   into one `Eq` proof `original = floated`.
4. **certify:** `cert/verified-rewrite?` re-checks the composed proof with the
   kernel. Only then is the plan adopted.
5. **run:** the chosen plan executes and equals the naive Σ — same answer, but the
   product is never materialized.

```clojure
(w/explain 'revenue)
;; => {:verified? true, :rewrites [:fold-factor :hoist-index], …}   ; the op-generic factorization
```

`w/explain` with no statistics already removes the product (`:fold-factor`) and
hoists the index out of the row-loop (`:hoist-index`). The **per-key pre-aggregated
index** — where the FD scope quotient *floats the key-factor in* — is **ndv-gated**:
given a build-side distinct-key estimate it upgrades to

```clojure
(opt/optimize-cost (a/env) term :lctx lctx :ndv {orders-fvar 3.0})
;; => {:verified? true, :rewrites [:frame-index-keyfactor],
;;     :physical {:strategy :in-memory-hash, :index-est 3.0}}  ; held index = #distinct keys
```

so `inc∘:cid` is computed once per distinct `cid`, never per `|custs|·|orders|` pair.

(See `test/wandler/surface_keyfactor_test.clj` for the runnable `:frame-index-keyfactor`
assertion under an ndv estimate, and [`BENCHMARKS.md`](BENCHMARKS.md) for wall-clock impact.)

## 4. Why it must be *dependent* types

A simple type (`Customer` is a map of ints) is not enough to license any of §2:

- carrier selection needs the value type to **carry its algebra** (which `⊕`/`⊗`,
  with *proofs* of distributivity/annihilation) — that proof rides in the type.
- the FD float needs the **proof** `lf y = k` on the bucket — a proposition about
  values, i.e. a dependent refinement, not a shape.
- the fast field/probe lowerings need the **refinement invariant** (conforms /
  NodupKeys) to be sound.

In each case the optimization is *gated on a proof that lives in the type*. That is
the whole point of doing this in a CIC kernel rather than a checker: the type system
is expressive enough to state the precondition of the rewrite, and the same kernel
that admits Mathlib certifies that the rewrite's precondition holds — per program,
on your data's schema.

## See also

- [`GRADUAL.md`](GRADUAL.md) — the verification ladder; `Value` vs `Option`; "verify
  the algebra, the functions are parameters."
- [`CORE.md`](CORE.md) — the architecture; §3 planner, §4 "verification licenses the
  fast representation," §5 the algebraic structures.
- [`BENCHMARKS.md`](BENCHMARKS.md) — measured impact of these rewrites.
