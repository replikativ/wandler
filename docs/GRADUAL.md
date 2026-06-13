# Gradual verification in wandler

Wandler is **gradually verified**: you write ordinary Clojure data-transformation
code, and the parts that fit the verified vocabulary are kernel-certified and
optimized, while the parts that don't still run — explicitly trusted, never
silently. This doc explains the model, the two ways "absence" is represented, and
how it contrasts with Typed Clojure.

## The verification ladder

Every function lands on one of three rungs, and `(w/explain 'f)` /
`(a/foreign …)` / `^:partial` make the rung visible:

1. **Verified + optimized** (`a/defn`): the body elaborates to a CIC kernel term,
   the optimizer rewrites it, and the kernel re-checks every adopted rewrite
   (`optimized ≡ original` is a theorem). The search is untrusted; only the
   certificate is.
2. **Trusted** (`^:partial`): elaborated and codegen'd, but admitted as an axiom at
   its type — not verified, not usable in proofs. For recursion we can't or won't
   prove total.
3. **Foreign** (`a/foreign`): an arbitrary Clojure function asserted at a kernel
   type. The body is *not even elaborated* — the raw Clojure fn is the runtime.
   The asserted type is the entire trust boundary.

The guarantee is **honest, not maximal**: verified where it can be, plainly marked
where it can't.

## "Verify the algebra; the functions are parameters"

The key property that makes the foreign rung useful: the optimizer's fusion and
relational laws are **parametric in the element functions**. `map f (filter p xs)
= filterMap (…) xs` holds for *any* `f, p` — so the kernel certifies the rewrite
while `f` and `p` stay opaque blackboxes.

```clojure
(a/foreign sqrt [x :- Float] Float (fn [x] (Math/sqrt x)))   ; trusted hole

(a/defn norm [xs :- (List Float)] (List Float)
  (mapv (fn [x] (sqrt x)) (filterv (fn [x] (< 0.0 x)) xs)))
;; (w/explain 'norm) => {:verified? true, :rewrites ["List.map_filter_filterMap"] …}
;; The pipeline fused into ONE pass and was kernel-certified — even though `sqrt`
;; is a trusted Clojure function the kernel knows nothing about.
```

This is the honest division of labor: **wandler verifies the pipeline algebra;
you bring the functions** — verified (lifted to kernel terms, usable in proofs) or
foreign (arbitrary Clojure, trusted at a type). Either composes into the same
optimized, certified pipeline.

## Two representations of "absence": `Value` (vnil) and `Option`

Wandler has a dynamic tier and a typed tier, and they encode optionality
differently — *not* redundantly, but because a CIC kernel forces it.

- **Dynamic tier — `Value`.** The EDN universe is one closed inductive,
  `vnil | vbool | vint | vstr | … | vmap`. `nil` is a *constructor* (`vnil`), so
  optionality is intrinsic: `(get v k)` returns `vnil` when absent, `(get v k d)`
  returns `d`, `(when c x)`/`(keep f xs)` all use `vnil`. No `Option` needed — and
  this matches Clojure, where `nil` is a genuine first-class EDN value (`{:a nil}`).
- **Typed tier — `Option`.** For a *static* element type (`Nat`, a record) there is
  no "nil Nat" — the kernel has no universal null. So "a `Nat` that might be absent"
  must be `Option Nat = none | some Nat`, consumed by a `match`/`Option.elim`.

You need both because they sit at the two ends of the gradual spectrum: `Value` is
the fully-dynamic, self-nullable end; `Option`-over-a-type is the fully-static end.
The bridge is `conforms` (commit a dynamic `Value` field to a static type) — and
that commitment is exactly where `vnil` becomes `Option`.

At the *surface* the two are unified: `nil?`/`some?`/`if-let`/`some->`/`get`-default
read the same in both tiers; the elaborator dispatches on the receiver's type
(`vnil`-matching for `Value`, `Option.elim` for `Option`).

## Contrast with Typed Clojure

Both are "types for Clojure," but in different regimes:

| | Typed Clojure | Wandler / ansatz |
|---|---|---|
| checks | *types* (no type errors) | *behavior* + transformation correctness |
| `nil` is | a member of a union `(U nil X)` | a constructor `vnil` / a wrapper `none` |
| narrowing | subtract `nil` from the union (`update*`), **erased** | match `vnil` / eliminate `Option`, **runtime, kernel-checked** |
| optimizes code | no (erased checker) | **yes** (certified rewrites) |
| idiomatic reach | high (occurrence typing over as-written code) | a vocabulary + foreign holes |

The deep correspondence: **the `Value` universe *is* Typed Clojure's union
`(U nil vint vstr …)`, reified from the type level to the value level.** TC narrows
by subtracting union members at check time and erasing; wandler narrows by matching
constructors at compile time and keeping the proof. That proof is what lets wandler
*optimize* on the narrowing — which an erased checker structurally cannot.

One-line summary: **Typed Clojure proves the absence of type errors; wandler proves
the presence of correct behavior — and only the latter can license optimization.**
They're complementary, for different jobs, and running both is fine.
