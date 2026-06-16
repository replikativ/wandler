# Wandler — a verified data-transformation runtime

> *Wandler* (German: **transducer / converter**). You write ordinary Clojure data
> pipelines; they are elaborated to CIC kernel terms, **optimized by certified
> rewriting**, and lowered to fast Clojure. Every adopted rewrite carries a kernel
> proof `optimized ≡ original` — *translation validation*, checked per program by
> the same kernel that admits Mathlib. The optimizer's search is untrusted; only
> the certificate is. A bad rewrite is rejected, never miscompiled.

Wandler is built on [`ansatz`](https://github.com/replikativ/ansatz) — the
Lean4-in-Clojure proof kernel + DSL. **Ansatz formulates and proves; Wandler
transforms and optimizes.**

## Quickstart

```clojure
(require '[ansatz.core :as a])
(a/init! "test-data/init-store" "init")  ; the Lean Init env (lazy PSS store, ~40ms)
(require '[wandler.core :as w])
(w/install!)                             ; fill ansatz's three seams (surface · optimizer · runtime)

;; ordinary Clojure — verified, optimized, certified, compiled
(a/defn big-squares [xs :- (List Nat)] (List Nat)
  (map (fn [x] (* x x)) (filter (fn [x] (< 2 x)) xs)))

(big-squares '(1 2 3 4 5))   ;; => (9 16 25)
(w/explain 'big-squares)
;; => {:verified? true, :changed? true,
;;     :rewrites ["List.map_filter_filterMap"],
;;     :stages-before ["map" "filter"], :stages-after ["filterMap"],
;;     :passes-before 2, :passes-after 1}

;; transducers are the same pipeline IR in another spelling
(a/defn sum-big [xs :- (List Nat)] Nat
  (transduce (comp (filter (fn [x] (< 2 x))) (map (fn [x] (* x x)))) + 0 xs))

;; relational re-planning, certified per plan: install the PROVEN law library,
;; and an O(n·m) membership scan re-plans to a build-once hash-index semijoin
(require '[wandler.laws.relational :as laws])
(laws/install!)
(a/defn only-known [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  (filter (fn [x] (member x ys)) xs))
(w/explain 'only-known)
;; => {:verified? true, :rewrites ["List.elem_filter_eq_index_probe"], …}

;; the measure→replan loop (the verified JIT): selectivities measured on real
;; data feed the cost model; the adapted plan is re-certified before it runs
(w/optimize-measured (a/env) term sample-data :compare? true)

;; DEPENDENT TYPES drive the plan: keep your malli, change defn → a/defn (the on-ramp;
;; load `ansatz.malli`). A `[:map …]` arg becomes a refinement record; the planner reads
;; the schema to factor an aggregating join — certified equal to the naive plan.
(require '[malli.core :as m] '[ansatz.malli])
(m/=> revenue
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]]]
             [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]] :int])
(a/defn revenue [custs orders]
  (reduce + 0 (map (fn [[c o]] (* (inc (:cid c)) (:amount o)))
                   (join (fn [c] (:cid c)) (fn [o] (:cid o)) custs orders))))
(revenue [{:cid 1 :region 0} {:cid 2 :region 0}]
         [{:cid 1 :amount 1} {:cid 1 :amount 1} {:cid 2 :amount 2} {:cid 2 :amount 2}])  ;; => 16
(w/explain 'revenue)   ;; => {:verified? true, :rewrites [:fold-factor :hoist-index], …}
;; with build-side cardinality stats the planner upgrades to the per-key pre-aggregated
;; index (`:frame-index-keyfactor` — the FD scope quotient floats the key-factor in); and
;; the SAME factorization is semiring-generic: counting (Nat), boolean provenance
;; (Bool, ∨/∧), tropical shortest-path (ℕ∞, min/+).
```

See [`docs/DEPENDENT_TYPES.md`](docs/DEPENDENT_TYPES.md) for how malli schemas become
refinement types that license the plan, and [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md)
for the measured impact (FAQ factorization: 4×→22× and widening, same certified answer).

See [`dev/demo.clj`](dev/demo.clj) for the full walk-through (fusion → transducer
re-execution → certified re-planning → batch/incremental/stream modes).

## The stack

```
   Clojure surface             (a/defn revenue [orders :- (List …)] …
   map/filter/reduce/             (reduce + 0 (map :amt (filter premium? orders))))
   group-by/join/records/             │
   transducers                        │  ELABORATE   (SEAM 1 — term/macro elaborator registries,
                                      ▼               lean4's elab_rules / macro_rules)
   kernel IR = CIC term        List.foldl + 0 (List.map amt (List.filter premium? orders))
   (the term IS the plan)             │
                                      │  OPTIMIZE    (SEAM 2 — a/optimize-hook:
                                      │               simp fusion + cost search + relational laws)
                                      ▼
                              term′ + PROOF: term = term′   ◀── the kernel CERTIFIES (yes/no)
                                      │
                                      │  LOWER       (SEAM 3 — a/codegen-registry:
                                      ▼               unboxed scans, parallel monoid fold, hash joins)
   fast Clojure                an ordinary fn
```

Integration with ansatz is **three additive seams** — no fork, no carve. ansatz
alone still runs base `a/defn`; ansatz + wandler is the full pipeline.

## Trust ledger

| level | meaning | enforced by |
|---|---|---|
| **L0** | kernel-certified — an algebraic law proven as a CIC term | the kernel's `check` (the path that admits Mathlib) |
| **L1** | sound by construction — codegen of a proven-equal term | the `define-verified` invariant |
| **L2** | trusted oracle — numeric/external, *not* a CIC proof | WMC counts, measured selectivity profiles, external engine planners |

Highlights at L0: pipeline fusion (`map∘filter → filterMap`, fold fusion),
relational pushdown + semijoin (`List.elem_filter_eq_index_probe`),
aggregation-through-join factorization (the **FAQ frame rule**, now
**semiring-generic** — one proof certifies counting (`Nat`), boolean provenance
(`Bool`, ∨/∧), and tropical shortest-path (`ℕ∞`, min/+); see
[`docs/DEPENDENT_TYPES.md`](docs/DEPENDENT_TYPES.md)), the dependent-types **FD
scope quotient** (a key-determined factor floats into the per-key index,
licensed by `Map.bucket_key_subst`), the parallel-fold licence (`Nat.add_assoc`
+ identities — the associativity proof *is* the soundness certificate for
fork-join), DBSP increment laws, Z-set group laws. Measured impact:
[`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

## Layout (v0.1 core)

| prefix | role |
|---|---|
| `wandler.core` | the front door: `install!` (the three seams), `explain`/`plan`, the measure→replan loop |
| `wandler.surface.*` | SEAM 1 — the Clojure verb vocabulary → kernel terms (collections · records · relational · streams · malli · refine; the dynamic EDN tier lives in `ansatz.surface.{data,schema}`) |
| `wandler.optimize.*` | SEAM 2 — `certify` (the kernel gate) · `cost` (the resource model) · `physical` (plan drivers) · `egraph` · `cse` · `plan`/`faq` |
| `wandler.laws.*` | the proven law library — `relational` · `proofs` (foundational List/Map/Perm) · `proofs.frame` (the FAQ frame-rule + semiring-generic family) · `semiring` (the carrier registry) · `tropical` (the ℕ∞ carrier) · `dist`; one DAG, strict admission |
| `wandler.runtime` · `wandler.algebra` | SEAM 3 — lowering (unboxed scans, hash joins) + the law-gated licences (parallel monoid fold) |
| `wandler.exec.*` | the verified paths: batch is implicit; `zset`/`dbsp*` (incremental) · `stream` (windows/comonad) · `live`/`fork` (push) · `mode` + `mode-laws` (the lattice + its kernel proof) |
| `wandler.jit.*` · `wandler.backend.*` | `jit.{estimate,pgo,stream}` (measure→replan→recompile) · `backend.{raster,stratum,simd}` (opt-in native/columnar engines) |
| `wandler.inference.*` | semiring readings of the same core (semiring · dist · wmc · giry · lens) |
| `wandler.bridge.*` | external engine adapters (datahike · spindel · stratum) — optional deps |
| `wandler.kmap` · `wandler.reducers*` · `wandler.gradual` · `wandler.regex` · `wandler.verified` | the verified Map · the (deferred) reducer calculus · gradual UI · regex planning · transducer surface |

See [`docs/CORE.md`](docs/CORE.md) for the architecture spec.

## Status

v0.2 — the cohesion release ([`docs/COHESION_AUDIT.md`](docs/COHESION_AUDIT.md)):
role-prefixed layout, the optimizer split (certify/cost/physical), the
`wandler.algebra` licence registry, one stream home, `mode/execute` (the type
picks the lowering — batch fuse / pull-incremental / push live graph), and the
vocabulary as data ([`docs/SURFACE.md`](docs/SURFACE.md) is generated from it).

Since: the **FAQ frame rule lifted off Nat** — the whole separable-weight
factorization (frame + sum-factor + the FD keyfactor-float layer) is now
**semiring-generic**, certified per-carrier and routed by a carrier registry that
each carrier's laws register into; three carriers ship (Nat / Bool / tropical
ℕ∞). A review-driven cleanup pass followed (4 reorg phases, dead-code removal, 4
execution-glue bug fixes, a shared emitter adopt/verify point). Suite: **335 tests
/ 1522 assertions**, green. [`test-deferred/`](test-deferred/) documents the
remaining quarantine — most of it now passes standalone and is blocked on a shared
test-isolation fixture (cross-namespace registry/env pollution in the single-JVM
runner), not per-test bugs.

## Tests

```
clj -M:test                 # needs the full Init store at test-data/init-store
clj -M:test:logicng         # + the LogicNG WMC path
```

## License

Copyright © 2026 Christian Weilbach. Distributed under the [Apache License 2.0](LICENSE).
