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
(require '[wandler.rel-laws :as laws])
(laws/install!)
(a/defn only-known [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  (filter (fn [x] (member x ys)) xs))
(w/explain 'only-known)
;; => {:verified? true, :rewrites ["List.elem_filter_eq_index_probe"], …}

;; the measure→replan loop (the verified JIT): selectivities measured on real
;; data feed the cost model; the adapted plan is re-certified before it runs
(w/optimize-measured (a/env) term sample-data :compare? true)
```

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
aggregation-through-join factorization, the parallel-fold licence
(`Nat.add_assoc` + identities — the associativity proof *is* the soundness
certificate for fork-join), DBSP increment laws, Z-set group laws.

## Layout (v0.1 core)

| namespace(s) | role |
|---|---|
| `wandler.core` | `install!` (the three seams), `explain`, `plan`, the measure→replan loop |
| `wandler.collections` · `wandler.records` · `wandler.relational` · `wandler.kmap` | the Clojure surface → kernel terms |
| `wandler.optimize` (+ `egraph`) · `wandler.rel-laws` · `wandler.plan` · `wandler.faq-plan` | the certified cost-directed optimizer + proven law library |
| `wandler.runtime` | the codegen seam: unboxed `long[]` scans, monoid-licensed parallel fold, hash-map joins |
| `wandler.reducers*` | reducer/transducer fusion algebra |
| `wandler.zset` · `wandler.dbsp*` · `wandler.stream*` · `wandler.mode` | incremental (DBSP) + stream execution; the mode lattice |
| `wandler.semiring` · `wandler.dist` · `wandler.wmc` · `wandler.giry` · `wandler.lens` | the inference layer (semiring readings of the same core) |
| `wandler.bridge.*` | external engine adapters (datahike · spindel · stratum) — optional deps |

See [`docs/CORE.md`](docs/CORE.md) for the architecture spec.

## Status

v0.1 — first public cut, fix-forwarded onto ansatz's unified (fvar/metavar)
elaborator and the three runtime seams. The core path — collections + records +
relational surface, certified optimizer + proven law library, runtime lowering,
`explain`/`plan` and the measure→replan loop — is suite-covered and green
(joins, semijoin re-planning, aggregation factorization, reducer fusion, zset/
DBSP/stream algebras, kmap, semiring/dist/wmc). Quarantined in
[`test-deferred/`](test-deferred/) for v0.2: the EDN dynamic-data tier, regex,
mode/stream surface routing, the Float/`def-record` primitive tier, and a few
elaboration-breadth verbs (`some->`, `str`/`clojure.string` ops).

## Tests

```
clj -M:test                 # needs the full Init store at test-data/init-store
clj -M:test:logicng         # + the LogicNG WMC path
```

## License

Copyright © 2026 Christian Weilbach. Distributed under the [Apache License 2.0](LICENSE).
