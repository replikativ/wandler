# Wandler — a verified data-transformation runtime

> *Wandler* (German: **transducer / converter**) — the runtime layer of the Ansatz system. You write
> ordinary Clojure data pipelines; they are **fused, optimized, and certified correct by a CIC kernel**,
> then run as **batch, incremental, or async** depending on the source type.

Wandler is built on [`ansatz`](../ansatz) — the Lean4-in-Clojure proof kernel + DSL. **Ansatz formulates and
proves; Wandler transforms and optimizes.**

## What you get

- **Write normal Clojure** — `(a/defn revenue [orders :- (List (Prod Nat Nat))] Nat (reduce + 0 (map second (filter ... orders))))`.
- **Every optimization is certified** — fusion (`map∘filter` → one pass), relational pushdown, join planning,
  aggregation-through-join — each kernel-checked `optimized ≡ naive`, *per program* (translation validation, not a fixed rule set).
- **The type chooses the mode** — `List` → batch fusion, `Zset` → incremental (DBSP), `Strm` → async, `Datahike.DB` → relational.
- **The semiring chooses the domain** — counting / shortest-path / datalog reachability / provenance / probability (`ansatz.semiring`/`dist`/`wmc`).

## Quickstart

```clojure
(require '[ansatz.core :as a] '[ansatz.stdlib :as std])

(a/init-store! "init")     ; full Lean Init — the optimizer's relational laws live here
                           ; (build once: ../ansatz/scripts/setup-init.sh)
(std/install!)             ; install the verified collection/relational laws

(a/defn big-squares [xs :- (List Nat)] (List Nat)
  (map (fn [x] (* x x)) (filter (fn [x] (< 2 x)) xs)))

(big-squares [1 2 3 4 5])  ; => (9 16 25)
(a/explain "big-squares")  ; => {:verified? true, :rewrites [List.map_filter_filterMap]}   ← fused to one pass, proven equal
```

## Layout

| namespace(s) | role |
|---|---|
| `ansatz.collections` · `ansatz.records` · `ansatz.relational` · `ansatz.edn` | the Clojure surface → kernel terms |
| `ansatz.optimize` (+ `egraph`) · `ansatz.rel-laws` · `ansatz.kmap` · `ansatz.plan` · `ansatz.faq-plan` | the certified cost-directed optimizer |
| `ansatz.mode` · `ansatz.live` · `ansatz.zset` · `ansatz.dbsp*` · `ansatz.stream*` · `ansatz.fork` | incremental + async execution |
| `ansatz.semiring` · `ansatz.dist` (+ `laws`) · `ansatz.wmc` (+ `logicng`) · `ansatz.giry` · `ansatz.lens` | the inference layer (FinSet/FinDist + WMC) |
| `ansatz.bridge.*` (datahike · spindel · stratum) | external engine adapters |
| `ansatz.malli` · `ansatz.refine` · `ansatz.gradual` · `ansatz.reducers*` | malli bridge · refinement · gradual UI · reducer fusion |

> Note: the namespaces are currently under the shared `ansatz.*` prefix (additive split from the monorepo);
> a rename to `wandler.*` is a possible future cleanup.

See [`../ansatz/docs/PROGRAMMING_MODEL.md`](../ansatz/docs/PROGRAMMING_MODEL.md) for the full programming model.

## Optional features (deps aliases)

- `:logicng` — pure-JVM weighted-model-counting backend (`ansatz.wmc.logicng`).
- `:spindel` — live FRP async substrate (`ansatz.bridge.spindel`).
- `:datahike` — live datahike engine for the bridge boundary property tests.

## Tests

```
clj -M:test                 # the full verified-runtime suite (needs the full Init store, ../ansatz/test-data/init-store)
clj -M:test:logicng         # + the LogicNG WMC path
```
