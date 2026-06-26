# Engines — cross-engine integration and end-to-end planning

A wandler pipeline does not have to run on one engine. A query can read one relation from a
[datahike](https://github.com/replikativ/datahike) database and another from a
[stratum](https://github.com/replikativ/stratum) columnar dataset, join them, aggregate — and
the **structure around those sources stays kernel-certified** even though the sources themselves
are opaque to the kernel. The trick: an external engine is a **trusted, typed boundary** (an
axiom), and the kernel proof `factored ≡ naive` is a fact about the *term*, **engine-agnostic at
the source**. So you can swap which engine owns a source without touching the proof.

Start with **the surface path** below — write a `datahike.api/q` straight into an `a/defn` and the
planner spans it. The rest of the doc is the mechanism under it: how an engine registers, the
plan-lens that bridges engine IR and kernel terms, the cost handshake that makes planning
end-to-end, and a worked cross-engine query. It lives in `wandler.surface.engines` (the surface
source) + `wandler.bridge` + `wandler.bridge.{datahike,stratum,spindel}` and the
`wandler.exec.mode/register-foreign!` boundary.

## The surface path: a database query inside an `a/defn`

The headline ergonomic — write a **real datahike query inside an ordinary `a/defn` pipeline** and
the planner treats *that very query* as a source, planning end-to-end across the combinator and the
query together. Opt in once (additive, no native dep until you actually run a query):

```clojure
(require '[ansatz.core :as a] '[wandler.core :as w] '[wandler.surface.engines :as eng])
(a/init! "test-data/init-store" "init")
(w/install!) (w/install-laws!)
(eng/install!)        ; intercept datahike.api/q as a surface source
```

Now a `datahike.api/q` call *is* a relation source in the pipeline. It elaborates to a typed
kernel leaf (`EngineSource.qN : Nat → List (Prod Nat … Nat)`), the certified optimizer plans over
the surrounding combinators, and codegen lowers the leaf back to the real `d/q` call:

```clojure
(def db @conn)                              ; a live datahike db value (a top-level var)

(a/defn sum-regions [] Nat
  (reduce + 0 (map (fn [r :- (Prod Nat Nat)] (Prod.snd Nat Nat r))
                   (datahike.api/q '[:find ?cid ?region
                                     :where [?e :cid ?cid] [?e :region ?region]] db))))

(:stages-before (w/explain 'sum-regions))  ;=> [map foldl]   ; map over the engine scan
(:stages-after  (w/explain 'sum-regions))  ;=> [foldl]       ; fused into one pass
(:verified?     (w/explain 'sum-regions))  ;=> true          ; kernel proved fused ≡ naive
sum-regions                                 ;=> 9             ; ran live against datahike
```

Two things to know: a **no-arg** `a/defn` evaluates to its result *constant* (the query runs once,
at definition, against the db var) — read `sum-regions`, don't call it. And the `db` lives inside
the opaque source, so it's an ordinary **runtime-resolvable form** (a top-level var), never a kernel
parameter.

With ansatz's namespace-alias resolution, the **aliased** form dispatches identically — so the
idiomatic `(d/q …)` works, not just the fully-qualified head:

```clojure
(require '[datahike.api :as d])
(a/defn sum-regions-aliased [] Nat
  (reduce + 0 (map (fn [r :- (Prod Nat Nat)] (Prod.snd Nat Nat r))
                   (d/q '[:find ?cid ?region :where [?e :cid ?cid] [?e :region ?region]] db))))
;; same plan, same proof, same answer (9)
```

**The boundary is where it pays off.** Join an engine source against an in-memory relation and an
aggregating group-by-over-join **factorizes across the boundary** — the join is never built, even
though one side is the live database scan:

```clojure
(m/=> rev-by-region                         ; orders is a named record so :amount/:cid resolve
  [:=> [:cat [:sequential [:map [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]]]]
       [:sequential :int]])
(a/defn rev-by-region [orders]
  (map (fn [g] (reduce + 0 (map (fn [[c o]] (:amount o)) g)))
       (vals (group-by (fn [[c o]] (Prod.snd Nat Nat c))         ; region, from the datahike scan
                       (join (fn [c] (Prod.fst Nat Nat c)) (fn [o] (:cid o))
                             (datahike.api/q '[:find ?cid ?region
                                               :where [?e :cid ?cid] [?e :region ?region]] cdb)
                             orders)))))

(:rewrites      (w/explain 'rev-by-region))  ;=> [:groupby-reduce-join :hoist-index]   ; join eliminated
(:stages-after  (w/explain 'rev-by-region))  ;=> [map foldl foldl group_by]            ; 6 → 4 passes
(:verified?     (w/explain 'rev-by-region))  ;=> true
```

> **✓ proven structure, ⚠ trusted source.** The factorization `factored ≡ naive` is a kernel proof
> about the *term* — engine-agnostic at the source boundary. The datahike scan's *contents* are the
> engine's trusted contract; the structure that eliminates the join is certified. Validated live in
> `engine_surface_test` (the single-source fuse) and the kernel-term-level `cross_engine_*` tests
> (the factorization). The mechanism below is what makes all this work.

## An engine is a trusted axiom

There are two registration contracts, at two granularities.

**A black-box function** — `wandler.exec.mode/register-foreign!` admits a third-party Clojure fn
as a typed `dom → cod` **kernel axiom** and registers its runtime. The pipeline *around* the
foreign leaf stays certified; the leaf is trusted. `references-axiom?` classifies each leaf
verified-vs-trusted, so the cost model and the coach can *see* the boundary. This is "the
`Datahike.q` pattern, generalized" — e.g. a foreign `pair-sum` runs inside a certified live graph,
reported `:trusted` while the join around it is `:verified`.

**A whole engine** — `wandler.bridge/register-engine!` takes `{:detect? :lift :lower :estimate}`.
The optional datahike and stratum adapters register on load:

```clojure
(require '[wandler.bridge :as bridge])
(bridge/load-optional-engines!)
(bridge/registered-engines)   ;=> #{:stratum :datahike}
(bridge/available-engines)    ;=> #{:stratum :datahike}     ; those actually on the classpath
```

For datahike the axioms go deeper than "opaque source": `Datahike.q : DB → (f : FindSpec) →
Result f` is typed so the **return type computes from the `:find` clause** (`Result`/`Decode` are
kernel recursors over `Datahike.FindSpec`) — a `:scalar` find yields `Nat`, `:coll` yields
`List Nat`, `:rel` yields `List (Nat × Bool)`. A lowered plan can then be checked to *provably
inhabit* the engine's declared result type.

## The plan-lens bridge: `lift` / `lower`

The relational **plan-lens** (`wandler.optimize.plan`, `term ⇄ plan`) is the common IR. Each
engine's adapter `lift`s its logical query IR into a kernel term and `lower`s a term back. For
datahike (`wandler.bridge.datahike`) the α-spec is:

```
LScan [?e :attr ?v]      ↦  a relation SOURCE  (List Row)   — opaque; datahike's contract is "yields the datoms for :attr"
LFilter p (q)            ↦  List.filter p ⟦q⟧
LEntityJoin on (l) (r)   ↦  Map.join kf lf ⟦l⟧ ⟦r⟧          — the equi-join on a shared logic var
```

A scan is an **opaque trusted source** — its schema lives in the *row type*, so a pushdown only
type-checks against attributes that are actually present. Once a query is lifted, the **already-
proven relational laws** optimize it (filter→join pushdown, semijoin, count/sum factorization) —
the same certified rewrites from [OPTIMIZER.md](OPTIMIZER.md), now over engine-shaped terms. A
correlated subquery (a transducer whose fn invokes the engine's `q`) **decorrelates** at the lift
boundary. `bridge/optimize-plan` runs the round-trip and reports the verified plan shape.

> **✓ proven structure, ⚠ trusted source.** The optimization is certified; the scan's *contents*
> are the engine's trusted contract. Lowering a source leaf is just `{:engine :datahike} → d/q`,
> `{:engine :stratum} → q/q` — and because the proof is engine-agnostic, **swapping the engine
> never touches the certificate.**

## End-to-end planning: the cost handshake

Planning is end-to-end because the optimizer's cost model reads each engine's own cardinality
estimate. datahike's live `:estimate` (an index count-slice) feeds the optimizer's per-source
`:sizes`/`:selectivity`; the JIT's measured `profile-selectivity` (see [JIT.md](JIT.md)) is the
stream override. The cost model then makes the drive-direction call — index the smaller side:

```clojure
;; users ⋈ orders, per-source sizes from each engine's :estimate
(opt/pipeline-cost join {:sizes {3 100.0  4 1000000.0}})   ;=> 2000100.0   ; index 100-row users
(opt/pipeline-cost join {:sizes {3 1000000.0 4 100.0}})    ;=> 1000200.0   ; swapped — cheaper
```

`plan/resolve-oracle` dispatches per source nature: a materialized engine gives exact sizes; a
stream gives measured selectivity. The plan that comes out is the same certified plan either way —
the estimate only chooses *which* certified plan runs (the [JIT](JIT.md) discipline:
profile steers, the kernel guarantees).

## A query that spans engines

The capstone: **joint inference across two databases.** A factor graph `Region — Channel —
HighValue` whose two factors live in different engines — φ₁(Channel, Region) in a datahike
`:memory` DB, φ₂(Channel, HighValue) in a stratum dataset. The marginal `P(HighValue)` sums out
Region and Channel:

```
g(h) = Σ_R Σ_C φ₁(C,R)·φ₂(C,h)        P(H=h) = g(h) / Σ_h' g(h')
```

The factors share `Channel`, so `Σ` over their product is a `Σ` over a **join on Channel** — which
**factorizes** (`Map.foldl_join_factor`), aggregating each channel's contribution per-bucket and
**never materializing** the `Region × Channel × HighValue` joint. Live (`:datahike` + `:stratum`
on the classpath), from `cross-engine-inference-test`:

```
P(HighValue=yes) = 0.5938   (g1 = 19, g0 = 13, Z = 32), cross-engine VE, certified
  scale 160 |φ₁|·|φ₂| = 2560:  naive 1.12 ms → factored 0.50 ms  (2.2×)
2 tests, 17 assertions, 0 failures   — marginal cross-validated == brute-force full-joint
```

> **✓ proven.** The kernel proof `factored ≡ naive` **is** the variable-elimination certificate,
> and it's engine-agnostic at the source boundary — so the *same* certificate covers factors
> drawn from two different databases. Count-weighted factors keep the proof at `Nat`; the
> normalization to a probability is the trusted L2 step. (The full inference story is
> [INFERENCE.md](INFERENCE.md).) Companion live tests: `cross-engine-source` (8 assertions),
> `cross-engine-pushdown` (datahike filter pushdown, 7), `cross-engine-capstone` (a 3-way
> datahike ⋈ stratum ⋈ stratum FAQ, 9).

## The plan-lens is also the physical IR

The same `term → plan` lens that bridges *engines* also drives the **physical backends** — three
lowerings off one lens: `:eager` (`codegen-fn` on the term), `:transduce` (a native Clojure
transducer pipeline), `:array`/SIMD (`plan→raster`). raster and stratum plug into the *same*
`register-engine!` cost-descriptor seam (spindel is the approximate-inference backend; raster the
numeric SIMD one). So "which engine runs this source" and "which physical strategy runs this stage"
are the same kind of certified, cost-gated choice.

## The honest boundary

- **Wired + tested:** engine registration; the datahike/stratum `lift` of their query IR into
  kernel terms; structural relational optimization over engine sources (pushdown, semijoin,
  count/sum factorization); the cross-engine joint-inference marginal; the cost handshake via
  `:sizes`/`:selectivity`.
- **Demonstrated, a small trusted extension:** pushing a predicate *into* datahike's index (the
  `Datahike.filter_q` API axiom) — it certifies with the axiom in the rewrite pool, but it adds a
  trusted datahike contract beyond the kernel (property-test it against live datahike).
- **Open γ side:** stratum's adapter does the α (compiling `[col op arg]` predicates) but the full
  SIMD lowering back to `stratum.query/q` is demo-scoped (2-column `Prod Nat`); the live
  `:estimate` count-slice inside `datahike.clj` is a partly-open oracle seam.

## Where to go next

- **INFERENCE.md** — the cross-engine marginal in full: semirings, variable elimination, WMC.
- **OPTIMIZER.md** — the certified relational laws the bridges reuse over engine-shaped terms.
- **ARCHITECTURE.md** — where the bridge boundary sits in the whole pipeline, and the L0/L2 ledger.
