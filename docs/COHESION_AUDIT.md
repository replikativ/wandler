# Cohesion audit (v0.1, 2026-06-12)

A three-axis audit of the codebase before first publication: execution-layer
strata, the surface/elaboration strategy, and proof/law organization. Summary
verdict: **the architecture is layered by design, but lightly integrated** —
the strata compose only at type boundaries, several seams are implicit, and
the audit found three trust-boundary bugs (all fixed, see §4).

---

## 1. Execution layers: five representations, three verified paths

| representation | namespaces | role |
|---|---|---|
| eager `List`/vector | collections · relational · kmap · runtime | the batch path |
| unboxed `long[]`/`double[]` | runtime | transparent fast lane of the batch path |
| streams `Strm A = Nat→A`, `LSeq A = Nat→Option A` | stream · stream-comonad · stream-surface | infinite sources, windowed observation |
| Z-sets `A→Int` | zset · dbsp* | incremental (deltas with deletions) |
| live cells (push graph) | live · fork | the push-driven *dispatch* of the Z-set semantics |

They organize into **three verified paths**: batch (`List` → fused codegen),
incremental (Z-set → ∂ pass), async-incremental (`Strm (Zset A)` via the proven
`Mode.diff_async_dist`). Composition is type-gated, not free: arrays compose
transparently with lists; streams meet lists only at a `take` window (the
productivity discipline); List and Z-set never mix in one pipeline — the mode
picks. **`live.clj` is active, not vestigial**: it is the push counterpart of
zset's pull queries (same kernel laws), reachable via `live/flow` or
`(mode/incrementalize … :live? true)`, green-tested. `fork.clj` (JIT
speculation substrate) is real but only deferred-tested; `causality.clj` is an
intentional standalone worked example (extrinsic causality of `z⁻¹`).

**Cohesion gaps (the v0.2 integration list):**
1. `mode.clj` computes the route but doesn't *apply* it — each lowering is a
   separate entry point. Needed: one `mode/execute` dispatcher.
2. Three stream abstractions (`Strm`/`LSeq`/`unfoldTake`) without a surface
   unification point.
3. Two monoid mechanisms: `runtime/monoid-fold-ops` (kernel-law-gated, active)
   vs `reducers/MonoidSpec` (kernel-oblivious, experimental) — unify on the
   gated one.
4. `stream.clj` ↔ `dbsp_stream.clj` operate on the same carrier with no
   declared seam (only `mode.clj` knows they compose).
5. The streaming measure→replan loop (fork + live) is designed but not
   green-tested.

## 2. The surface strategy, honestly characterized

It is **not abstract interpretation**. It is a **type-directed staged
elaborator**: partial evaluation of a *fixed, closed verb vocabulary*
(~40 clojure.core verbs + records + relational + EDN predicates) into a typed
CIC IR, with dispatch on the *inferred receiver type* (`count` over
`Value`→`vsize`, `Map`→entries, `List`→`length`). Mechanically it is lean4's
`elab_rules`/`macro_rules` split, reached through ansatz's two registries.

It **is compositional within the vocabulary** — every elaborator recurses
through the single `elab` entry, so verbs nest arbitrarily. The boundary is
where it frays, and the boundary is currently implicit:
- receiver type not inferable → was a silent List default (**fixed**: honest
  error, §4.4);
- unregistered verbs as function *values* fail late (registered ones are
  eta-expanded);
- `stream-surface` routing captures the original registrations at install
  time — install-order fragile (v0.2: late-bound registry reads);
- EDN predicates throw rather than delegate off-Value (the old delegate
  pattern died with the legacy elaborator).

v0.2: write the surface subset down as a spec (the verb table with signatures
and dispatch rules), and make every boundary failure an early, named error.

## 3. Proofs and laws

Better organized than the file count suggests: one dependency DAG
(lookup/group_by foundation → pushdown → semijoin → aggregation → join_comm →
grace-hash/FAQ), built and admitted in order by `rel-laws/install!`, memoized.
Only three axioms exist in src — the opt-in datahike API spec
(`Datahike.DB/q/scan`); everything else is kernel-proven (`Mode.diff_async_dist`,
once admitted, is now a real proof). `optimize.clj` splits cleanly into
certifier / cost model / physical strategies when we get to it; the cost model
is heuristic by design — soundness rests solely on `verified-rewrite?` (strict
kernel check) per adopted rewrite.

## 4. Trust-boundary bugs found and FIXED (this commit)

1. **`relational.proofs/reg-anon!` admitted the six `join_comm`-chain
   intermediates with the lenient `add-constant`** → now strict
   `check-constant`. (All six pass — nothing was masked.)
2. **`Map.count_join_factor` was consumed by `optimize/try-count-factor` but
   only ever admitted in a test** → the prover now lives in `rel-laws` and is
   installed by `install!`; the path fires in production
   (`(count (join …))` → `:count-factor` + `:hoist-index`, certified, runs).
3. **`rel-laws/install!` cache replay used lenient admission** → strict on
   replay too.
4. **`collections/list-elem` silently let an uninferable receiver fall into
   List ops** → throws a named error (`list-elem?` remains as the probe form).
5. (enabling fix) the `a/defn` optimizer pre-check skipped SOAC-trivial bodies;
   bare aggregates over `Map.join` are now exempt (like `List.elem`), and
   `List.sum` — the factored form — gained its runtime lowering.
