# Cost model redesign: tree-aware, binder-aware, descriptor-driven

> **Status update:** the core of this redesign SHIPPED as `wandler.optimize.cost`
> (tree/let/binder-aware, descriptor-driven op-cost table). The §4 SIGNATURE-derived
> `:list`/`output-list?` and the B2 cost-based backend push-down remain live roadmap items
> (referenced from `clean/optimize/cost.clj`, `exec/physical.clj`, `backend/raster.clj`).
> The original plan below is kept for the rationale.

Status: PLAN (not yet implemented). Goal: make `wandler.optimize.cost` cost *trees* and
*lets*, so the planner can reward sharing (CSE), cost a backend push-down, and serve as the
single seam where engine capabilities (raster / datahike / stratum) declare their cost. Done
carefully and gated on the full suite — we are getting the framework right, not rushing.

## 1. What the model is today

Two independent static models over the kernel term:

- `soac-cost` / `soac-cost-deep` — **op count** (number of SOAC applications). Tree-aware
  (walks the whole term). Consumed by `optimize-body`'s keep-gate and `explain`.
- `pipeline-resources` → `{:size :time :memory}`, `pipeline-cost` = its `:time` — **cardinality
  propagation** (datahike `estimate.cljc`, made static). Consumed by every reorder/factor gate
  in `physical.clj` and the e-graph extraction cost-fn.

`pipeline-resources.walk` is a **linear-pipeline** model: it descends only the `:list` input of a
recognized SOAC (`soac-info`), applies that op's cardinality transform, and returns
`[(size-of e) 0 0]` for anything else (a *leaf* of size `base`, time `0`). Consequences:

- A **tree** — `(+ (foldl A) (foldl B))`, `(Prod.mk a b)` — is a leaf: time `0`. The branches are
  never costed.
- A **let** — `(let s := V in B)` — is a leaf: time `0`. No sharing is visible.
- A **bvar** has no size; a let-bound var defaults to `base`.

## 2. The load-bearing invariant (do not break)

`physical.clj` factor/reorder gates adopt iff `pipeline-cost(rhs) < pipeline-cost(term)`.
`try-fold-factor` rewrites `foldl op e (map proj (join …))` → `foldl (λacc x. foldl … acc (bucket x)) e xs`.
The model charges the **join product** on the LHS, and `~base` on the RHS — *because the RHS's inner
fold sits inside the outer fold's step-λ, and the model never descends into a SOAC step-λ.* The
comment at `physical.clj:64-70` states this explicitly ("no pairs built; … ~0 on the factored sum;
soac-cost RISES 1→2; the materialization win is only visible to pipeline-cost").

> **Invariant: SOAC inputs and step-lambdas must keep their current cost.** Any redesign that
> changes the `:size` a downstream SOAC sees, or starts counting step-λ work in `:time`, will flip
> factorization/reorder adopt decisions. The whole point of tree/let awareness is the *outer*
> structure the old model collapsed to a leaf.

## 3. Design: an additive, binder-aware extension

Cost becomes `cost(e, benv) → {:size :time :memory :ops}` where `benv` maps de-Bruijn indices to
`{:size}` for let-bound variables. The change is **additive**: every case the old model costed
returns the SAME `:size` and `:time`; only the previously-collapsed cases (trees, lets) gain time.

| node | size | time | notes |
|---|---|---|---|
| `bvar i` | `(benv i).size` or `base` | 0 | NEW: let-bound var resolves to its value's size |
| `fvar` / leaf | `(sizes fvar)` or `base` | 0 | UNCHANGED |
| `lit` | 1 | 0 | scalar |
| `lam` | 1 | 0 | a function value — **not descended** (preserves the invariant) |
| `let n T V B` | `cost(B).size` | `cost(V).time + cost(B).time` | NEW: value counted **once** → CSE is cheaper |
| SOAC app | (current `soac-info` transform) | (current) | UNCHANGED — descends only `:list`/`:rhs`/`:pred`, never the step-λ |
| non-SOAC app | **`base` (UNCHANGED leaf size)** | `Σ time(args)` | NEW: trees sum their branches; non-data args recurse to time 0 |

Why this is safe:
- **Size unchanged everywhere.** A non-SOAC node still reports `:size base`, so every downstream
  SOAC sees the same input size → linear-pipeline and factorization *size* estimates are identical.
- **Step-λ still uncounted.** SOAC propagation is untouched; the factored form's outer fold still
  descends only `xs`, so its `:time` is still `~base`. Factorization gates preserved.
- **Trees/lets now have time.** `(+ (foldl S)(foldl S))` → `2·time(S)`; `(let s := S in (+ (foldl s)(foldl s)))`
  → `time(S) + 2·base`. For an expensive barrier `S` (sort/join), the let is strictly cheaper →
  CSE becomes cost-justified (today `try-cse` drops the cost gate because the model mis-prices `let`).

Lambdas are deliberately treated as time-0 leaves (not descended), which both preserves the
invariant and matches "the per-element fn's cost is the consuming op's business" (the op already
charges per element; `predicate-extra-cost` is the existing hook for fn-internal cost like a
membership scan).

## 4. Refactorings / abstractions (make it general on the way)

These are independent of the tree/let fix and each is a net simplification:

1. **Cost-descriptor table — THE framework seam, keyed by signature not name.** Replace `soac-info`
   + the hard-coded `case` in `walk` with a declarative registry: each op → `{:inputs [idx…]
   :card (fn [in opts]→size) :time (fn) :mem (fn)}`. The walk becomes generic (look up descriptor,
   recurse `:inputs`, apply). Crucially, an op's **input/output List-vs-scalar shape is DERIVED from
   its kernel signature** (the elaborator already typed it — `List.map : … → List β` returns a
   `List`), not hand-remembered in a name table. The descriptor table is then
   *"signature → cost behavior"*: `:list`-input positions and `:output-is-list?` come from the
   constant's type in the env (a cheap lookup, no re-inference), and the table only carries the
   genuinely-extra cost semantics (fanout, selectivity, build-weight).
   - Adding an op = a data entry; its data-flow shape comes free from its type.
   - **Engine capabilities plug in here.** A stratum fused-join-group-agg, a raster SIMD kernel, a
     datahike indexed read each become a cost descriptor (+ a lowering) attached to the typed
     constant that names them. The planner's cost model is then the *single place* engines declare
     cost — the capability/cost handshake's home, and what makes raster's compiler transparent to
     the planner. The `:ndv`/`:sizes`/`:selectivity` opts (datahike's `:estimate`) already
     prototype this shape.

2. **Resource profile + algebra.** `{:size :time :memory :ops}` as one record with a `combine`
   (sum times/ops, max mem) so the walk is compositional. Folds `soac-cost` into the SAME traversal
   as an `:ops` dimension — one tree-walk instead of three (`soac-cost`, `soac-cost-deep`,
   `pipeline-resources`), removing duplication.

3. **Binder environment.** Threaded `benv` for lets (and, if ever needed, λ-params); the only new
   piece of state, kept minimal (lambdas aren't descended, so it only grows at `let`).

4. **Gate dimension clarity (document, don't change behavior).** Make explicit which resource each
   gate keys on: fusion/reorder/CSE → `:time`; index-hoist/grace-hash → `:memory`. The factorization
   gate works on `:time` today *because* `:time` charges the product; once the descriptor table makes
   the materialization cost first-class we can optionally move factorization to gate on `:memory`
   (the product avoided) — more accurate, but a separate, later step with its own validation.

5. **Lean on the elaborator's types — cheap reads, not re-inference (this IS v1).** The cost model
   should be type-directed, consistent with the type-directed *soundness* layer (laws typecheck,
   refinements license rewrites, `verified-rewrite?` is a strict `.check`). It just must not pay
   typechecking cost in the search loop. The resolution: read the types the elaborator ALREADY
   attached — a `λ`-binder's type (`e/lam-type`), a constant's signature/return type (one env
   lookup) — never a full `tc/infer-type` per node. So "is this node a `List` (propagate
   cardinality) or a scalar (size 1)?" is a cheap return-type read of the head constant, and
   List-ness generalizes for free to every op (and engine descriptor) instead of being a
   hand-maintained `soac-names` set. Full `infer-type` stays where it belongs — the soundness
   gate, run once per adopted rewrite. (A node whose type genuinely can't be read cheaply falls
   back to the `base`/scalar default — never a hot-path typecheck.)

## 5. Validation strategy (the careful part)

1. **Golden-cost snapshot.** Before touching `walk`, write a test that records
   `pipeline-resources` + `soac-cost` on the gate-critical shapes (the factor LHS/RHS, the reorder
   pair, a linear pipeline, the semijoin) under the current model.
2. **Re-implement to MATCH.** Build the descriptor-driven, binder-aware `walk` so the golden
   snapshot is byte-identical on all linear-pipeline / SOAC shapes (proves §2 invariant held).
3. **Extend.** Add the tree/let/benv cases (new behavior only where the old model returned a leaf).
4. **Suite gate.** Full 288-test suite green. A flipped factorization gate is a RED flag to
   investigate, not to paper over.
5. **Payoff.** Re-enable the CSE cost gate (cost-justified sharing); enable cost-based fuse-vs-share
   for borderline cases; then the engine cost-descriptor handshake and (later) egg cost-extraction
   consume the now-tree-aware model.

## 6. Sequencing

- **A1** golden-cost snapshot test (locks the invariant).
- **A2** descriptor table + profile-with-algebra + generic `walk`, matching the snapshot (pure refactor).
- **A3** tree + let + benv cases (the new capability) → CSE cost gate re-enabled.
- **A4** fold `soac-cost`/`soac-cost-deep` into the descriptor walk (dedup the three traversals).
- **B**  engine cost descriptors (raster/datahike/stratum capability handshake) — separate effort,
        consumes A2's table.
- **C**  egg cost-extraction + cost-based fuse-vs-share — consumes A3.

The keystone is **A2+A3**: a descriptor-driven, binder-aware cardinality model that is identical to
today on pipelines and correct on trees/lets. Everything else (CSE-by-cost, engine transparency,
egg extraction) is a consumer of it.
