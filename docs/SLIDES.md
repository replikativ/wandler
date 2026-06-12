# Wandler — slide outline (one slide per layer, with the CIC connection)

The narrative: **"the query plan is a mathematical term, so the planner can be
audited by a proof checker."** Each slide is one stage of the stack; each stage
has a lean4/CIC counterpart, so the architecture doubles as a CIC tutorial.

---

### 1. The problem (hook)
Optimizers are the most bug-prone part of every data system: rewrite rules,
join reordering, fusion — each "obviously correct," collectively a minefield.
Classic answer: test harder. Our answer: **check every plan, per program, with
a proof kernel.** (Translation validation, not verified-compiler heroics.)

### 2. You write ordinary Clojure
```clojure
(a/defn big-squares [xs :- (List Nat)] (List Nat)
  (map (fn [x] (* x x)) (filter (fn [x] (< 2 x)) xs)))
```
malli users: your `m/=>` schemas already ARE the signatures (ansatz on-ramp).
**CIC connection:** elaboration — lean4's `elab_rules`/`macro_rules` split,
verbatim: `map`/`count` are *type-directed term elaborators*; threading macros
are *syntax rewrites*. Wandler extends ansatz through the same two registries
Lean uses for its own syntax.

### 3. The kernel term IS the query plan
`List.foldl + 0 (List.map amt (List.filter premium? orders))` — a term in the
Calculus of Inductive Constructions, the same type theory as Lean 4 / Mathlib.
No separate IR, no impedance: the plan language is a logic.
**CIC connection:** terms, types, and props are one calculus — a pipeline and a
statement *about* the pipeline live in the same language.

### 4. Optimization = certified rewriting
```clojure
(w/explain "big-squares")
;; {:verified? true, :rewrites ["List.map_filter_filterMap"],
;;  :stages ["map" "filter"] → ["filterMap"], :passes 2 → 1}
```
The optimizer searches (simp fusion + cost model + e-graph); the kernel only
answers yes/no to `optimized ≡ original`. Search is untrusted; the certificate
is everything. A wrong rewrite is **rejected, never miscompiled**.
**CIC connection:** the certificate is an `Eq` proof term, checked by the same
Java kernel that re-verifies Mathlib's 648k declarations.

### 5. The law library has receipts
`(laws/install!)` proves the relational rule set on the spot (~5s): filter→join
pushdown, semijoin (`List.elem_filter_eq_index_probe`), aggregation-through-join
factorization. Then:
```clojure
(a/defn only-known [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  (filter (fn [x] (member x ys)) xs))
;; O(n·m) scan  →  build-once hash-index SEMIJOIN, kernel-certified
```
**CIC connection:** an optimizer rule = a theorem. The rule set isn't a config
file; it's a library of proofs.

### 6. Profiles close the loop (the verified JIT)
```clojure
(w/optimize-measured env term sample :compare? true)
```
Measure real selectivities → feed the cost model → re-plan → **re-certify**.
Adapting to the workload cannot make the plan unsound, because every adapted
plan passes the same kernel gate. (This is datahike-style adaptive planning
with a proof obligation.)

### 7. Verification licenses the fast representation
- kernel `Map` = association list with a `NodupKeys` proof → runtime = Clojure
  **hash-map** (observationally equal, O(1) probe — the proof justifies the rep)
- a fold over a **proven** monoid (`Nat.add_assoc` + identities in the env) may
  re-associate → **parallel fork-join**; the associativity proof IS the licence
- unboxed `long[]` scans; `Option` = nil-punning; `Prod` = `[a b]`
**CIC connection:** quotients/refinements (Subtype) erased at runtime.

### 8. One core, many readings (where this goes)
The same pipeline term, interpreted in a different algebra:
Bool semiring → relational · Nat → counting · tropical → shortest path ·
provenance → probability (WMC) · Z-sets → **incremental (DBSP)** · streams →
windowed/async. Each algebra's laws kernel-proven the same way (zset/dbsp/
stream namespaces). *Join order = variable elimination order = the plan.*

### 9. Trust ledger (the honesty slide)
| L0 | algebraic laws, fusion, plans | CIC proof, kernel-checked |
| L1 | codegen of proven-equal terms | sound by construction |
| L2 | selectivity profiles, WMC backends, external planners | trusted oracles, diff-tested |

### 10. Status + the ansatz/wandler split
ansatz = the kernel + DSL ("formulates and proves") — released, malli on-ramp.
wandler = the runtime ("transforms and optimizes") — v0.1 tonight: surface +
certified optimizer + law library + runtime seams, integrated into ansatz by
**three additive seams** (elaborator registries · optimize-hook ·
codegen-registry). Demo: `dev/demo.clj`.
