(ns wandler.clean.optimize
  "Phase 5 (clean tree) — the verified optimizer facade. THE IR IS THE KERNEL TERM; THE REWRITER IS
   simp — the elaborated `a/defn` body IS the plan, and every adopted rewrite carries a kernel proof
   `orig = result` (translation validation, Lean's `@[csimp]` discipline). Mirrors lean-wandler
   `Optimize.lean` (the certify seam) and the old `wandler.optimize` facade.

   Staged port (each stage harness-gated by `wandler.clean.diff` against the old optimizer = oracle):
     5.1 certify + cost foundations  ← HERE
         · `wandler.clean.optimize.certify` — the CERTIFIER: simp-driven rewriting returning proof
           terms + the strict kernel gate `verified-rewrite?`. `optimize` = fuse + self-certify in one
           (the confluent deforestation path — fully functional end-to-end).
         · `wandler.clean.optimize.cost` — the COST MODEL (SOAC counts + cardinality propagation).
     5.2 cse (let/zeta, soundness-free) · 5.3 egraph (revisit reusing grind directly, cf lean-wandler)
     5.5 relational strategies on the AGGREGATE laws (aggJoin_factor/reorder, replacing the Map cluster)
     5.6 the cost-search DRIVER (optimize-cost/optimize-body) — integrates cse+egraph+physical; ported last.

   This ns re-exports the certify + cost public names; the driver lands in 5.6."
  (:require [wandler.clean.optimize.certify :as cert]
            [wandler.clean.optimize.cost :as cost]
            [wandler.clean.optimize.cse :as cse]))

;; ── certify: the rewriter + the soundness gate (5.1) ─────────────────────────────────────────
(def fusion-lemmas               cert/fusion-lemmas)
(def string-lemmas               cert/string-lemmas)
(def optimize-term               cert/optimize-term)
(def verified-rewrite?           cert/verified-rewrite?)
(def optimize                    cert/optimize)
(def install-filtermap-fusion-law! cert/install-filtermap-fusion-law!)
(def unfold-eqn-ci               cert/unfold-eqn-ci)
(def with-unfold-lemmas          cert/with-unfold-lemmas)

;; ── cost: the heuristic resource model that steers the search (5.1) ──────────────────────────
(def cost-rewrites               cost/cost-rewrites)
(def soac-cost                   cost/soac-cost)
(def soac-stages                 cost/soac-stages)
(def pipeline-resources          cost/pipeline-resources)
(def pipeline-cost               cost/pipeline-cost)

;; ── cse: shared-subtree hoist, soundness-FREE (let/zeta = Eq.refl) (5.2) ─────────────────────
(def try-cse                     cse/try-cse)
