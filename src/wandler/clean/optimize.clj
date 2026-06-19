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
            [wandler.clean.optimize.cse :as cse]
            [wandler.clean.optimize.physical :as phys]))

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

;; ── physical strategies (5.5b) ───────────────────────────────────────────────────────────────
(def try-agg-join-factor         phys/try-agg-join-factor)

;; ── the cost-search DRIVER (5.6) ─────────────────────────────────────────────────────────────
(defn optimize-cost
  "Cost-directed optimization — the SEARCH layer (clean tree). Tries the certified, cost-gated
   PHYSICAL strategies first (currently `try-agg-join-factor` — the FAQ aggregation-through-join
   factorization); if one fires, its result is then FUSED (`cert/optimize` over the confluent
   deforestation set) and the two proofs are composed via `Eq.trans` (`phys/compose-trans`) into ONE
   kernel-certified step: orig ≡ factored ≡ fused. Otherwise plain fusion. The search itself is
   UNTRUSTED — soundness rests entirely on each adopted step being independently `verified?`
   (check-constant). Returns the `cert/optimize`-shaped result + `:rewrites` + `:cost`.

   `:selectivity`/`:sizes` steer the cost gate; `:comm` supplies the join monoid's commutativity
   witness to the factor strategy; `:extra-lemmas` augments the fusion set."
  [env term & {:keys [lctx selectivity sizes comm extra-lemmas]}]
  (let [pc   (fn [t] (cost/pipeline-cost t {:selectivity selectivity :sizes sizes}))
        phys (phys/try-agg-join-factor env term :lctx lctx :selectivity selectivity
                                       :sizes sizes :comm comm)]
    (if (and phys (:verified? phys))
      ;; a physical step fired → fuse its factored result, compose proofs (physical ∘ fuse).
      (let [sub        (cert/optimize env (:term phys) :lctx lctx :extra-lemmas extra-lemmas)
            final-term (:term sub)
            composed   (phys/compose-trans env lctx term (:term phys) final-term
                                           (:proof phys) (:proof sub))
            res {:term final-term :proof composed :changed? true :cost (pc final-term)
                 :rewrites (into [(:rw phys)] (when (:changed? sub) [:fuse]))}]
        (assoc res :verified? (cert/verified-rewrite? env term res :lctx lctx)))
      ;; no physical rewrite applied → plain confluent fusion.
      (let [sub (cert/optimize env term :lctx lctx :extra-lemmas extra-lemmas)]
        (assoc sub :rewrites (when (:changed? sub) [:fuse]) :cost (pc (:term sub)))))))
