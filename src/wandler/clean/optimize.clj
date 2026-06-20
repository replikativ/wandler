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
            [wandler.clean.optimize.physical :as phys]
            [wandler.clean.optimize.egraph :as egraph]
            [wandler.clean.optimize.faq :as faq]
            [ansatz.kernel.expr :as e])
  (:import [ansatz.kernel Env]))

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
(def try-agg-join-factor         phys/try-agg-join-factor)   ; clean wsum aggregate strategies
(def try-agg-join-reorder        phys/try-agg-join-reorder)
;; the ported FAQ/index strategies live in wandler.clean.optimize.faq (the shared Map-cluster driver);
;; re-export the ones the breadth + tests reach by name.
(def try-hoist-invariant         faq/try-hoist-invariant)
(def try-count-factor            faq/try-count-factor)
(def try-fold-factor             faq/try-fold-factor)
(def try-frame-index             faq/try-frame-index)
(def try-join-reorder            faq/try-join-reorder)
(def try-pre-agg-index           faq/try-pre-agg-index)

;; ── e-graph equality-saturation search (5.3) ─────────────────────────────────────────────────
(def saturate-and-extract        egraph/saturate-and-extract)

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
   witness to the factor strategy; `:extra-lemmas` augments the fusion set.

   `:use-egraph?` swaps the greedy fusion fallback for EQUALITY SATURATION (`saturate-and-extract`):
   when no structured physical strategy fires, saturate the e-graph with all non-confluent hoist +
   reorder laws and extract the cheapest equivalent plan. This finds combinations the greedy path
   misses (a rewrite that is individually cost-neutral but jointly enables a cheaper plan). Soundness
   is unchanged — the e-graph is an untrusted oracle, every adopted plan carries a `check-constant`-
   verified proof. The structured physical strategies still run first (their factor/reorder wins need
   the commutativity witness + the structured recognizer, not expressible as a flat oriented rewrite)."
  [env term & {:keys [lctx selectivity sizes comm extra-lemmas] :as opts}]
  (let [pc   (fn [t] (cost/pipeline-cost t {:selectivity selectivity :sizes sizes}))
        ;; clean AGGREGATE (wsum) strategies — the clean tree's OWN aggJoin_factor/reorder over WSemiring
        ;; (a distinct shape from the Map-cluster driver). Try first; if neither fires, delegate to the
        ;; FULL ported driver (`faq/optimize-cost-driver`: pre-agg / frame (+cond/keyfactor) / grace-hash /
        ;; count·fold·join reorder → hoist-index | nested-loop, + the greedy cost-rewrite pool + e-graph
        ;; saturation, all budget/ndv-gated) — a verbatim port of the old optimizer so the breadth gets
        ;; identical plan selection. Every adopted step is kernel-certified (verified-rewrite?).
        wsum (or (phys/try-agg-join-factor env term :lctx lctx :selectivity selectivity :sizes sizes :comm comm)
                 (phys/try-agg-join-reorder env term :lctx lctx :selectivity selectivity :sizes sizes :comm comm))]
    (if (and wsum (:verified? wsum))
      (let [sub        (cert/optimize env (:term wsum) :lctx lctx :extra-lemmas extra-lemmas)
            final-term (:term sub)
            composed   (phys/compose-trans env lctx term (:term wsum) final-term (:proof wsum) (:proof sub))
            res {:term final-term :proof composed :changed? true :cost (pc final-term) :rewrites [(:rw wsum)]}]
        (assoc res :verified? (cert/verified-rewrite? env term res :lctx lctx)))
      (apply faq/optimize-cost-driver env term (mapcat identity opts)))))

;; ── the a/defn-integrated optimizer entry (Phase 8.3) ────────────────────────────────────────
(def ^:dynamic *use-egraph*
  "When true, `optimize-body` runs the e-graph equality-saturation search instead of the greedy
   cost driver. Default greedy (saturation is heavier)." false)

(defn optimize-body
  "Optimize the pipeline INSIDE a function body `λp0…λp_{n-1}. pipeline` — what `a/defn` calls (via the
   ansatz.core optimize-hook) to get a faster but proven-equivalent runtime term. Opens the n parameter
   binders with fresh fvars (so the pipeline optimizes in its proper context, not as a whole-function
   term that η-collapses), runs the cost-directed search (confluent fusion + cost-gated physical
   strategies, each adopted step kernel-certified), then CSE-hoists shared barriers post-fusion, and
   re-abstracts. Keeps the rewrite iff it verified AND changed (and, when named helpers were inlined,
   only if the honest SOAC cost strictly dropped). `:term` is the original body unless the rewrite
   verified. Clean-tree port of wandler.optimize/optimize-body over the clean cert/cost/cse/phys driver."
  [^Env env body n & {:keys [extra-lemmas]}]
  (loop [ex body, i 0, fvids [], types [], names []]
    (if (and (< i n) (e/lam? ex))
      (let [fid (+ 8800000 i)]
        (recur (e/instantiate1 (e/lam-body ex) (e/fvar fid)) (inc i)
               (conj fvids fid) (conj types (e/lam-type ex)) (conj names (e/lam-name ex))))
      (let [lctx (into {} (map (fn [fid nm ty] [fid {:name (str nm) :type ty}]) fvids names types))
            ;; INLINE named helpers (definitional `.eq_unfold` rules, generated on the fly).
            [env0 unfold-names] (cert/with-unfold-lemmas env ex)
            ;; ensure the map∘filter→filterMap law is available (idempotent; verify-once, local).
            env+ (cert/install-filtermap-fusion-law! env0)
            cost-before (cost/soac-cost-deep env ex)
            ;; cheap pre-check: nothing to fuse with < 2 (deep) SOAC ops — skip simp entirely, EXCEPT a
            ;; membership scan (List.elem → semijoin) or a bare aggregate over a Map.join (factorization).
            res (if (and (< cost-before 2)
                         (not (cost/mentions-const? ex "List.elem"))
                         (not (cost/mentions-const? ex "Map.join")))
                  {:term ex :verified? true :changed? false :rewrites []}
                  (optimize-cost env+ ex :lctx lctx :use-egraph? *use-egraph*
                                 :extra-lemmas (concat extra-lemmas unfold-names)))
            ;; SHARED-SUBTREE PLANNING (CSE) — POST-fusion: hoist a remaining shared BARRIER (join/sort/
            ;; group-by used by ≥2 consumers) into a `let` (certificate Eq.refl = zeta defeq). Composes
            ;; (fuse ∘ cse) proofs by Eq.trans.
            res (if-not (:verified? res) res
                  (loop [r res, guard 0]
                    (let [c (when (< guard 8) (cse/try-cse env+ (:term r) :lctx lctx))]
                      (if (and c (:verified? c))
                        (recur {:term (:term c)
                                :proof (phys/compose-trans env+ lctx ex (:term r) (:term c) (:proof r) (:proof c))
                                :verified? true :changed? true
                                :rewrites (conj (vec (:rewrites r)) :cse)}
                               (inc guard))
                        r))))
            ;; keep iff verified + changed; AND when helpers were inlined, only if the honest SOAC cost
            ;; strictly DROPPED (inlining that doesn't fuse would just duplicate code → revert).
            ok (and (:verified? res) (:changed? res)
                    (or (empty? unfold-names)
                        (< (cost/soac-cost (:term res)) cost-before)))
            reabstract (fn [t]
                         (loop [t t, j (dec (count fvids))]
                           (if (neg? j) t
                               (recur (e/lam (str (nth names j)) (nth types j)
                                             (e/abstract1 t (nth fvids j)) :default)
                                      (dec j)))))]
        {:term (if ok (reabstract (:term res)) body)
         :verified? (:verified? res)
         :changed? (boolean ok)
         :rewrites (:rewrites res)
         :stages-before (cost/soac-stages ex)
         :stages-after (cost/soac-stages (if ok (:term res) ex))
         :passes-before cost-before
         :passes-after (cost/soac-cost (if ok (:term res) ex))}))))

;; ── explain: a human-readable account of optimize-cost's plan (Phase 8 Level 1) ──────────────
(defn explain
  "Human-readable account of what `optimize-cost` did — the relational/PHYSICAL strategy + the
   memory reasoning, the algebraic rewrites, and the certificate. Clean-tree port; uses the FAQ
   strategy descriptions."
  [result]
  (let [rw (:rewrites result)
        physd (:physical result)
        rewrites (keep faq/rewrite-descriptions rw)
        strlaws  (filter string? rw)]
    (str "verified plan" (when-not (:changed? result) " (unchanged)") "\n"
         (when (seq rewrites) (str "  rewrites: " (clojure.string/join "; " rewrites) "\n"))
         (when physd
           (str "  physical: "
                (case (:strategy physd)
                  :in-memory-hash "IN-MEMORY HASH (build the index once)"
                  :nested-loop    "NESTED-LOOP (stream, no held index)"
                  :grace-hash     "GRACE-HASH (spill: build side in budget-sized blocks)"
                  :pre-agg-index  "PRE-AGGREGATED HASH (buckets pre-summed; O(distinct keys))"
                  (str (:strategy physd)))
                (format " — index est ~%.0f %s budget %s\n"
                        (double (:index-est physd))
                        (if (<= (double (:index-est physd)) (double (:budget physd))) "≤" ">")
                        (if (>= (double (:budget physd)) 1.0e8) "(default)" (format "%.0f" (double (:budget physd)))))))
         (when (seq strlaws) (str "  laws:     " (clojure.string/join ", " strlaws) "\n"))
         "  proof:    " (if (:verified? result) "optimized ≡ original (kernel-certified)" "UNVERIFIED"))))
