;; Phase 5.3 (clean tree) — the E-GRAPH SEARCH layer for the verified optimizer.
;;
;; The greedy `optimize-cost` (5.6) commits to cost-rewrites one at a time, each of which must
;; STRICTLY lower cost in isolation — so it misses combinations where a rewrite is individually
;; cost-neutral (or slightly worse) but jointly enables a cheaper plan. This layer instead does
;; EQUALITY SATURATION: load the pipeline + all our oriented laws into ansatz `grind`'s e-graph,
;; saturate via E-matching, then EXTRACT the cheapest equivalent term by `pipeline-cost`.
;;
;; SOUNDNESS is unchanged and rests entirely on the kernel. The e-graph is an UNTRUSTED SEARCH
;; oracle: it only decides WHICH term to keep. The certificate is grind's `mk-eq-proof` (a CIC proof
;; `orig = extracted` built by walking the e-graph's transitivity chain) re-checked independently by
;; `verified-rewrite?`. Extraction is restricted to MATERIALIZED in-class members (terms actually
;; present as e-graph nodes), so the proof chain always exists — no synthesized terms.
;;
;; Cross-generation cascades (a law firing on another law's output) are blocked within one saturation
;; by grind's gen=0 E-match gate (loop guard). We recover full saturation with an OUTER FIXPOINT:
;; re-saturate on the extracted term and compose the per-round proofs with `Eq.trans`. Every round is
;; independently kernel-checked.
;;
;; Clean-tree port of the old `wandler.optimize.egraph`: the machinery is IR-AGNOSTIC and reuses ansatz
;; `grind` directly (per lean-wandler's "keep the reuse minimal"), so this is a verbatim retarget — the
;; only changes are (a) requiring the certify/cost LEAVES directly (not the facade — keeps the facade
;; free to require us back without a cycle) and (b) the clean AGGREGATE hoist-law set (`wsum_*`, the
;; prelude big-operator linearity laws) replacing the old `List.sum_map_*` names.

(ns wandler.clean.optimize.egraph
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [wandler.clean.optimize.cost :as cost]
            [wandler.clean.optimize.certify :as cert]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.ematch :as ematch]
            [ansatz.tactic.grind.proof :as egproof])
  (:import [ansatz.kernel Env]))

(def ^:private soac-head?
  "Predicate on a head Name: true for SOAC ops (map/filter/foldl/flatMap/…). Drives `internalize-binders`'
   under-binder descent — only SOAC step-λs are opened, bounding e-graph growth."
  (fn [nm] (boolean (cert/soac-names (name/->string nm)))))

(def ^:private binder-descent-depth
  "Max binder-nesting `internalize-binders` opens (cost guard). 3 covers nested aggregations (Σx Σy …)."
  3)

(defn- mk-st [^Env env lctx]
  (if (seq lctx) (tc/mk-tc-state-with-locals env lctx) (tc/mk-tc-state env)))

(def hoist-laws
  "FAQ loop-invariant HOIST + sum-semiring LINEARITY laws (the prelude `wsum_*` big-operator lemmas,
   installed by `ansatz.prelude.list/install!`; any not yet installed are silently skipped by
   `prepare-theorems`). `wsum_map_mul_left` pulls an x-free factor out of an aggregate; the rest carry
   the additive structure. One of the two sub-categories of `default-laws`."
  ["wsum_map_mul_left" "wsum_map_add" "wsum_map_const_zero"])

(def reorder-laws
  "Relational/cardinality REORDERS (`cost/cost-rewrites` — filter↔map, filter→join pushdown, …). The
   other sub-category of `default-laws`."
  (vec cost/cost-rewrites))

(def default-laws
  "The e-graph's NON-CONFLUENT law set: hoist/linearity (`hoist-laws`) + cardinality/relational reorders
   (`reorder-laws`). `saturate-and-extract` saturates with ALL of these in ONE iterated pass and lets
   recursive extraction + the cost pick the cheapest form — no fixed hoist-before-reorder ordering (the
   e-graph holds every equivalent shape simultaneously). Confluent fusion (`cert/fusion-lemmas`) is NOT
   here — that's simp's job (simp ≈ lean4 Meta/Tactic/Simp normalizer; the e-graph cost-extraction is
   the egg-style search layer on the grind congruence core)."
  (vec (concat hoist-laws reorder-laws)))

(defn- saturate-once
  "One saturation round on `term`: build a fresh e-graph, internalize, E-match all `laws`, then
   RECURSIVELY extract the cheapest equivalent term by `cost-fn` together with its kernel proof
   `term = extracted` (`proof/extract-and-prove`). Recursive (egg-style) extraction rebuilds the
   ENCLOSING term from a rewritten subterm — so a rewrite that fires under an application (e.g. a
   loop-invariant hoist in-context) is extractable, which a flat `extract-min-cost` could not reach.
   Returns {:term :proof :cost} or nil if extraction found nothing usable. `proof` is nil when the
   cheapest term IS `term` (no change)."
  [^Env env st term laws cost-fn]
  (let [thms (ematch/prepare-theorems env laws)
        gs (eg/internalize-binders (eg/mk-grind-state env) term 0 soac-head? 0 binder-descent-depth)
        gs (if (seq thms) (:gs (ematch/run-ematch gs thms #{})) gs)
        rec (try (egproof/extract-and-prove gs st term cost-fn)
                 (catch Throwable _ nil))]
    (when (and rec (:term rec))
      (if (.equals ^Object (:term rec) term)
        {:term term :proof nil :cost (:cost rec)}
        (when (:proof rec)
          {:term (:term rec) :proof (:proof rec) :cost (:cost rec)})))))

(defn- advance
  "Fold one verified rewrite step into the running [term proof] state.
   `step` is {:term :proof} with proof : cur = step.term (proof nil ⇒ no change).
   Composes with the accumulated `acc` (orig = cur) via Eq.trans."
  [st alpha orig [cur acc] step]
  (if (and step (:proof step) (not (.equals ^Object (:term step) cur)))
    [(:term step)
     (if (nil? acc)
       (:proof step)
       (egproof/mk-eq-trans st alpha orig cur (:term step) acc (:proof step)))]
    [cur acc]))

(defn- egraph-step
  "One GATED e-graph pass on `cur`: saturate with `laws`, extract the cheapest materialized member by
   `ecost`, and return the {:term :proof} step iff it BOTH strictly lowers `ecost` AND its proof
   kernel-verifies (`cert/verified-rewrite?`). Returns nil otherwise — so a pass that finds nothing
   better (or whose proof doesn't reconstruct) is a clean no-op. The kernel check is the sole trust
   boundary."
  [^Env env st cur laws ecost lctx]
  (let [r (saturate-once env st cur laws ecost)]
    (when (and r (:proof r) (< (ecost (:term r)) (ecost cur))
               (cert/verified-rewrite? env cur {:term (:term r) :proof (:proof r)} :lctx lctx))
      r)))

(defn saturate-and-extract
  "Saturating cost optimization of pipeline `term`. Each round runs TWO moves, both kernel-proved and
   composed with `Eq.trans` (the split-by-confluence design — simp owns confluent fusion, the e-graph
   owns the non-confluent cost choices):
     1. e-graph cost-search over ALL non-confluent `laws` (hoist + reorder), ITERATED to its own
        fixpoint — each `egraph-step` re-internalizes (with under-binder descent), so multi-step
        cascades (the nested-FAQ inner hoist → outer hoist; reorder-then-hoist) complete here, and
        recursive extraction picks the cheapest equivalent form. No fixed hoist-before-reorder order is
        needed: the e-graph holds every equivalent shape and the cost decides.
     2. simp-fuse/normalize — confluent deforestation + cleanup (`map_map`, `map id → ·`, `zero_add`,
        β). simp OWNS fusion (directed, always-helps, lean4-faithful); it may expose a new hoist that
        the NEXT outer round's e-graph pass picks up.
   Repeats until a fixpoint (no move changes the term) or `:max-rounds`.

   Returns {:term :proof :verified? :changed? :cost :rounds}. `:proof` is a kernel term of type
   `term = result` (nil if unchanged); `:verified?` is the independent kernel check of the COMPOSED
   proof — the value a caller trusts.

   Opts:
     :lctx         free-variable context for an in-progress a/defn body
     :laws         the non-confluent e-graph law set (default `default-laws` = hoist + reorder)
     :selectivity  threaded to `pipeline-cost` (measured profile / refinement bound)
     :sizes        per-source cardinalities, threaded to `pipeline-cost`
     :max-rounds   outer fixpoint cap (default 4)"
  [^Env env term & {:keys [lctx selectivity sizes max-rounds laws]
                    :or {max-rounds 4}}]
  (let [laws (or laws default-laws)
        st (mk-st env lctx)
        cost-fn (fn [t] (cost/pipeline-cost t {:selectivity selectivity :sizes sizes}))
        ;; honest extraction/adopt cost for the e-graph search — LEXICOGRAPHIC (depth, invariant, pipeline):
        ;;   primary   = SOAC-DEPTH cost (a fold under a step-λ pays base^depth) → drives hoists that move a
        ;;               SOAC OUT of a binder (the FAQ hoist, the nested-FAQ OUTER hoist) — the win
        ;;               pipeline-cost can't see (it doesn't descend step-λs);
        ;;   secondary = SOAC-INVARIANT cost (pays base^enclosing-binders-DEPENDED-ON) → drives the
        ;;               nested-FAQ INNER hoist, which is depth-NEUTRAL but makes a subterm loop-invariant,
        ;;               enabling the next outer hoist;
        ;;   tertiary  = pipeline-cost (cardinality) → breaks remaining ties between equal-depth flat
        ;;               reorders (e.g. filter-before-map).
        ;; ε's chosen so depth ≫ invariant ≫ pipeline. SEPARATE from the bare pipeline-cost gate of the
        ;; confluent/factorization path, so that invariant is untouched.
        ecost (fn [t] (+ (cost/soac-depth-cost t)
                         (* 1e-6 (cost/soac-invariant-cost t))
                         (* 1e-12 (cost/pipeline-cost t {:selectivity selectivity :sizes sizes}))))
        alpha (try (tc/infer-type st term) (catch Throwable _ nil))
        finish (fn [cur acc rounds]
                 {:term cur
                  :proof acc
                  :verified? (if (nil? acc)
                               (identical? cur term)
                               (cert/verified-rewrite? env term {:term cur :proof acc} :lctx lctx))
                  :changed? (not (identical? cur term))
                  :cost (cost-fn cur)
                  :rounds rounds})]
    (loop [cur term, acc nil, rounds 0]
      (if (>= rounds max-rounds)
        (finish cur acc rounds)
        (let [;; (1) ONE e-graph pass over ALL non-confluent laws, ITERATED to its own fixpoint (each
              ;; egraph-step re-internalizes with under-binder descent) so multi-step cascades complete
              ;; here; recursive extraction picks the cheapest — no fixed hoist/reorder order needed.
              [cur1 acc1] (loop [c cur, ac acc, i 0]
                            (let [step (egraph-step env st c laws ecost lctx)]
                              (if (and (< i 8) step (:proof step) (not (.equals ^Object (:term step) c)))
                                (let [[c' ac'] (advance st alpha term [c ac] step)]
                                  (recur c' ac' (inc i)))
                                [c ac])))
              ;; (2) simp fuse/normalize the chosen plan (confluent deforestation + cleanup)
              fuse (let [o (cert/optimize env cur1 :lctx lctx)]
                     (when (and (:changed? o) (:verified? o)) o))
              [cur2 acc2] (advance st alpha term [cur1 acc1] fuse)]
          (if (.equals ^Object cur2 cur)
            (finish cur2 acc2 (inc rounds))
            (recur cur2 acc2 (inc rounds))))))))
