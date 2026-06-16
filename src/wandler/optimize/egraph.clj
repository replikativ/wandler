;; E-graph search layer for the verified optimizer (roadmap item B).
;;
;; The greedy `optimize-cost` commits to cost-rewrites one at a time, each of which
;; must STRICTLY lower cost in isolation — so it misses combinations where a rewrite
;; is individually cost-neutral (or slightly worse) but jointly enables a cheaper
;; plan. This layer instead does EQUALITY SATURATION: load the pipeline + all our
;; oriented laws into grind's e-graph, saturate via E-matching, then EXTRACT the
;; cheapest equivalent term by `pipeline-cost`.
;;
;; SOUNDNESS is unchanged and rests entirely on the kernel. The e-graph is an
;; untrusted SEARCH oracle: it only decides WHICH term to keep. The certificate is
;; grind's `mk-eq-proof` (a CIC proof `orig = extracted` built by walking the
;; e-graph's transitivity chain) re-checked independently by `verified-rewrite?`.
;; Extraction is restricted to MATERIALIZED in-class members (terms actually present
;; as e-graph nodes), so the proof chain always exists — no synthesized terms.
;;
;; Cross-generation cascades (a law firing on another law's output) are blocked
;; within one saturation by grind's gen=0 E-match gate (loop guard). We recover full
;; saturation with an OUTER FIXPOINT: re-saturate on the extracted term and compose
;; the per-round proofs with `Eq.trans`. Every round is independently kernel-checked.

(ns wandler.optimize.egraph
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [wandler.optimize :as opt]
            [wandler.optimize.cost :as cost]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.ematch :as ematch]
            [ansatz.tactic.grind.proof :as egproof])
  (:import [ansatz.kernel Env]))

(defn- mk-st [^Env env lctx]
  (if (seq lctx) (tc/mk-tc-state-with-locals env lctx) (tc/mk-tc-state env)))

(def hoist-laws
  "FAQ loop-invariant HOIST + sum-semiring LINEARITY laws (installed by
   `wandler.laws.relational/install!`; any not yet installed are silently skipped by
   `prepare-theorems`). These fire PRE-fusion: `sum_map_mul_const` pulls an x-free factor out of a
   sum, which needs the unfused `map (λx. f x * c)` shape — simp fusion would collapse `foldl(map …)`
   and destroy it. So the e-graph runs these BEFORE simp in `saturate-and-extract`."
  ["List.sum_map_mul_const" "List.sum_map_const_mul"
   "List.sum_map_add_distrib" "List.sum_map_zero" "List.foldl_add_pull"])

(def reorder-laws
  "Relational/cardinality REORDERS (`opt/cost-rewrites` — filter↔map, filter→join pushdown, …). These
   are non-confluent cost choices that work on the FUSED form, so the e-graph runs them AFTER simp.
   Keeping them separate from `hoist-laws` matters: a cardinality reorder fired pre-fusion can separate
   two adjacent `map`s and block simp's `map_map` fusion (the interleaved fuse-then-reorder case)."
  (vec opt/cost-rewrites))

(def default-laws
  "Union of the e-graph's non-confluent law sets (`hoist-laws` + `reorder-laws`) — the full set a
   caller gets if they pass `:laws` explicitly. The default pipeline does NOT use this single set; it
   runs hoist-laws pre-fusion and reorder-laws post-fusion (see `saturate-and-extract`). Confluent
   fusion (`opt/fusion-lemmas`) is NOT here — that's simp's job. (simp ≈ lean4 Meta/Tactic/Simp
   normalizer; the e-graph cost-extraction is the egg-style search layer on the grind congruence core.)"
  (vec (concat hoist-laws reorder-laws)))

(defn- saturate-once
  "One saturation round on `term`: build a fresh e-graph, internalize, E-match all `laws`, then
   RECURSIVELY extract the cheapest equivalent term by `cost-fn` together with its kernel proof
   `term = extracted` (`proof/extract-and-prove`, #35). Recursive (egg-style) extraction rebuilds the
   ENCLOSING term from a rewritten subterm — so a rewrite that fires under an application (e.g. a
   loop-invariant hoist in-context) is extractable, which flat `extract-min-cost` could not reach.
   Returns {:term :proof :cost} or nil if extraction found nothing usable. `proof` is nil when the
   cheapest term IS `term` (no change)."
  [^Env env st term laws cost-fn]
  (let [thms (ematch/prepare-theorems env laws)
        gs (-> (eg/mk-grind-state env) (eg/internalize term 0))
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
   kernel-verifies (`verified-rewrite?`). Returns nil otherwise — so a pass that finds nothing better
   (or whose proof doesn't reconstruct) is a clean no-op. The kernel check is the sole trust boundary."
  [^Env env st cur laws ecost lctx]
  (let [r (saturate-once env st cur laws ecost)]
    (when (and r (:proof r) (< (ecost (:term r)) (ecost cur))
               (opt/verified-rewrite? env cur {:term (:term r) :proof (:proof r)} :lctx lctx))
      r)))

(defn saturate-and-extract
  "Saturating cost optimization of pipeline `term`. Each round runs THREE moves IN ORDER, all
   kernel-proved, composed with `Eq.trans` — the order encodes the split-by-confluence design and the
   fact that different non-confluent laws need different shapes:
     1. e-graph HOIST (`hoist-laws`) on the SHAPE-PRESERVING (unfused) term — a loop-invariant hoist
        needs the unfused `map (λx. f x * c)` shape that simp fusion would collapse, so it runs FIRST.
        Ranked by the honest SOAC-DEPTH cost (charges base^depth for a fold under a map step-λ — the
        win pipeline-cost can't see, since it doesn't descend step-λs).
     2. simp-fuse — confluent deforestation (congruence-descent SUBTERM fusion). simp OWNS fusion
        (directed, always-helps); e.g. fuses adjacent maps and cleans up `map id xs → xs`.
     3. e-graph REORDER (`reorder-laws` = cardinality reorders) on the FUSED term — these work on the
        fused shape, and running them pre-fusion could separate adjacent maps and block step 2's fusion.
   Repeats until a fixpoint (no move changes the term) or `:max-rounds`. When recursive extraction
   (#35) lands, steps 1+3 collapse into one all-laws e-graph pass (no fixed order needed).

   Returns {:term :proof :verified? :changed? :cost :rounds}. `:proof` is a kernel
   term of type `term = result` (nil if unchanged); `:verified?` is the independent
   kernel check of the COMPOSED proof — the value a caller trusts.

   Opts:
     :lctx         free-variable context for an in-progress a/defn body
     :hoist-laws   pre-fusion e-graph law set (default `hoist-laws`)
     :reorder-laws post-fusion e-graph law set (default `reorder-laws`)
     :selectivity  threaded to `pipeline-cost` (measured profile / refinement bound)
     :max-rounds   outer fixpoint cap (default 4)"
  [^Env env term & {:keys [lctx selectivity max-rounds]
                    hlaws :hoist-laws rlaws :reorder-laws
                    :or {max-rounds 4}}]
  (let [hlaws (or hlaws hoist-laws)
        rlaws (or rlaws reorder-laws)
        st (mk-st env lctx)
        cost-fn (fn [t] (opt/pipeline-cost t {:selectivity selectivity}))
        ;; honest extraction/adopt cost for the e-graph search — LEXICOGRAPHIC (depth, pipeline):
        ;;   primary   = SOAC-DEPTH cost (a fold under a step-λ pays base^depth) → ranks a loop-invariant
        ;;               HOIST strictly cheaper, the win pipeline-cost can't see (it doesn't descend step-λs);
        ;;   secondary = pipeline-cost (cardinality) → breaks ties between flat reorders of EQUAL depth
        ;;               (e.g. filter-before-map), the win depth-cost can't see.
        ;; Encoded as `depth + ε·pipeline` so depth dominates and pipeline only decides equal-depth plans.
        ;; ε small enough that any genuine depth difference (≥1) outweighs any pipeline difference. Kept
        ;; SEPARATE from the bare pipeline-cost gate of the confluent/factorization path (invariant intact).
        ecost (fn [t] (+ (cost/soac-depth-cost t)
                         (* 1e-9 (opt/pipeline-cost t {:selectivity selectivity}))))
        alpha (try (tc/infer-type st term) (catch Throwable _ nil))
        finish (fn [cur acc rounds]
                 {:term cur
                  :proof acc
                  :verified? (if (nil? acc)
                               (identical? cur term)
                               (opt/verified-rewrite? env term {:term cur :proof acc}
                                                      :lctx lctx))
                  :changed? (not (identical? cur term))
                  :cost (cost-fn cur)
                  :rounds rounds})]
    (loop [cur term, acc nil, rounds 0]
      (if (>= rounds max-rounds)
        (finish cur acc rounds)
        (let [;; (1) e-graph HOIST on the UNFUSED term (needs the pre-fusion map(λ.f x*c) shape)
              [cur1 acc1] (advance st alpha term [cur acc]
                                   (egraph-step env st cur hlaws ecost lctx))
              ;; (2) confluent fusion (simp) on the chosen plan — proof cur1 = fused
              fuse (let [o (opt/optimize env cur1 :lctx lctx)]
                     (when (and (:changed? o) (:verified? o)) o))
              [cur2 acc2] (advance st alpha term [cur1 acc1] fuse)
              ;; (3) e-graph cardinality REORDER on the FUSED term (works on the fused shape)
              [cur3 acc3] (advance st alpha term [cur2 acc2]
                                   (egraph-step env st cur2 rlaws ecost lctx))]
          (if (.equals ^Object cur3 cur)
            (finish cur3 acc3 (inc rounds))
            (recur cur3 acc3 (inc rounds))))))))
