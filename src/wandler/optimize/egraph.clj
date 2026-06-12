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
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.ematch :as ematch]
            [ansatz.tactic.grind.proof :as egproof])
  (:import [ansatz.kernel Env]))

(defn- mk-st [^Env env lctx]
  (if (seq lctx) (tc/mk-tc-state-with-locals env lctx) (tc/mk-tc-state env)))

(def default-laws
  "All oriented laws the e-graph saturates with: the confluent fusion set PLUS the
   non-confluent cost/relational reorders. Unlike greedy `optimize-cost`, throwing
   them all in is safe here — the e-graph keeps every equivalent form and extraction
   picks the cheapest, so a reorder that doesn't help is simply not extracted."
  (vec (concat opt/fusion-lemmas opt/cost-rewrites)))

(defn- saturate-once
  "One saturation round on `term`: build a fresh e-graph, internalize, E-match all
   `laws`, extract the cheapest materialized member by `cost-fn`, and build a
   kernel proof `term = extracted` from the e-graph. Returns
   {:term :proof :cost :members} or nil if extraction found nothing better/usable.
   `proof` is nil when the cheapest member IS `term` (no change)."
  [^Env env st term laws cost-fn]
  (let [thms (ematch/prepare-theorems env laws)
        gs (-> (eg/mk-grind-state env) (eg/internalize term 0))
        gs (if (seq thms) (:gs (ematch/run-ematch gs thms #{})) gs)
        best (eg/extract-min-cost gs term cost-fn)]
    (when best
      (if (.equals ^Object (:term best) term)
        {:term term :proof nil :cost (:cost best) :members (:members best)}
        (let [proof (try (egproof/mk-eq-proof gs st term (:term best))
                         (catch Throwable _ nil))]
          (when proof
            {:term (:term best) :proof proof
             :cost (:cost best) :members (:members best)}))))))

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

(defn saturate-and-extract
  "Saturating cost optimization of pipeline `term`. Each round INTERLEAVES two
   complementary moves, both kernel-proved, composed with `Eq.trans`:
     1. simp-fuse — confluent deforestation incl. SUBTERM fusion via congruence
        descent (what the e-graph can't materialize as a top-level parent);
     2. e-graph reorder — saturate with all laws, extract the cheapest equivalent
        MATERIALIZED top-level term by `pipeline-cost` (the non-confluent cost
        choices greedy ordering can miss).
   Repeats until a fixpoint (neither move changes the term) or `:max-rounds`.

   Returns {:term :proof :verified? :changed? :cost :rounds}. `:proof` is a kernel
   term of type `term = result` (nil if unchanged); `:verified?` is the independent
   kernel check of the COMPOSED proof — the value a caller trusts.

   Opts:
     :lctx        free-variable context for an in-progress a/defn body
     :laws        law name set the e-graph saturates with (default `default-laws`)
     :selectivity threaded to `pipeline-cost` (measured profile / refinement bound)
     :max-rounds  outer fixpoint cap (default 4)"
  [^Env env term & {:keys [lctx laws selectivity max-rounds]
                    :or {laws default-laws max-rounds 4}}]
  (let [st (mk-st env lctx)
        cost-fn (fn [t] (opt/pipeline-cost t {:selectivity selectivity}))
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
        (let [;; (1) confluent fusion (simp) — proof cur = fused
              fuse (let [o (opt/optimize env cur :lctx lctx)]
                     (when (and (:changed? o) (:verified? o)) o))
              [cur1 acc1] (advance st alpha term [cur acc] fuse)
              ;; (2) e-graph cost reorder on the fused term — proof cur1 = reordered
              reo (let [r (saturate-once env st cur1 laws cost-fn)]
                    (when (and r (:proof r) (< (:cost r) (cost-fn cur1))
                               (opt/verified-rewrite?
                                env cur1 {:term (:term r) :proof (:proof r)} :lctx lctx))
                      r))
              [cur2 acc2] (advance st alpha term [cur1 acc1] reo)]
          (if (.equals ^Object cur2 cur)
            (finish cur2 acc2 (inc rounds))
            (recur cur2 acc2 (inc rounds))))))))
