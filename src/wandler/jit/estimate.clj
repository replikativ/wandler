(ns wandler.jit.estimate
  "Cost-PARAMETER estimation — the ONE seam where DATA informs the inductive plan. The planner's cost
   model reads exactly three workload knobs: :sizes (per-source cardinality), :selectivity (filter
   pass-rates), :ndv (distinct join-key values). This ns measures them from a sample and FUSES them with
   refinement-derived PRIORS into the map `optimize-cost` consumes.

   The framing: a malli refinement / type is a PRIOR on a cost knob ([:enum a b c] → ndv ≤ 3; a bounded
   sequential → size ≤ N; a PK → ndv = |table|); a measurement is EVIDENCE; the fused result is the
   POSTERIOR the planner selects against. The kernel certifies every candidate plan, so a wrong posterior
   costs SPEED, never correctness — the inductive layer owns soundness, this layer owns cost selection.

   For a coinductive stream this is not just optimization but NECESSARY: an infinite source has no
   inductive size, so a measured size/ndv is the only way it becomes cost-plannable. See verified-stream-jit."
  (:require [ansatz.core :as a]
            [wandler.core :as wcore]
            [ansatz.kernel.expr :as e]))

(defn measure-size
  "Observed cardinality of a `sample` (a window / sampled prefix of the source)."
  [sample]
  (max 1.0 (double (count sample))))

(defn measure-ndv
  "Observed distinct-value count of join key `keyfn` (an `α → K` kernel lambda) over `sample` — the
   knob the join-factorization / pre-aggregated-index gates turn on (worth it iff ndv ≪ |source|).
   Compiles the kernel keyfn and counts distinct results."
  [env keyfn sample]
  (let [k (eval (a/ansatz->clj env keyfn []))]
    (max 1.0 (double (count (into #{} (map k) sample))))))

(defn cost-params
  "Fuse refinement PRIORS ⊕ measured EVIDENCE into the {:sizes :selectivity :ndv} `optimize-cost`
   consumes — the posterior the planner selects against.

   `obs` keys (all optional):
     :priors      a base {:sizes :selectivity :ndv} from refinements/types (the prior; filled first)
     :sample      a representative seq of compiled source values → measures :selectivity (every filter
                  predicate in `term`) and, with :key-of, :ndv
     :key-of      the join key kernel lambda (α → K) whose distinct count is the :ndv evidence
     :source-id   the fvar id whose :sizes entry the sample's size updates
   Evidence overrides the prior where present; the prior covers the rest."
  [env term {:keys [priors sample key-of source-id]}]
  (cond-> (or priors {})
    (seq sample)
    (assoc :selectivity (merge (:selectivity priors)
                               (wcore/profile-selectivity env term sample)))
    (and (seq sample) source-id)
    (update :sizes assoc source-id (measure-size sample))
    (and (seq sample) key-of)
    (assoc :ndv (measure-ndv env key-of sample))))
