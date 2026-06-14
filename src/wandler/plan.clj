(ns wandler.plan
  "Integration 1 — the unified, CONSUMER-AWARE planner. One entry that plans a list-producing pipeline
   end-to-end, source→sink, every plan kernel-certified ≡ the naive query.

   Two ideas, both reusing the existing certified core (optimize-cost / verified-rewrite?):

   1. CONSUMER-AWARENESS by sink-folding. We fold the SINK (what the caller does with the result: count,
      sum, materialize-ordered, …) INTO the pipeline term before optimizing. This makes the certified
      optimizer legalize exactly the consumer-appropriate rewrites with NO extra gate: an order-destroying
      rewrite (join reorder via Map.join_comm, a Perm) only certifies as `Eq` when wrapped in an
      order-invariant consumer (count/sum). So `:count`/`:sum` sinks unlock reorder + pre-aggregation,
      while `:vector` (materialize-ordered) does not — enforced by verified-rewrite? itself, not by a flag.

   2. SOURCE-NATURE oracle dispatch. Each source's cardinality oracle is chosen by its nature:
      materialized (a DB table) → the engine's exact `:estimate` (sizes/selectivity); stream → a forked
      sample (stationary-distribution profile, via wandler.exec.stream — the next slice). Both feed the
      SAME optimize-cost; only the provenance of `:selectivity`/`:sizes` differs.

   This is the seam that ties the inductive (datahike/stratum, finite/exact) and coinductive (live
   streams, sampled/stationary) views together under one certified search."
  (:require [wandler.optimize :as opt]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))

;; ── sink folding: wrap a list-producing pipeline in its consumer term ─────────────────────────────
;; The folded term is what the certified optimizer sees, so the sink's order-(in)variance is what gates
;; the rewrites. Order-invariant sinks (count/sum) admit join-reorder/pre-agg; :vector keeps order.

(defn- count-sink [term elem-type]
  (let [nat (e/const' (nm "Nat") [])
        op  (e/lam "acc" nat (e/lam "x" elem-type (e/app (e/const' (nm "Nat.succ") []) (e/bvar 1)) :default) :default)]
    (e/app* (e/const' (nm "List.foldl") [z z]) nat elem-type op (e/const' (nm "Nat.zero") []) term)))

(defn- sum-sink [term elem-type value-fn value-type]
  (let [nat  (e/const' (nm "Nat") [])
        vt   (or value-type elem-type)
        vals (if value-fn (e/app* (e/const' (nm "List.map") [z z]) elem-type vt value-fn term) term)]
    (e/app* (e/const' (nm "List.foldl") [z z]) vt vt
            (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) vals)))

(defn fold-sink
  "Fold a sink descriptor `{:kind … :value-fn? :value-type?}` into a list-producing `term`
   (element type `elem-type`). Returns the consumer-wrapped term the optimizer should plan."
  [term elem-type sink]
  (case (:kind sink)
    :count               (count-sink term elem-type)
    :sum                 (sum-sink term elem-type (:value-fn sink) (:value-type sink))
    (:vector :materialize nil) term))      ; identity — order preserved; order-destroying rewrites won't certify

(defn order-invariant?
  "Does this sink ignore output order (so join-reorder / pre-aggregation are sound to offer)?"
  [sink]
  (boolean (#{:count :sum :group :set} (:kind sink))))

;; ── source-nature oracle dispatch ─────────────────────────────────────────────────────────────────
(defn- resolve-oracle
  "Pick the cardinality oracle. `sources` = {fvar-id → {:nature … :size … :selectivity …}}. Materialized
   sources contribute exact sizes (the engine estimate). Explicit :sizes/:selectivity override. (Stream
   sampling is the next slice — it would replace :selectivity with a forked-window profile.)"
  [sources sizes selectivity]
  {:sizes (or sizes (not-empty (into {} (keep (fn [[id d]] (when-let [n (:size d)] [id n])) sources))))
   :selectivity selectivity})

(defn unified-plan
  "Plan a list-producing pipeline `term` (element type `:elem-type`) end-to-end for a `:sink`, with sources
   described in `:sources` (fvar-id → {:nature :size}). Folds the sink in, picks the oracle by source
   nature, runs the shared certified optimize-cost. Returns the optimize-cost result augmented with
   `:sink`, `:wrapped` (the consumer-folded term actually optimized), and `:route` (the chosen physical
   strategy, or nil if none — e.g. an order-preserving sink that admits no reorder)."
  [env term & {:keys [lctx elem-type sink sources sizes selectivity memory-budget ndv]
               :or {sink {:kind :vector}}}]
  (let [wrapped (fold-sink term elem-type sink)
        {osz :sizes osel :selectivity} (resolve-oracle (or sources {}) sizes selectivity)
        r (opt/optimize-cost env wrapped :lctx lctx
                             :sizes osz :selectivity osel :memory-budget memory-budget :ndv ndv)]
    (assoc r
           :sink (:kind sink)
           :wrapped wrapped
           :order-invariant? (order-invariant? sink)
           :route (get-in r [:physical :strategy]))))
