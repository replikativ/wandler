(ns wandler.exec.physical
  "Physical backend selection for a BATCH pipeline — the additive layer below wandler.exec.mode/route.
   `route` picks the mode lowering (:batch-fuse vs :async vs :incremental); for :batch-fuse this
   picks the physical REALIZATION over the plan lens (wandler.optimize.plan):

     :eager      — the existing unboxed amapl/apfoldl codegen (the DEFAULT — unchanged).
     :transduce  — a Clojure transducer pipeline (`(into [] (comp (map f) (filter p)) src)`), so a
                   verified pipeline composes with native into/sequence/transduce. The fusion proofs
                   ARE the certificate that this is the same computation.
     :array      — (future) raster preallocated unboxed arrays, gated by the boundedness analysis.

   physical-route is a POST-optimize selector over the plan — it never feeds back into the certified
   search, so it cannot perturb plan choice or the verified-rewrite gate. Default :eager keeps every
   existing path byte-for-byte; the other tags are opt-in until boundedness makes the choice automatic."
  (:require [ansatz.codegen :as cg]
            [wandler.optimize.plan :as plan]))

(defn transducible?
  "Does this plan reduce to a LINEAR producing pipeline (map/filter/filterMap/flatMap over a source,
   ≥1 stage) that plan->transducer can emit? join/group_by/foldl/foldr → no (eager handles those)."
  [plan]
  (and (not= :source (:op plan))
       (loop [p plan]
         (case (:op p)
           :source true
           (:map :filter :filter-map :flat-map) (recur (:input p))
           false))))

;; ── chunkability classifier (the chunked-array model, see docs/OPTIMIZER.md) ──────────────
;; The physical "array" realization is a transducer over fixed-size unboxed chunks + a monoid merge —
;; bounded memory for any input length, the shape stratum/raster share. The boundedness analysis is
;; really CHUNKABILITY: per-op, how does it chunk?

(def chunk-class
  "plan :op → how it chunks. :per-chunk = independent per chunk (map/filter — outputs concat);
   :reduce = per-chunk fold + a MONOID merge (the merge's associativity certificate is gated at emit
   time via runtime/monoid-fold-op); :cross-chunk = needs a hash table across chunks (join/group_by —
   routes to stratum / grace-hash, not the chunked-array kernel)."
  {:map :per-chunk, :filter :per-chunk, :filter-map :per-chunk, :flat-map :per-chunk
   :foldl :reduce, :foldr :reduce
   :join :cross-chunk, :group-by :cross-chunk
   :source :source})

(defn chunkable?
  "Is this plan a chunked-array pipeline — a map/filter/fold chain over a source, so it runs in bounded
   per-chunk passes with a monoid merge? join/group_by need cross-chunk state (→ stratum/grace-hash);
   a bare source has nothing to chunk. The fold's monoid certificate is checked at emit time, not here."
  [plan]
  (and (not= :source (:op plan))
       (loop [p plan]
         (case (:op p)
           :source true
           (:map :filter :filter-map :flat-map :foldl :foldr) (recur (:input p))
           false))))

(defn classify
  "Per-op chunk classes of a (linear) plan, innermost source → outermost op, plus :chunkable?. The
   detail view for explain/cost; :cross-chunk ops (join/group_by) stop the linear walk."
  [plan]
  (loop [p plan, acc ()]
    (let [cls (get chunk-class (:op p) :opaque)]
      (if (or (= :source (:op p)) (#{:cross-chunk :opaque} cls))
        {:classes (vec (cons cls acc)) :chunkable? (chunkable? plan)}
        (recur (:input p) (cons cls acc))))))

;; ── optional chunked-array backend seam ──────────────────────────────────────────────────────────
;; The clojure realization of a chunked-array fold IS the existing apfoldl/amapl eager path (already
;; certified + parallel for monoid folds), so we don't reimplement it. The distinct value of :array is
;; the UNBOXED (raster, per-chunk SIMD/GPU) and COLUMNAR (stratum, OLAP) per-chunk kernels — those plug
;; in here as optional detect-and-lower backends, with eager as the equal-result Clojure fallback. Same
;; pattern as the datahike/stratum LIFT bridge (register-engine!), now for EXECUTION.

(defonce ^:private array-backends (atom []))

(defn register-array-backend!
  "Register an optional chunked-array execution backend: a fn (env plan names) → a Clojure form that
   runs the plan as a chunked-array kernel, or nil to decline. Tried in registration order; first
   non-nil wins. raster (unboxed per-chunk) / stratum (columnar) register here. Returns the count."
  [f] (count (swap! array-backends conj f)))

(defn clear-array-backends! [] (reset! array-backends []) nil)

(defn array-form
  "Run the registered array backends over a CHUNKABLE plan — first non-nil form wins; nil if none
   apply (the caller falls back to the eager/apfoldl Clojure realization, which is result-equal)."
  [env plan names]
  (when (chunkable? plan)
    (some (fn [f] (f env plan names)) @array-backends)))

;; ── cost-based physical push-down (B2 of COST_MODEL_REDESIGN — the engine-transparency seam) ──────
;; `array-form` above fires the FIRST backend that recognizes the shape — no cost comparison. The
;; cost-backend registry instead lets each engine ADVERTISE a cost for the shapes it handles, so the
;; planner picks the cheapest lowering that actually beats the eager Clojure cost. This is what makes
;; raster/stratum TRANSPARENT to the planner: their cost is consulted, not assumed. Every backend is
;; result-equal (the kernel proof of the optimized plan is the certificate), so the choice is purely
;; performance. An engine's :cost is naturally backed by its op-cost descriptor (register-op-cost!).
(defonce ^:private cost-backends (atom []))

(defn register-cost-backend!
  "Register a COST-BASED execution backend: {:name kw, :lower (fn [env plan names] → clj-form | nil
   if the shape isn't handled), :cost (fn [plan eager-cost] → number, the engine's estimated cost for
   this plan; `eager-cost` is the Clojure realization's cost, so a backend can advertise relative, e.g.
   a SIMD ≈ eager/4)}. Costs must be defined even for unsupported shapes; :lower declines those.
   Replaces an existing entry with the same :name, preserving other backends. Returns the count."
  [backend]
  (count (swap! cost-backends
                (fn [backends]
                  (conj (into [] (remove #(= (:name %) (:name backend))) backends)
                        backend)))))

(defn clear-cost-backends! [] (reset! cost-backends []) nil)
(defn cost-backends* [] @cost-backends)

(defn choose-cost-form
  "Cost-based physical push-down. Among registered cost-backends whose `:lower` RECOGNIZES `plan`
   (returns non-nil), pick the cheapest by `:cost`; return it iff strictly cheaper than `eager-cost`
   (the Clojure realization's pipeline-cost, computed by the caller from the plan's kernel term).
   Estimates costs before lowering; lowers affordable candidates in cost order until one recognizes
   the shape. Returns {:backend :form :cost} or nil → eager fallback. A certified term rewrite does
   not verify backend code: each lowering must honor its execution and numerical contract."
  [env plan names eager-cost]
  (let [cands (->> @cost-backends
                   (map (fn [b] (assoc b :estimated-cost
                                       (double ((:cost b) plan eager-cost)))))
                   (filter #(< (:estimated-cost %) (double eager-cost)))
                   (sort-by :estimated-cost))]
    ;; Lowering may compile a native kernel. Do it only for affordable candidates,
    ;; in cost order, and stop as soon as a backend recognizes the plan.
    (some (fn [b]
            (when-let [form ((:lower b) env plan names)]
              {:backend (:name b) :form form :cost (:estimated-cost b)}))
          cands)))

(defn physical-route
  "Choose a physical backend tag for a batch `plan`. Default :eager (unchanged current behavior).
   :transduce when requested AND the plan is a linear producing pipeline; :array when requested AND the
   plan is chunkable (a map/filter/fold chain — the chunked-array realization, served by a registered
   array backend or the eager fallback). Cost + boundedness will make the choice automatic; for now the
   non-default tags are opt-in via `:requested`."
  [plan & {:keys [requested]}]
  (cond
    (and (= requested :array)     (chunkable? plan))    :array
    (and (= requested :transduce) (transducible? plan)) :transduce
    :else :eager))

(defn- xf-comp [xfs]
  (cond (empty? xfs) nil, (= 1 (count xfs)) (first xfs), :else (apply list 'clojure.core/comp xfs)))

(defn- linear-stages
  "Walk a linear plan into {:src <source form> :xfs [transducer forms, outermost LAST]} (via the
   plan-lens fields), codegen'ing the source + leaf fns with the binder-name stack `names`. nil if a
   non-linear op (join/group_by/foldl) is hit."
  [env plan names]
  (loop [p plan, xfs ()]
    (case (:op p)
      :source     {:src (cg/ansatz->clj env (:term p) names) :xfs (vec xfs)}
      :map        (recur (:input p) (cons (list 'clojure.core/map    (cg/ansatz->clj env (:fn p)   names)) xfs))
      :filter     (recur (:input p) (cons (list 'clojure.core/filter (cg/ansatz->clj env (:pred p) names)) xfs))
      ;; filterMap's fn returns Option β = value-or-nil at runtime → `keep` drops the nils.
      :filter-map (recur (:input p) (cons (list 'clojure.core/keep   (cg/ansatz->clj env (:fn p)   names)) xfs))
      :flat-map   (recur (:input p) (cons (list 'clojure.core/mapcat (cg/ansatz->clj env (:fn p)   names)) xfs))
      nil)))

(defn plan->transducer
  "Emit a Clojure transducer-pipeline FORM for a linear producing plan: `(into [] (comp xf…) src)`.
   `names` is the binder-name stack so bvar sources / free vars in the leaf fns codegen correctly.
   Returns nil for non-linear or bare-source plans (the caller falls back to the eager backend).
   The single materialize via `into` keeps it a fused single pass while composing with native xforms."
  [env plan names]
  (when-let [{:keys [src xfs]} (linear-stages env plan names)]
    (when (seq xfs)
      (list 'clojure.core/into [] (xf-comp xfs) src))))
