(ns wandler.exec.physical
  "Physical backend selection for a BATCH pipeline — the additive layer below wandler.exec.mode/route.
   `route` picks the mode lowering (:batch-fuse vs :reactive vs :incremental); for :batch-fuse this
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

;; ── chunkability classifier (the chunked-array model, see docs/PHYSICAL_PLANNER.md) ──────────────
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

(defn physical-route
  "Choose a physical backend tag for a batch `plan`. Default :eager (unchanged current behavior).
   :transduce when explicitly requested AND the plan is a linear producing pipeline. (The :array tag —
   the chunked-array realization — lands with its backend; chunkable?/classify already gate it. Cost +
   boundedness will make the choice automatic; for now the non-default tags are opt-in via `:requested`.)"
  [plan & {:keys [requested]}]
  (if (and (= requested :transduce) (transducible? plan)) :transduce :eager))

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
