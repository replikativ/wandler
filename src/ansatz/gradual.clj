(ns ansatz.gradual
  "The GRADUAL-TYPING → GRADUAL-OPTIMIZATION front door. Start with a pipeline and *no* annotations;
   add Malli schemas, then cardinality / selectivity / ndv estimates, and watch the certified planner
   unlock more optimization at each tier. Every plan is kernel-certified equivalent to the original —
   richer annotations change only the PLAN, never the result.

   Three entry points over `ansatz.optimize`:
     (plan env term & opts)        — one call: optimize + `explain` the chosen plan.
     (gradient env term lctx tiers)— run the planner at increasing annotation tiers; report what each
                                     tier UNLOCKS (the legible 'more typing ⇒ more optimization' story).
     (coach env term lctx)         — analyze the pipeline and suggest which annotation would unlock
                                     which rewrite, *empirically* (it tries each and reports the delta).

   The annotation tiers map to the type/stat evidence the planner needs:
     • Malli `:map` schemas        → field types + the join KEY  ⇒ relational rewrites (pushdown, join)
     • `:sizes` (per-source card.) → cost numbers               ⇒ join reorder, physical strategy
     • `:ndv` (distinct-key est.)  → DuckDB-style gating         ⇒ the pre-aggregated index
     • `:memory-budget`            → resource bound              ⇒ hash / nested-loop / grace-hash
     • `:selectivity` (or a sample, via optimize-measured)       ⇒ measured replanning (JIT)"
  (:require [ansatz.core :as a]
            [ansatz.optimize :as opt]
            [ansatz.plan :as plan]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [clojure.set :as set]
            [clojure.string :as str]))

(declare report)

(defn- const-names
  "The set of constant head-names occurring in `term` (for feature detection)."
  [term]
  (let [acc (volatile! #{})]
    (letfn [(go [t]
              (cond
                (e/const? t) (vswap! acc conj (name/->string (e/const-name t)))
                (e/app? t) (do (go (e/app-fn t)) (go (e/app-arg t)))
                (e/lam? t) (do (go (e/lam-type t)) (go (e/lam-body t)))
                (e/forall? t) (do (go (e/forall-type t)) (go (e/forall-body t)))))]
      (go term))
    @acc))

;; ── standard Clojure → {:term :lctx} : the surface the planner consumes ─────────────────────────
(defn elaborate
  "Elaborate a TYPED CLOJURE pipeline into `{:term :lctx}` ready for the planner. `params` is an
   a/defn-style binder vector `[name :- TypeForm, …]`; the params become FREE fvars (so the planner's
   lctx ranges over the data sources) and `body` — standard Clojure — is elaborated open over them.
   Idiomatic pipelines flow straight in: `(->> custs (filter #(< 1 (:age %))) (map :id))`,
   `(reduce + 0 (map :amount (join …)))`, etc. This is the bridge from 'standard Clojure + annotations'
   to the certified planner."
  [env params body]
  (let [pairs (a/parse-params params)
        lam   (binding [a/*current-lctx* {}] (a/build-telescope env {} 0 pairs body e/lam))]
    (loop [t lam, fid 4000000, lctx {}]
      (if (e/lam? t)
        (recur (e/instantiate1 (e/lam-body t) (e/fvar fid)) (inc fid)
               (assoc lctx fid {:name (e/lam-name t) :type (e/lam-type t) :tag :local}))
        {:term t :lctx lctx}))))

(defn- by-name
  "Translate an annotation map keyed by PARAM NAME into one keyed by fvar-id (using `lctx`)."
  [lctx m]
  (when m (into {} (for [[k v] m] [(some (fn [[id d]] (when (= (str k) (:name d)) id)) lctx) v]))))

(defn- name-keyed-opts [lctx opts]
  (cond-> opts (:sizes opts) (update :sizes #(by-name lctx %)) (:ndv opts) (update :ndv #(by-name lctx %))))

(defn report-clj
  "The one-call gradual surface from STANDARD CLOJURE: elaborate `(params, body)` and render the full
   report (plan tree + gradient + coach). Each tier's `opts` may key `:sizes`/`:ndv` by PARAM NAME
   (translated internally), so callers never touch fvar ids. E.g.
     (report-clj env '[xs :- (List Nat) ys :- (List Nat)]
                     '(count (join (fn [x :- Nat] x) (fn [y :- Nat] y) xs ys))
                     [[\"untyped\" {}] [\"+ sizes\" {:sizes {\"xs\" 100 \"ys\" 1e6}}]])"
  [env params body tiers]
  (let [{:keys [term lctx]} (elaborate env params body)]
    (report env term lctx (for [[label opts] tiers] [label (name-keyed-opts lctx opts)]))))

(defn plan
  "Optimize `term` under the given annotations and return the certified result enriched for humans:
   {:term :verified? :rewrites :physical :cost :explain}. `opts` are the `optimize-cost` keys
   (:lctx :sizes :selectivity :ndv :memory-budget …)."
  [env term & {:as opts}]
  (let [res (apply opt/optimize-cost env term (mapcat identity opts))]
    (assoc res :explain (opt/explain res))))

(defn gradient
  "Run the planner at INCREASING annotation tiers and report what each tier unlocks. `tiers` is an
   ordered seq of `[label opts-map]` (opts ACCUMULATE conceptually; pass the full opts each tier).
   `lctx` is shared. Returns a seq of {:tier :rewrites :strategy :cost :verified? :gained}, where
   :gained is the set of rewrites newly unlocked vs. the previous tier — the optimization GRADIENT."
  [env term lctx tiers]
  (first
   (reduce (fn [[out prev] [label opts]]
             (let [res (apply opt/optimize-cost env term :lctx lctx (mapcat identity opts))
                   rw (set (:rewrites res))]
               [(conj out {:tier label :rewrites (vec (:rewrites res))
                           :strategy (get-in res [:physical :strategy])
                           :cost (:cost res) :verified? (:verified? res)
                           :gained (vec (set/difference rw prev))})
                rw]))
           [[] #{}] tiers)))

(defn render-gradient
  "A human-readable string for `gradient` output — the 'annotate ⇒ optimize' ladder."
  [grad]
  (clojure.string/join "\n"
    (for [{:keys [tier rewrites strategy cost verified? gained]} grad]
      (format "  %-22s → %-28s %s%s"
              (str tier)
              (str (or (seq rewrites) "(fused only)"))
              (if verified? "✓" "✗")
              (if (seq gained) (str "   +unlocked " (vec gained)) "")))))

(defn coach
  "Analyze `term` and EMPIRICALLY suggest annotations that would unlock more optimization — the
   gradual-typing feedback loop. For each candidate annotation it re-plans and, if new rewrites appear,
   reports them. Returns a seq of {:annotation :unlocks :note}. `base-opts` is the current annotation
   set (defaults to none beyond lctx)."
  [env term lctx & {:keys [base-opts] :or {base-opts {}}}]
  (let [cs (const-names term)
        base (set (:rewrites (apply opt/optimize-cost env term :lctx lctx (mapcat identity base-opts))))
        has? (fn [n] (contains? cs n))
        ;; candidate annotations to probe, each with the opts it adds and a note
        cands (cond-> []
                (has? "Map.join")
                (conj {:annotation :sizes
                       :opts {:sizes (zipmap (keys lctx) (repeat 1000.0))}
                       :note "per-source cardinalities ⇒ cost-based join reorder / physical strategy"})
                (has? "Map.join")
                (conj {:annotation :ndv
                       :opts {:ndv (zipmap (keys lctx) (repeat 4.0))}
                       :note "distinct-key estimate (HLL / datahike schema) ⇒ pre-aggregated index for a separable sum"})
                (has? "Map.join")
                (conj {:annotation :memory-budget
                       :opts {:memory-budget 1.0 :sizes (zipmap (keys lctx) (repeat 1000.0))}
                       :note "a memory bound ⇒ spill (grace-hash) / nested-loop instead of the in-memory hash"})
                (has? "List.filter")
                (conj {:annotation :selectivity
                       :opts {:selectivity {} :sizes (zipmap (keys lctx) (repeat 1000.0))}
                       :note "measured filter pass-rates (a data sample, via optimize-measured) ⇒ JIT replanning"}))]
    (->> cands
         (keep (fn [{:keys [annotation opts note]}]
                 (let [rw (set (:rewrites (apply opt/optimize-cost env term :lctx lctx
                                                 (mapcat identity (merge base-opts opts)))))
                       gained (set/difference rw base)]
                   (when (seq gained)
                     {:annotation annotation :unlocks (vec gained) :note note}))))
         vec)))

(defn render-coach
  "A human-readable string for `coach` output."
  [suggestions]
  (if (empty? suggestions)
    "  (no further annotations would change the plan)"
    (str/join "\n"
      (for [{:keys [annotation unlocks note]} suggestions]
        (format "  + add %-14s ⇒ unlocks %-26s  %s" (str annotation) (str (vec unlocks)) note)))))

(defn report
  "One-call legible REPORT for a pipeline: the chosen plan (tree + strategy + certificate), the
   annotation GRADIENT, and the COACH suggestions — the whole gradual-typing surface in one string.
   `tiers` (ordered [label opts]) drives the gradient; the LAST tier is taken as the current/best
   annotation set for the chosen-plan view and the coach baseline."
  [env term lctx tiers]
  (let [[_ best-opts] (last tiers)
        res (apply opt/optimize-cost env term :lctx lctx (mapcat identity best-opts))
        grad (gradient env term lctx tiers)
        sugg (coach env term lctx :base-opts best-opts)]
    (str "CHOSEN PLAN  " (plan/plan->str (plan/term->plan (:term res))) "\n"
         (opt/explain res) "\n\n"
         "GRADIENT (more annotations ⇒ more optimization):\n" (render-gradient grad) "\n\n"
         "COACH (annotate next):\n" (render-coach sugg))))
