(ns wandler.infer
  "Sample-driven schema + refinement inference at the data-ingestion boundary.

   `malli.provider` (metosin) already recovers the STRUCTURE of a relation from a sample — and
   deliberately stays LOOSE (a minimal schema all values validate against; it never tightens to the
   sample's observed extremes). This namespace delegates the structural pass to `mp/provide` and adds
   the VALUE-LEVEL refinements it omits — the facts that actually drive the wandler planner — split
   into two lanes by HOW a wrong inference manifests:

     • GUARDED SOUND lane — unique-key / FD candidates. A collision-free field is a *candidate* key,
       never a fact: a high-cardinality non-key (e.g. a name) can look unique on a sample. So these go
       to `wandler.adaptive`, which builds a `Subtype`-refined carrier, KERNEL-CERTIFIES the rewrite
       under the key, GUARDS the key at the runtime boundary, and deopts to the original plan if it is
       violated. A wrong candidate costs a missed optimization, never a wrong answer.

     • ADVISORY PRIOR lane — numeric ranges, ndv, low-cardinality domains. These feed
       `wandler.jit.estimate/cost-params` as PRIORS fused with measured evidence. The kernel certifies
       every candidate plan, so a wrong prior costs SPEED, never correctness — it only mis-ranks
       equivalent plans.

   The enriched schema also round-trips back into a malli schema that `ansatz.malli/schema->type-expr`
   already lifts to `Subtype` refinements — so a sample-inferred refinement rides the EXACT same path
   as a declared one (no new kernel machinery). The refined schema always validates the sample it was
   built from (observed bounds contain the sample by construction)."
  (:require [malli.core :as m]
            [malli.provider :as mp]))

;; ── per-field profiling ──────────────────────────────────────────────────────────────────────────
(defn field-profile
  "Profile field `k` over `rows`. `:unique-key?` is a CANDIDATE (collision-free in the sample), not a
   fact — the guarded consumer (wandler.adaptive) discharges it. `:range-prior`/`:len-prior` are
   one-sidedly-too-tight (a sample never exceeds the true domain) → advisory only. `small-domain` (≤
   `:small-domain-max`) marks a good low-ndv join key."
  [rows k & {:keys [small-domain-max] :or {small-domain-max 16}}]
  (let [n    (count rows)
        vs   (map #(get % k) rows)
        nums (filter number? vs)
        strs (filter string? vs)
        ndv  (count (distinct vs))]
    (cond-> {:ndv ndv
             :ndv-ratio   (double (/ ndv (max 1 n)))
             :unique-key? (= ndv n)}                       ; collision-free over the sample
      ;; Nonfinite values have no useful ordered range contract. In particular,
      ;; NaN bounds reject even the sample that produced them.
      (and (seq nums)
           (every? #(cond
                      (instance? Double %) (Double/isFinite (double %))
                      (instance? Float %) (Float/isFinite (float %))
                      :else true)
                   nums))
      (assoc :range-prior {:min (reduce min nums) :max (reduce max nums)})
      (seq strs) (assoc :len-prior   {:min (reduce min (map count strs))
                                      :max (reduce max (map count strs))})
      (<= ndv small-domain-max)
      (assoc :small-domain
             (let [values (distinct vs)]
               (try (vec (sort values))
                    (catch ClassCastException _ (vec (sort-by pr-str values)))))))))

(defn- map-fields
  "The field keys of a `mp/provide` `[:map [k schema]…]` structure, else nil."
  [structure]
  (when (and (vector? structure) (= :map (first structure)))
    (map first (rest structure))))

(defn profile
  "Profile a relation `rows` (a seq of maps). Returns
     {:structure <mp/provide schema> :n <count> :fields {k <field-profile>…}}.
   For non-map rows only `:structure`/`:n` are returned (no per-field refinements)."
  [rows & opts]
  (let [structure (mp/provide rows)
        n         (count rows)]
    (cond-> {:structure structure :n n}
      (map-fields structure)
      (assoc :fields (into {} (for [k (map-fields structure)]
                                [k (apply field-profile rows k opts)]))))))

;; ── lane 1: GUARDED SOUND — unique-key candidates → wandler.adaptive ──────────────────────────────
(defn key-candidates
  "The fields that are collision-free over the sample — unique-key CANDIDATES for the guarded
   group-by/distinct elimination path (wandler.adaptive). Optionally require a minimum sample size
   (`:min-n`) before proposing any (a candidate from n=3 is weak); default 1 (propose; the runtime
   guard is the real filter)."
  [profiled & {:keys [min-n] :or {min-n 1}}]
  (if (< (:n profiled) min-n)
    []
    (vec (for [[k f] (:fields profiled) :when (:unique-key? f)] k))))

;; ── lane 2: ADVISORY PRIOR — ranges/ndv → wandler.jit.estimate/cost-params ────────────────────────
(defn cost-priors
  "A `:priors` map for `wandler.jit.estimate/cost-params`: `{:sizes {source-id n} :ndv <distinct of
   join-key field>}`. `:source-id` is the fvar id of the relation source; `:join-key` is the field
   whose distinct-count seeds the `:ndv` prior (omit → no `:ndv`)."
  [profiled & {:keys [source-id join-key]}]
  (cond-> {}
    source-id (assoc :sizes {source-id (double (:n profiled))})
    (and join-key (get-in profiled [:fields join-key :ndv]))
    (assoc :ndv (double (get-in profiled [:fields join-key :ndv])))))

;; ── round-trip: enriched profile → a refined malli schema (rides ansatz.malli unchanged) ──────────
(defn refined-schema
  "Tighten the structural `mp/provide` schema with the sample-inferred refinements (numeric ranges,
   string lengths) → a malli schema `ansatz.malli/schema->type-expr` lifts to `Subtype` refinements.
   The result ALWAYS validates the sample (observed bounds contain it by construction). The refinements
   are tagged `::source :sample-prior` so a consumer can tell inferred bounds from declared ones —
   treat them as priors, not hard contracts, until confirmed."
  [profiled]
  (if-let [_ (map-fields (:structure profiled))]
    (into [:map]
          (for [[k entry-schema & more] (rest (:structure profiled))
                :let [entry-options (when (seq more) entry-schema)
                      base (if (seq more) (first more) entry-schema)
                      f (get-in profiled [:fields k])
                      refined (cond
                 ;; Preserve the provider's numerical carrier. A Float sample must
                 ;; not become an :int schema that rejects the very data we profiled.
                                (and (:range-prior f)
                                     (contains? #{:int :double :float :number}
                                                (if (vector? base) (first base) base)))
                                [(if (vector? base) (first base) base)
                                 (merge (when (and (vector? base) (map? (second base))) (second base))
                                        (:range-prior f) {::source :sample-prior})]
                                (and (:len-prior f) (= :string (if (vector? base) (first base) base)))
                                [:string (merge (when (and (vector? base) (map? (second base))) (second base))
                                                (:len-prior f) {::source :sample-prior})]
                                :else base)]]
            (if entry-options [k entry-options refined] [k refined])))
    (:structure profiled)))

;; ── one-call front door ──────────────────────────────────────────────────────────────────────────
(defn infer
  "Profile `rows` and return everything a planner needs:
     {:structure :n :fields :key-candidates :refined-schema}
   `:key-candidates` → the GUARDED sound lane (wandler.adaptive); `:refined-schema` carries the
   advisory range/length refinements (rides ansatz.malli); `cost-priors` builds the `cost-params`
   prior on demand (needs the source fvar id). Opts forward to `field-profile`/`key-candidates`."
  [rows & opts]
  (let [p (apply profile rows opts)]
    (assoc p
           :key-candidates (apply key-candidates p opts)
           :refined-schema (refined-schema p))))

(defn induce-types!
  "DATA-FIRST type induction — the on-ramp that lets you skip hand-written `a/defn` annotations.
   Infer a malli FUNCTION schema for the plain Clojure fn `fvar` from `sample-args` (the return type is
   inferred by RUNNING `fvar` on them), and register it via malli's `=>` registry, so a subsequent
   `(a/defn <same name> [bare args] body)` IN THE SAME NAMESPACE picks up the kernel types automatically.

   Each sequential arg of records → `[:sequential <inferred element schema>]` (`:refined? true` uses the
   range-refined schema, so declared/inferred ranges sharpen the planner's selectivity); other args and
   the return go through `mp/provide`. Returns the registered `[:=> [:cat …] ret]` schema.

   `f` is either a VAR of the plain fn (`#'total` — the return type is inferred by RUNNING it on the
   sample) or a bare SYMBOL (`'revenue` — for bodies that use a wandler-only verb like `join`/`member`
   that can't run as plain Clojure; then `:ret <malli-schema>` is required). A symbol registers under
   the current namespace, so call it where you'll write the `a/defn`.

   Examples:
     (defn total [os] (reduce + 0 (map :amount os)))      ; plain Clojure, no types
     (induce-types! #'total [[{:amount 5} {:amount 9}]])  ; read the schema off the data
     (a/defn total [os] (reduce + 0 (map :amount os)))    ; same body — now verified + optimized

     (induce-types! 'revenue [custs orders] :ret :int)    ; relational: name + explicit return
     (a/defn revenue [custs orders] (reduce + 0 (map … (join … custs orders))))"
  [f sample-args & {:keys [refined? ret]}]
  (let [arg->schema (fn [x]
                      (if (and (sequential? x) (map? (first x)))
                        [:sequential ((if refined? :refined-schema :structure) (infer x))]
                        (mp/provide [x])))
        v?     (var? f)
        ns-sym (if v? (ns-name (:ns (meta f))) (ns-name *ns*))
        nm     (if v? (:name (meta f)) f)
        ret    (or ret
                   (when v? (try (mp/provide [(apply @f sample-args)]) (catch Throwable _ nil)))
                   (throw (ex-info (str "induce-types!: no return type for " nm
                                        " — pass `:ret <malli-schema>` (required when the body uses a "
                                        "wandler-only verb like join/member, or `" nm "` is a symbol).")
                                   {:fn nm})))
        schema (into [:=> (into [:cat] (mapv arg->schema sample-args))] [ret])]
    (m/-register-function-schema! ns-sym nm schema nil)
    schema))
