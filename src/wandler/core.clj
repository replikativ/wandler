;; Wandler — the verified data-transformation runtime, built on the ansatz CIC kernel.
;;
;; You write ordinary Clojure pipelines in `a/defn`; wandler elaborates them to kernel
;; terms (lean4 elab_rules-shaped TERM elaborators through `ansatz.surface.api`),
;; OPTIMIZES them by certified rewriting (every adopted rewrite carries a kernel proof
;; `optimized ≡ original` — translation validation, checked by the same kernel that
;; admits Mathlib), and LOWERS them to fast Clojure through the codegen seam.
;;
;; Integration is three seams in ansatz, all additive (no carve, no fork):
;;   SEAM 1  term/macro elaborator registries  — the collection/relational surface
;;   SEAM 2  a/optimize-hook                   — the certified optimizer (this ns wires it)
;;   SEAM 3  a/codegen-registry                — the runtime lowering (wandler.runtime)
(ns wandler.core
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [wandler.surface.vocabulary]
            [wandler.surface.collections :as coll]
            [wandler.surface.strings]
            [wandler.surface.option]
            [wandler.surface.records :as rec]
            [wandler.surface.relational :as rel]
            [wandler.kmap :as kmap]
            [wandler.algebra :as algebra]
            [wandler.runtime :as rt]
            [wandler.optimize :as copt]
            [wandler.infer :as infer]))

(defonce ^{:doc "fn-name → the optimizer report for its last definition (the explain source)."}
  reports (atom {}))

(declare ^:dynamic *optimize*)

(defn- optimize-hook
  "The SEAM 2 filler: cost-directed certified optimization of an a/defn body.
   Keeps the rewrite only if the kernel certified it; records the report for explain."
  [env fn-name term]
  (if-not *optimize*
    term
    (let [n (loop [t term, k 0] (if (e/lam? t) (recur (e/lam-body t) (inc k)) k))
          res (try (copt/optimize-body env term n)
                   (catch Throwable t
                     {:term term :verified? false :changed? false
                      :error (.getMessage t)}))]
      ;; keep the NAIVE term too, so the JIT (`optimize-measured`) can re-plan it from the fn NAME
      ;; with measured cardinalities (a cost-gated choice can differ from the static plan).
      (swap! reports assoc fn-name (assoc res :naive term))
      (:term res))))

(defn explain
  "The optimizer report for a verified fn: was a rewrite adopted, which laws fired,
   and the pipeline shape before/after. `:verified?` means the kernel CERTIFIED the
   adopted term equal to the original definition.

   `fn-name` is a symbol or string (coerced) — reports are keyed by the KERNEL
   constant's name, recorded when the optimizer hook fires inside define-verified
   (before the Clojure var exists), so the fn VALUE has nothing to look up by."
  [fn-name]
  (when-let [r (get @reports (str fn-name))]
    (cond-> {:verified? (:verified? r)
             :changed? (:changed? r)
             :rewrites (vec (:rewrites r))
             :stages-before (:stages-before r)
             :stages-after (:stages-after r)
             :passes-before (:passes-before r)
             :passes-after (:passes-after r)}
      (:error r) (assoc :error (:error r)))))

(defn term
  "The kernel term of a verified fn `fn-name` (so the whole API composes by NAME): the optimized
   (fused) term by default, or the NAIVE pre-optimization term with `:naive? true`. nil if `fn-name`
   has no optimization record (define it with `a/defn` first)."
  [fn-name & {:keys [naive?]}]
  (when-let [r (get @reports (str fn-name))]
    (if naive? (:naive r) (:term r))))

(defn install-registries!
  "Fill the env-FREE seams (surface verb registries, runtime lowering, the optimizer
   hook). Safe at namespace load — nothing here consults the kernel env."
  []
  (coll/install!)
  (rec/install!)
  (rel/install!)
  (rt/install!)
  (reset! a/optimize-hook optimize-hook)
  :installed)

(defn vocabulary
  "The surface verb vocabulary, as data: verb → {:sig :dispatch :denotation :lowering
   :ns :tier}. The wandler surface is a type-directed staged elaborator over THIS
   closed vocabulary — compositional inside it, explicit about its edge.
   docs/REFERENCE.md is generated from it (dev/gen_surface_md.clj)."
  []
  ((requiring-resolve 'wandler.surface.vocabulary/vocabulary-table)))

(defn execute
  "THE mode dispatcher (thin wrapper over wandler.exec.mode/execute, loaded on demand):
   given an elaborated {:term :lctx}, the source TYPES pick the lowering — batch fuse,
   pull-incremental (Z-sets), or the push-driven live graph for async delta sources.
   Options: :sizes (cost-gates the ∂ choice), :live? (force/suppress push)."
  [env elaborated & opts]
  (apply (requiring-resolve 'wandler.exec.mode/execute) env elaborated opts))

(defn- open-body
  "Open a (curried) function body `λp0…λpₙ. pipeline` — instantiate each parameter binder with a fresh
   fvar — into the `{:term :lctx}` the mode dispatcher consumes (`lctx`: fvar-id → {:name :type}; the
   source TYPES in it are what `execute` reads to pick the mode)."
  [body]
  (loop [ex body, i 0, lctx {}]
    (if (e/lam? ex)
      (let [fid (+ 6600000 i)]
        (recur (e/instantiate1 (e/lam-body ex) (e/fvar fid)) (inc i)
               (assoc lctx fid {:name (str (e/lam-name ex)) :type (e/lam-type ex)})))
      {:term ex :lctx lctx})))

(defn- retype-list-sources
  "Re-wrap every `List A` source type in `lctx` via `(wrap A)` (other types pass through) — the knob
   `run` turns to select a mode: `List A` → `Zset A` (incremental) / `Strm (Zset A)` (async). The term
   is unchanged; the source type is purely the mode SELECTOR `execute` reads (it differentiates the
   batch plan), so this is a retype, not a re-elaboration."
  [lctx wrap]
  (into {} (map (fn [[id {:keys [type] :as d}]]
                  (let [[h targs] (e/get-app-fn-args type)]
                    [id (if (and (e/const? h) (= "List" (name/->string (e/const-name h))) (seq targs))
                          (assoc d :type (wrap (first targs))) d)]))
                lctx)))

(defn run
  "The Rung-5 front door: run a verified pipeline `fn-name` in an execution MODE picked by the SOURCE
   type — ONE logical pipeline, three lowerings, each carrying its certificate at the boundary.
     :batch       (default) over Lists — fused + codegen'd; returns {:run (fn …) …}.
     :incremental each `List A` source becomes a `Zset A` (DBSP pull view over deltas).
     :async       each becomes a `Strm (Zset A)` (push-driven live graph).
   Returns the `wandler.exec.mode/execute` result ({:mode :route :certificate (:run | :push! …)}). The
   source type is only a mode selector: :batch runs the OPTIMIZED (fused) term, while :incremental /
   :async DIFFERENTIATE the canonical NAIVE term — the un-fused join/filter/map/sum skeleton the ∂ pass
   reads (the optimizer's `filterMap` / factorized `group_by` aren't those stages). `naive ≡ optimized`
   is kernel-certified, so the route never changes the trust story; the batch route is certified by the
   optimizer, and the incremental/async route carries a per-stage certificate (kernel-proven for the
   linear/join stages, an un-runnable certified PLAN for an op it can't linearize). Requires the mode
   layer (`(wandler.exec.mode/install!)` / `w/install-streaming!`). Extra opts thread to `execute`."
  [env fn-name & {:keys [mode] :or {mode :batch} :as opts}]
  (let [ci (kenv/lookup env (name/from-string (str fn-name)))
        _  (when-not ci (throw (ex-info (str "run: no such verified fn " fn-name) {:fn fn-name})))
        ;; :batch runs the OPTIMIZED (fused) term — the fast path. :incremental / :async
        ;; DIFFERENTIATE the canonical NAIVE term instead: the ∂ pass lowers a relational
        ;; skeleton of un-fused stages (join / filter / map / sum), whereas the optimizer
        ;; collapses those into `filterMap` / a factorized `group_by` that the differentiator
        ;; can't read. naive ≡ optimized is kernel-certified (and each ∂ stage carries its own
        ;; increment law), so choosing the naive normal form for the incremental view never
        ;; changes the trust story. Fall back to the stored (optimized) term if no naive record.
        body (or (when (#{:incremental :async} mode) (term fn-name :naive? true))
                 (.getValue ci))
        eb (open-body body)
        zset (fn [a] (e/app (e/const' (name/from-string "Zset") []) a))
        strm (fn [a] (e/app (e/const' (name/from-string "Strm") []) (zset a)))
        lctx (case mode
               :batch       (:lctx eb)
               :incremental (retype-list-sources (:lctx eb) zset)
               :async       (retype-list-sources (:lctx eb) strm)
               (throw (ex-info (str "run: unknown mode " mode " (use :batch | :incremental | :async)")
                               {:mode mode})))]
    (apply execute env (assoc eb :lctx lctx) (mapcat identity (dissoc opts :mode)))))

(defn install-streaming!
  "Install the streaming / coinductive layer (idempotent, cached — each law proved once): the mode
   lattice + ∂ pass, the Z-set / `Strm` kernel laws, and the `Strm`/`LSeq` surface router. After this,
   `(range)` is typed `Strm Nat`, `take`/`reductions` window it, the productivity gate rejects a raw
   `reduce` over an infinite stream, and `run` can lower a pipeline to the `:incremental` / `:async`
   modes. Separate from `install!` (kept lean) — call this when you need the streaming/coinductive surface."
  []
  ((requiring-resolve 'wandler.exec.mode/install!))
  :installed)

(defn install!
  "Install the wandler runtime into ansatz's three seams (idempotent). Call after the
   kernel env is loaded — (a/init! \"init\") or richer — then define pipelines with a/defn.
   (The registry seams are already filled at load; this adds the env-dependent pieces.)
   This is the BATCH + relational surface; add `install-streaming!` for the incremental /
   async / `Strm` (coinductive) modes, and `install-laws!` for the FAQ optimization laws."
  []
  (install-registries!)
  (kmap/install!)
  (algebra/install!)
  :installed)

(defn install-laws!
  "Install the proven relational law library so the optimizer can adopt those
   rewrites: semijoin / anti-join index probes, aggregating-join factorization
   (the FAQ frame family), drive-direction reorder, and grace-hash spill. Heavier
   than `install!` the FIRST time (it admits the law DAG by proving each theorem),
   but `wandler.laws.faq/install!` caches the proved terms per-process, so a later
   call against a fresh env (e.g. each test namespace) just re-checks them — seconds
   → ~20ms. Idempotent. Call after `install!` and a loaded kernel env. Returns :installed."
  []
  ;; Prove the certified law DAG against ansatz's CANONICAL simp set, independent of whatever Lean
  ;; @[simp] corpus the host env inherited. `a/init!` loads it (attrs/load-bundled-attrs!); the suite's
  ;; test-env does not — and an inherited @[simp] lemma can rewrite an induction goal out of the shape a
  ;; law proof's `simp` expects ("Proof incomplete"). The laws are DESIGNED + verified against the clean
  ;; set, so clear the inherited :simp-lemmas while proving and restore it after (optimization keeps the
  ;; rich set). Soundness is unaffected: a proof term valid in the cleared env stays kernel-valid in the
  ;; attr-loaded env — clearing only narrows the simp TACTIC's search, never the kernel check.
  (let [saved (kenv/get-extension (a/env) :simp-lemmas #{})]
    (swap! a/ansatz-env kenv/with-extension :simp-lemmas #{})
    (try
      ((requiring-resolve 'wandler.laws.faq/install!))
      (finally
        (swap! a/ansatz-env kenv/update-extension :simp-lemmas #{} into saved))))
  :installed)

(install-registries!)

;; Data-first type induction (front-door re-export of wandler.infer/induce-types!): infer a malli
;; function schema from sample data + register it, so a bare-arg `a/defn` of the same name picks up the
;; kernel types. See its docstring for the plain-fn → induce-types! → a/defn flow.
(def induce-types! infer/induce-types!)

;; ── the plan view + the measure→replan loop (the PLANNING JIT) ───────────────────────────
;; "JIT" in wandler names TWO things. THIS is the PLANNING JIT (measured replanning): re-plan the
;; STATIC term against a measured workload, statically, before running. The RUNTIME hot-swap JIT —
;; replacing an operator mid-stream — is `wandler.jit.swap` / `wandler.jit.stream`. Both are sound
;; for the same reason (translation validation: every plan is kernel-certified ≡ the original).

(def ^:dynamic *optimize*
  "When false, the optimizer hook passes terms through untouched (the naive plan runs)."
  true)

(defn plan
  "A datahike-explain-style report of how the verified optimizer compiled `fn-name`:
   the SOAC stages and pass count before vs after fusion, the laws applied, and whether
   the rewrite is kernel-certified. Pass `samples` (a seq of inputs) to also PROFILE:
   cardinality, selectivity, and the fused runtime in ms. See `plan-str` to print."
  [fn-name & [samples]]
  (when-let [info (get @reports (str fn-name))]
    (let [base {:fn (str fn-name)
                :stages-before (:stages-before info)
                :stages-after  (:stages-after info)
                :passes-before (:passes-before info)
                :passes-after  (:passes-after info)
                :fused? (boolean (:changed? info))
                :verified? (boolean (:verified? info))
                :laws (:rewrites info)}]
      (if-let [xs (seq samples)]
        (let [f (resolve (symbol fn-name))
              t0 (System/nanoTime)
              outs (mapv #(f %) xs)
              ms (/ (- (System/nanoTime) t0) 1e6)
              outn (reduce + 0 (map (fn [o] (if (counted? o) (count o) 1)) outs))
              inn (reduce + 0 (map (fn [x] (if (counted? x) (count x) 1)) xs))]
          (assoc base :n-in inn :n-out outn
                 :selectivity (when (pos? inn) (double (/ outn inn)))
                 :runtime-ms (double ms)))
        base))))

(defn plan-str
  "Render `(plan fn-name samples)` as a human-readable string."
  [fn-name & [samples]]
  (if-let [p (apply plan fn-name (when samples [samples]))]
    (let [arrow (fn [stages] (if (seq stages) (clojure.string/join " → " (map str stages)) "(none)"))]
      (str "plan " (:fn p) "\n"
           "  naive:  " (arrow (:stages-before p)) "   (" (:passes-before p) " passes)\n"
           "  fused:  " (arrow (:stages-after p))  "   (" (:passes-after p) " passes)\n"
           "  laws:   " (if (seq (:laws p)) (clojure.string/join ", " (:laws p)) "confluent fusion") "\n"
           "  proof:  " (if (:verified? p) "optimized ≡ naive (kernel-certified)" "unverified") "\n"
           (when (:n-in p)
             (str "  sample: " (:n-in p) " in → " (:n-out p) " out"
                  (when (:selectivity p) (str "  (selectivity " (format "%.2f" (:selectivity p)) ")"))
                  "  in " (format "%.3f" (:runtime-ms p)) " ms\n"))))
    (str "plan " fn-name ": no optimization record")))

(defn- walk-subterms [f ex]
  (f ex)
  (cond
    (e/app? ex)    (do (walk-subterms f (e/app-fn ex)) (walk-subterms f (e/app-arg ex)))
    (e/lam? ex)    (do (walk-subterms f (e/lam-type ex)) (walk-subterms f (e/lam-body ex)))
    (e/forall? ex) (do (walk-subterms f (e/forall-type ex)) (walk-subterms f (e/forall-body ex)))
    (e/proj? ex)   (walk-subterms f (e/proj-struct ex))
    :else nil))

(defn filter-predicates
  "Every `List.filter` predicate appearing in `term` (distinct)."
  [term]
  (let [acc (volatile! [])]
    (walk-subterms
     (fn [ex]
       (let [[h args] (e/get-app-fn-args ex)]
         (when (and (e/const? h)
                    (#{"List.filter" "List.filterv"} (name/->string (e/const-name h)))
                    (>= (count args) 2))
           (vswap! acc conj (nth args 1)))))
     term)
    (distinct @acc)))

(defn measure-selectivity
  "MEASURE a filter predicate's pass-rate on a real workload. `pred` is a kernel
   `α → Bool` lambda; `sample` a seq of representative compiled values. Returns the
   observed rate ∈ [0.01, 1]."
  [env pred sample]
  (let [f (eval (a/ansatz->clj env pred []))
        n (count sample)]
    (if (zero? n) 0.5
        (-> (count (clojure.core/filter f sample)) (/ (double n)) (max 0.01) (double) (min 1.0)))))

(defn profile-selectivity
  "Build a `:selectivity` profile {pred-string → rate} for `optimize-cost` by measuring
   every `List.filter` predicate in `term` against `sample`."
  [env term sample]
  (into {} (clojure.core/map (fn [p] [(e/->string p) (measure-selectivity env p sample)])
                             (filter-predicates term))))

(defn optimize-measured
  "The CLOSED measure→replan loop (the PLANNING JIT — measured replanning; the runtime hot-swap JIT is
   `wandler.jit.swap`). REGULAR form: a `'fn-name` — re-plans that fn's
   NAIVE term against the current env. Low-level form: `(env term …)`. MEASURES the pipeline's filter
   selectivities on `sample`, fuses them with any caller-supplied `:sizes`/`:ndv` cardinalities (e.g.
   from a stream window or a datahike `:estimate`), then re-optimizes — every adopted rewrite
   kernel-re-certified, so adapting to the observed workload cannot make it unsound. Returns the
   optimize-cost result + `:profile`; with `:compare?` also `:static` (the plan WITHOUT the measured
   stats). `:sizes`/`:ndv` steer cost-gated choices (drive-direction, pre-aggregated index).

   NOTE on `sample` shape: this takes a flat seq of ELEMENTS — the per-row values the `List.filter`
   predicates see (e.g. a stream window) — because selectivity is a per-element pass-rate. This DIFFERS
   from `plan`, whose `samples` is a seq of whole INPUTS (each passed to the fn to time it / count
   cardinality). To feed one collection here, splice its elements: `(optimize-measured 'f xs)` with
   `xs` the element seq, not `[xs]`."
  [x & more]
  (let [named? (or (symbol? x) (string? x))
        [env term sample opts] (if named?
                                 [(a/env) (let [r (get @reports (str x))] (or (:naive r) (:term r)))
                                  (first more) (rest more)]
                                 [x (first more) (second more) (drop 2 more)])
        {:keys [lctx compare? sizes ndv]} (apply hash-map opts)
        _ (when (nil? term) (throw (ex-info (str "optimize-measured: no optimization record for " x
                                                 " — define it with a/defn first") {:fn x})))
        profile (profile-selectivity env term sample)
        co (fn [extra] (apply copt/optimize-cost env term
                              (concat [:lctx lctx] extra
                                      (when sizes [:sizes sizes]) (when ndv [:ndv ndv]))))
        res (assoc (co [:selectivity profile]) :profile profile)]
    (if compare? (assoc res :static (copt/optimize-cost env term :lctx lctx)) res)))
