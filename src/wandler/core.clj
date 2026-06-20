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
            [ansatz.kernel.name :as name]
            [wandler.surface.vocabulary]
            [wandler.clean.surface.collections :as coll]
            [wandler.clean.surface.strings]
            [wandler.clean.surface.option]
            [wandler.clean.surface.records :as rec]
            [wandler.clean.surface.relational :as rel]
            [wandler.kmap :as kmap]
            [wandler.algebra :as algebra]
            [wandler.runtime :as rt]
            [wandler.optimize :as opt]
            [wandler.clean.optimize :as copt]))

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
      (swap! reports assoc fn-name res)
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
    {:verified? (:verified? r)
     :changed? (:changed? r)
     :rewrites (vec (:rewrites r))
     :stages-before (:stages-before r)
     :stages-after (:stages-after r)
     :passes-before (:passes-before r)
     :passes-after (:passes-after r)}))

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
   docs/SURFACE.md is generated from it (dev/gen_surface_md.clj)."
  []
  ((requiring-resolve 'wandler.surface.vocabulary/vocabulary-table)))

(defn execute
  "THE mode dispatcher (thin wrapper over wandler.exec.mode/execute, loaded on demand):
   given an elaborated {:term :lctx}, the source TYPES pick the lowering — batch fuse,
   pull-incremental (Z-sets), or the push-driven live graph for async delta sources.
   Options: :sizes (cost-gates the ∂ choice), :live? (force/suppress push)."
  [env elaborated & opts]
  (apply (requiring-resolve 'wandler.exec.mode/execute) env elaborated opts))

(defn install!
  "Install the wandler runtime into ansatz's three seams (idempotent). Call after the
   kernel env is loaded — (a/init! \"init\") or richer — then define pipelines with a/defn.
   (The registry seams are already filled at load; this adds the env-dependent pieces.)"
  []
  (install-registries!)
  (kmap/install!)
  (algebra/install!)
  :installed)

(install-registries!)

;; ── the plan view + the measure→replan loop (the verified JIT) ───────────────────────────

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
  "The CLOSED measure→replan loop (the verified JIT): MEASURE the pipeline's filter
   selectivities on `sample` data, then re-optimize `term` with those REAL cardinalities —
   every adopted rewrite kernel-re-certified, so adapting the plan to the observed workload
   cannot make it unsound. Returns the optimize-cost result plus :profile; with :compare?
   also :static (the plan WITHOUT the measured profile)."
  [env term sample & {:keys [lctx compare?]}]
  (let [profile (profile-selectivity env term sample)
        res (assoc (opt/optimize-cost env term :lctx lctx :selectivity profile) :profile profile)]
    (if compare?
      (assoc res :static (opt/optimize-cost env term :lctx lctx))
      res)))
