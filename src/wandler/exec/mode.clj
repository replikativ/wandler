(ns wandler.exec.mode
  "MODE LATTICE + the ∂ (differentiation) pass — the type-level organizing layer that lets ONE surface
   pipeline mix BATCH, DIFFERENTIAL (incremental / DBSP) and ASYNC (reactive) computation while staying
   certified at the boundary, rather than compiling each combination separately and gluing them in an
   un-kernel-ed substrate.

   ── Why a lattice ────────────────────────────────────────────────────────────────────────────────
   Build-Systems-à-la-Carte (Mokhov–Mitchell–Peyton Jones) factors a dataflow system into TWO
   orthogonal knobs — `scheduler × rebuilder` — and any combination is valid. We add a clock (Rhine):
     :diff   false (batch / recompute)   ⊑   true (differential — ∂, the DBSP increment)   [rebuilder]
     :sched  :sync (pull)                ⊑   :async (push / reactive — Strm, spindel)       [scheduler]
     :clock  nil | keyword               (rate; differing clocks ⇒ a typed RESAMPLING seam)  [Rhine]
   A pipeline's mode is the LUB of its parts (`lub`); the mode selects the γ-lowering (`route`). Two
   sub-pipelines at different clocks meet at a `::resample` seam — Rhine's type-level resampling buffer.

   ── Why it stays in the kernel ───────────────────────────────────────────────────────────────────
   Differentiation/dataflow is COMONADIC (context: history/stream); async/effects are MONADIC; the
   principled way to combine effectful + context-dependent computation is a DISTRIBUTIVE LAW (Uustalu &
   Vene, *The Essence of Dataflow Programming* — they apply exactly this to clocked dataflow). The
   modern type-theoretic realization is MODAL FRP (Bahr, *Modal FRP for all* / *Asynchronous Modal
   FRP*): the mode is a MODALITY (□ stable/batch, ▷ later/async) tracked in the TYPE, so cross-mode
   composition is the modalities' intro/elim — kernel-checked — and productivity is a theorem. We keep
   the Ansatz pattern (admit a typed boundary law, discharge it over time, cf. `Datahike.q`).

   ── The ∂ pass ───────────────────────────────────────────────────────────────────────────────────
   `differentiate` lowers a plan-lens (wandler.optimize.plan) into the Z-set incremental stage-DSL (wandler.exec.zset),
   emitting a CERTIFICATE that cites, per op, the kernel law that licenses incrementalizing it:
     join             → Zproduct_product_rule  (PROVEN, diff×diff bilinear differential)
                        + Strm.joinCount2_step  (PROVEN, diff×async — streamed join recurrence)
     map/filter/sum   → Mode.diff_async_dist    (PROVEN by induction on n via Strm.scan_step: a LINEAR
       (LINEAR ops)     Z-set operator — additive + 0-preserving — commutes with stream integration ∫.
                        The certified incremental path is AXIOM-FREE; the only axioms are the INTENTIONAL
                        foreign/black-box leaves admitted via register-foreign! (Datahike.q, user fns).
   ∂ is a functor with a CHAIN RULE (∂(g∘f)=∂g∘∂f), so a SUBTERM can be differentiated while the rest
   stays batch — 'differential for one thing, not the rest'.

   Lineage: `../rhine` (clock-safe FRP, separates clocking/scheduling/resampling) informed `../spindel`,
   the async substrate. See docs/MODE_LATTICE.md and [[modal-mode-lattice]]."
  (:require [wandler.runtime]   ; codegen lowering registry (auto-installs at load — leaf/batch codegen needs it)
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.level :as lvl]
            [wandler.optimize.plan :as plan]
            [wandler.exec.physical :as phys]
            [wandler.exec.zset :as zs]
            [clojure.string :as str]
            [clojure.walk :as walk]))

;; ── the mode lattice (plain data) ────────────────────────────────────────────────────────────────
(def batch "Pure batch: recompute, pull-driven (List / reducer fusion)."     {:diff false :sched :sync  :clock nil})
(def diff  "Differential: incremental, pull-driven (Z-set / DBSP view)."      {:diff true  :sched :sync  :clock nil})
(def async "Reactive: push-driven at the base clock (Strm / spindel)."        {:diff false :sched :async :clock :base})

(defn lub
  "Compose two modes at a pipeline boundary — the lattice JOIN. ∂ propagates (or), async dominates
   (a single async source makes the whole pipeline reactive), clocks must agree else a `::resample`
   seam is flagged (Rhine: a typed resampling buffer is required to bridge the rates)."
  [m1 m2]
  (let [c1 (:clock m1) c2 (:clock m2)
        clock (cond (nil? c1) c2 (nil? c2) c1 (= c1 c2) c1 :else ::resample)]
    {:diff      (boolean (or (:diff m1) (:diff m2)))
     :sched     (if (or (= :async (:sched m1)) (= :async (:sched m2))) :async :sync)
     :clock     clock
     :resample? (= clock ::resample)}))

;; ── mode of a TYPE — read from the head constant (NO whnf: keeps Strm/Zset/Box visible) ───────────
(def head->mode
  "Kernel type-head constant → its mode. The element type's head traces the computational mode, exactly
   as wandler.surface.streams routes surface verbs on Strm-vs-List."
  {"List" batch, "Box" batch, "Subtype" batch, "Array" batch
   "Strm" async, "LSeq" async
   "Zset" diff})

(defn- head-name [ty] (let [[h _] (e/get-app-fn-args ty)] (when (e/const? h) (name/->string (e/const-name h)))))

(defn mode-of-type
  "The MODE of a kernel TYPE, from its head constant (no unfolding). A `Strm`/`LSeq` whose ELEMENT type
   is a `Zset` is a stream of Z-set CHANGES — differential AND async (a delta stream). Unknown heads
   default to batch."
  [ty]
  (let [[h targs] (e/get-app-fn-args ty)
        head (and (e/const? h) (name/->string (e/const-name h)))
        base (get head->mode head batch)]
    (if (and (#{"Strm" "LSeq"} head) (seq targs) (= "Zset" (head-name (first targs))))
      (assoc base :diff true)                     ; Strm (Zset _) = async stream of differences
      base)))

(defn mode-of-expr
  "The MODE of a kernel expression, via its inferred type's head."
  [env expr]
  (if-let [t (a/get-arg-type env nil expr)] (mode-of-type t) batch))

;; ── the router: a composed mode picks the γ-lowering ─────────────────────────────────────────────
(defn route
  "Pick the γ-lowering target for a composed mode:
     :batch-fuse        — reducer/transducer fusion (List, pull)
     :reactive          — push stream, no increment (Strm/spindel)
     :incremental       — pull-driven DBSP view (Z-set engine)
     :async-incremental — push-driven DBSP view maintained on the async substrate (spindel)."
  [{:keys [diff sched]}]
  (cond (and diff (= sched :async)) :async-incremental
        diff                        :incremental
        (= sched :async)            :reactive
        :else                       :batch-fuse))

;; ── cost model: WHICH rebuilder? (incremental only pays off when |Δ| ≪ base) ──────────────────────
(defn rebuilder-cost
  "Per-batch cost of the two rebuilders maintaining a relational view: a batch RECOMPUTE rescans the
   whole base (≈ `base-size`); the DIFFERENTIAL update touches only the cross-terms (≈ |Δ|·`fanout`,
   the DBSP `δL⋈R ⊞ L⋈δR ⊞ δL⋈δR`). The sweet spot is |Δ| ≪ base."
  [{:keys [base-size delta-size fanout] :or {fanout 1 base-size 0 delta-size 0}}]
  {:batch (double base-size) :incremental (double (* delta-size (max 1 fanout)))})

(defn choose-rebuilder
  "Cost-gated rebuilder choice: `:incremental` when its per-batch cost beats a full recompute, else
   `:batch-fuse`. This is the DBSP/datahike cardinality gate — incremental wins for small deltas."
  [sizes]
  (let [{:keys [batch incremental]} (rebuilder-cost sizes)]
    (if (< incremental batch) :incremental :batch-fuse)))

;; ── the ∂ pass: plan-lens → Z-set incremental stage skeleton + certificate ───────────────────────
(defn- chain
  "Split a (linear) plan into its base (a :join or :source) and the linear ops above it, innermost-first
   (the stage order). `(source → filter → map)` ⇒ {:base source, :ops [filter map]}."
  [p]
  (loop [p p, acc []]
    (cond
      (#{:source :join} (:op p)) {:base p :ops (vec (reverse acc))}
      (:input p)                 (recur (:input p) (conj acc p))
      :else                      {:base p :ops (vec (reverse acc))})))

(defn- op->stage
  "Map a plan op to its Z-set stage + the kernel law(s) that license incrementalizing it under `mode`."
  [op mode]
  (case op
    :join     {:stage :join   :proven? true
               :cert  (if (= :async (:sched mode))
                        ["Zproduct_product_rule" "Strm.joinCount2_step"]
                        ["Zproduct_product_rule"])}
    :filter   {:stage :filter :proven? true :obligation :linearity :cert ["Mode.diff_async_dist"]}
    :map      {:stage :map    :proven? true :obligation :linearity :cert ["Mode.diff_async_dist"]}
    :foldl    {:stage :sum    :proven? true :obligation :linearity :cert ["Mode.diff_async_dist"]}
    {:stage op :proven? false :cert []}))

(defn differentiate
  "The ∂ pass. Given a plan-lens and the source MODE, lower it into the Z-set incremental stage skeleton
   and emit the per-stage CERTIFICATE. Returns
     {:src-mode m, :mode m', :route kw, :base node, :stages [{:stage :cert :proven? :node}], :all-proven? b}
   where :mode = (assoc src-mode :diff true) (the pass IS the ∂/diff modality). The join base becomes the
   first stage; the linear ops follow. `node` keeps the plan node (its kernel-term fns) for codegen."
  [plan-node src-mode]
  (let [{:keys [base ops]} (chain plan-node)
        mode    (assoc (dissoc src-mode :resample?) :diff true)
        join?   (= :join (:op base))
        stages  (cond-> []
                  join? (conj (assoc (op->stage :join mode) :node base))
                  true  (into (map (fn [o] (assoc (op->stage (:op o) mode) :node o)) ops)))]
    {:src-mode    src-mode
     :mode        mode
     :route       (route mode)
     :base        base
     :stages      stages
     :all-proven? (every? :proven? stages)}))

(defn certificate
  "A human-legible certificate chain for a ∂ result: the route, and per stage which kernel law licenses
   its incremental execution (★ = kernel-proven law; ⊢ = unproven). A linear stage's law is proven, but
   it carries a per-op `obligation` — a one-lemma linearity witness for that specific operator."
  [{:keys [src-mode mode route stages]}]
  (str/join "\n"
    (concat
      [(format "mode: %s  ⟶[∂]⟶  %s   route: %s"
               (select-keys src-mode [:diff :sched :clock])
               (select-keys mode [:diff :sched :clock]) (name route))]
      (for [{:keys [stage cert proven? obligation]} stages]
        (format "  %-7s %s %s%s" (name stage) (if proven? "★" "⊢") (str/join " + " cert)
                (if obligation (str "   (obligation: " (name obligation) " witness)") ""))))))

;; ── execution: materialize the ∂ skeleton into a runnable wandler.exec.zset query ──────────────────────
;; The leaf fns (kf/lf/pred/f) live as kernel terms in each stage's :node; kernel-term → Clojure-fn
;; codegen is not yet automatic, so runtime IMPLS are supplied here (the honest codegen boundary).
(defn to-zset-query
  "Materialize a ∂ result into a runnable streaming query (a fn `Δ-stream → running-results`) using the
   runtime `impls` — a vector parallel to (:stages diff-result): [kf lf] for the join stage, a predicate
   for :filter, a fn for :map / :sum. Soundness of each stage is the kernel law in `certificate`."
  [{:keys [stages]} impls]
  (zs/query
    (mapv (fn [{:keys [stage]} impl]
            (case stage
              :join   (into [:join] impl)
              :filter [:filter impl]
              :map    [:map impl]
              :sum    [:sum impl]))
          stages impls)))

;; ── codegen: kernel-term leaf fn → runnable Clojure fn (closes the manual-impls gap) ─────────────
;; A joined Z-set element is a `[a b]` vector — exactly `Prod`. So a kernel `Prod.fst` codegens to
;; `(nth _ 0)` and runs directly on the engine's runtime values; `Nat.ble` ↦ `<=`, etc.
(defonce ^{:doc "name-string → runtime Clojure fn, for foreign (black-box) leaves admitted as axioms."}
  foreign-registry (atom {}))

(defn- resolve-foreigns
  "Rewrite any bare symbol in a codegen'd form that names a registered FOREIGN fn into a registry lookup
   `(get (deref foreign-registry) \"name\")`, so the eval'd code calls the black box's runtime fn — closing
   the foreign-axiom → executable seam without polluting namespaces or touching ansatz->clj."
  [form reg]
  (walk/postwalk
    (fn [x] (if (and (symbol? x) (nil? (namespace x)) (contains? reg (clojure.core/name x)))
              `(get (deref foreign-registry) ~(clojure.core/name x))
              x))
    form))

(defn codegen-fn
  "Compile a kernel-term function (a lambda `Expr`) into a runnable Clojure fn via `ansatz->clj` + eval —
   the honest kernel-term → executable bridge that `a/defn` uses for its fused runtime. Foreign (black-box)
   leaves admitted via `register-foreign!` are resolved to their registered runtime fn."
  [env term]
  (let [form (a/ansatz->clj env term [])
        reg  @foreign-registry]
    (eval (if (seq reg) (resolve-foreigns form reg) form))))

(defn auto-impls
  "Codegen the runtime `impls` for a ∂ result DIRECTLY from each stage's kernel-term leaf fns — no
   hand-supplied Clojure. Requires the plan nodes to carry real kernel terms (:kf/:lf/:pred/:fn). The
   kernel term IS the source of the executable, so the run and its certificate share one origin."
  [env {:keys [stages]}]
  (mapv (fn [{:keys [stage node]}]
          (case stage
            :join   [(codegen-fn env (:kf node)) (codegen-fn env (:lf node))]
            :filter (codegen-fn env (:pred node))
            :map    (codegen-fn env (:fn node))
            :sum    (codegen-fn env (:fn node))
            nil))
        stages))

;; ── black-box boundary: which leaves are trusted axioms vs verified kernel terms (the coach) ──────
(defn references-axiom?
  "Does the kernel `term` mention any admitted AXIOM constant? An axiom is a trusted black-box boundary
   (a foreign fn admitted via `register-foreign!`, or `Datahike.q`); a leaf with no axioms is verified."
  [env term]
  (cond
    (e/const? term)  (boolean (when-let [ci (kenv/lookup env (e/const-name term))] (.isAxiom ci)))
    (e/app? term)    (or (references-axiom? env (e/app-fn term)) (references-axiom? env (e/app-arg term)))
    (e/lam? term)    (or (references-axiom? env (e/lam-type term)) (references-axiom? env (e/lam-body term)))
    (e/forall? term) (or (references-axiom? env (e/forall-type term)) (references-axiom? env (e/forall-body term)))
    :else false))

(defn- leaf-terms [node] (keep node [:kf :lf :pred :fn]))
(defn- stage-trust [env {:keys [node]}]
  (if (some #(references-axiom? env %) (leaf-terms node)) :trusted :verified))

(defn incrementalize
  "End-to-end: differentiate `plan-node`, CODEGEN its leaf fns from their kernel terms, and return a
   runnable incremental view. By default a pull/lazy query `{:run (Δ-stream → results), :certificate,
   :route, :diff}`; with `:live? true` the kernel-grounded counterpart of a `flow` — a PUSH-driven live
   graph handle `{:push! :out :report :diff}` (drive it with `wandler.exec.live/drive!`). The `:report`
   classifies each leaf as `:verified` (codegen'd from a kernel term) or `:trusted` (references a
   black-box axiom). No hand-supplied impls: the kernel terms ARE the executable."
  [env plan-node src-mode & {:keys [live?]}]
  (let [dr    (differentiate plan-node src-mode)
        impls (auto-impls env dr)]
    (if live?
      (let [report (mapv (fn [{:keys [stage cert] :as s}]
                           {:op stage :certificate (first cert) :payload (stage-trust env s)})
                         (:stages dr))]
        (assoc ((requiring-resolve 'wandler.exec.live/from-stages) (:stages dr) impls report) :diff dr))
      {:run         (to-zset-query dr impls)
       :certificate (certificate dr)
       :route       (:route dr)
       :diff        dr})))

;; ── admit a third-party / black-box Clojure fn as a typed boundary axiom (Datahike.q, generalized) ─
(defn register-foreign!
  "Admit a black-box Clojure fn `f` of kernel type `dom → cod` as a TYPED AXIOM (opaque, trusted — the
   boundary is named and typed, the body unverified) and register its runtime. After this, a pipeline may
   use `sym` as a leaf: the structure AROUND it stays certified (the ∂ laws are payload-independent), the
   leaf is `:trusted` (sound for incremental iff `f` is pure). `env-atom` is e.g. `ansatz.core/ansatz-env`.

   This is the EXEC-LAYER counterpart of the DSL `a/foreign` / `wandler.algebra/foreign` macros: same
   idea (a trusted black-box fn at a kernel type), different layer. The macros DEFINE a foreign fn in a
   surface program (and `w/foreign` additionally lifts ^{:laws …} into the algebra registry); this
   registers the runtime closure into `foreign-registry` so `codegen-fn` can RESOLVE the axiom leaf to
   its executable when running an incremental view."
  [env-atom sym dom cod f]
  (let [nm (name/from-string (str sym))]
    (when-not (kenv/lookup @env-atom nm)
      (swap! env-atom kenv/check-constant (kenv/mk-axiom nm [] (e/forall' "_" dom cod :default))))
    (swap! foreign-registry assoc (str sym) f)
    nm))

;; ── runtime-rep alignment: run the engine over the kernel-native EDN `Value` rep, EDN in / EDN out ─
;; The engine and the codegen'd leaf fns must share ONE row representation. Codegen of a kernel term over
;; `Value` (vget/vint?/…) runs on the tagged-vector rep `[cidx field…]`, while callers hold keyword-maps.
;; `run-edn` bridges them with the existing `edn->value` / `value->edn` converters (ansatz.surface.data): ingest
;; each delta row (keyword-map → tagged Value), egress each result key back. A join pair `[a b]` of
;; Values egresses component-wise; a numeric aggregate (sum/count) passes through.
(defn- edn-conv [s] (requiring-resolve (symbol "ansatz.surface.data" s)))

(defn run-edn
  "Wrap an incremental `run` (Δ-stream → running views over the kernel-native `Value` rep) so it accepts
   and returns ordinary keyword-map EDN. Ingest: each row keyword-map → tagged `Value` (`edn->value`).
   Egress: each result key → EDN (`value->edn`), recursing into join pairs; numeric aggregates pass."
  [run]
  (let [edn->v @(edn-conv "edn->value")
        v->edn @(edn-conv "value->edn")
        ingest (fn [zm] (into {} (map (fn [[r w]] [(edn->v r) w])) zm))
        eg (fn eg [k] (cond (number? k)                          k             ; aggregate
                            (and (vector? k) (integer? (first k))) (v->edn k)   ; a single tagged Value
                            (vector? k)                          (mapv eg k)   ; a join pair/tuple of Values
                            :else                                k))]
    (fn [deltas]
      (->> (mapv (fn [[dl dr]] [(ingest dl) (ingest dr)]) deltas)
           run
           (map (fn [zm] (into {} (map (fn [[k w]] [(eg k) w])) zm)))))))

;; ── the ::resample clock seam: bridge two differential streams at different rates (Rhine) ────────
;; When `lub` meets two sub-pipelines at different clocks it flags `::resample` — Rhine's insight that
;; composing rates REQUIRES an explicit, typed resampling buffer. For a DIFFERENTIAL (Z-set delta)
;; stream the faithful buffer is ACCUMULATE-and-RELEASE: ⊞ the fast deltas between slow ticks, emit the
;; net delta at each slow tick. This is exactly DBSP batching, so the slow-clock view is byte-identical
;; to the fast run sampled at the slow ticks — correctness is preserved across the rate change.
(defn resample-deltas
  "Resample a FAST `[δL δR]` delta-stream onto a SLOWER clock: ⊞-accumulate each side between slow ticks
   and release the net `[δL δR]` at each tick (`tick?` : index → bool). The certified-safe rate bridge —
   feeding the result to an incremental `run` yields the same views as the fast run sampled at the ticks."
  [tick? deltas]
  (let [step (fn [[bl br out] [i [dl dr]]]
               (let [bl' (zs/z-add bl dl) br' (zs/z-add br dr)]
                 (if (tick? i) [{} {} (conj out [bl' br'])] [bl' br' out])))]
    (nth (reduce step [{} {} []] (map-indexed vector deltas)) 2)))

(defn every-nth
  "A slow clock that fires every `n` fast ticks (a `tick?` predicate for `resample-deltas`)."
  [n] (fn [i] (zero? (mod (inc i) n))))

;; ── the surface front door: source TYPES pick the lowering automatically ─────────────────────────
(defn pipeline-mode
  "The pipeline's overall mode = the LUB of its source modes (each read from its kernel type). This is
   where 'the source type selects the lowering' happens — pass the source types (e.g. the param types
   from an elaboration `lctx`)."
  [source-types]
  (reduce lub batch (map mode-of-type source-types)))

(defn- lctx-types
  "The source kernel types in an elaboration `lctx` (a map fvar-id → {:type …}, as wandler.gradual emits)."
  [lctx]
  (keep :type (vals lctx)))

(defn- batch-run
  "Optimize + codegen an elaborated BATCH `term` into a runnable Clojure fn, curried over the source fvars
   (the `lctx` keys). This gives `route-surface`'s batch branch a `:run` — the SAME shape the incremental
   branch already returns — so the type-driven front door yields a runnable in every mode. Returns nil if
   the term isn't codegenable (e.g. a bare source variable with a mismatched lctx)."
  [env term lctx]
  (let [opt ((requiring-resolve 'wandler.optimize/optimize-cost) env term :lctx lctx)
        t   (:term opt)
        ids (sort > (keys lctx))   ; abstract highest id first (innermost) ⇒ first param = lowest id
        lam (reduce (fn [body fid]
                      (e/lam (or (:name (lctx fid)) (str "s" fid)) (:type (lctx fid)) (e/abstract1 body fid) :default))
                    t ids)]
    (eval (a/ansatz->clj env lam []))))

(defn- batch-run-transduce
  "Like batch-run, but emit the optimized body as a TRANSDUCER pipeline (phys/plan->transducer over the
   plan lens), then curry over the source fvars — same callable shape as batch-run. Returns nil when the
   optimized plan isn't a linear producing pipeline (the caller falls back to batch-run's eager path)."
  [env term lctx]
  (let [opt ((requiring-resolve 'wandler.optimize/optimize-cost) env term :lctx lctx)
        t   (:term opt)
        ids (sort > (keys lctx))
        lam (reduce (fn [body fid]
                      (e/lam (or (:name (lctx fid)) (str "s" fid)) (:type (lctx fid)) (e/abstract1 body fid) :default))
                    t ids)
        [names body] (loop [x lam, ns []] (if (e/lam? x) (recur (e/lam-body x) (conj ns (e/lam-name x))) [ns x]))
        tform (phys/plan->transducer env (plan/term->plan body) names)]
    (when tform
      ;; curry outermost-first, matching batch-run's nested lambdas
      (eval (reduce (fn [inner nm] (list 'clojure.core/fn [(symbol nm)] inner)) tform (reverse names))))))

(defn- batch-run-array
  "Run a chunkable batch plan via a registered chunked-array backend (raster/stratum); nil if no backend
   applies (the caller falls back to the eager/apfoldl realization, which is result-equal)."
  [env term lctx]
  (let [opt ((requiring-resolve 'wandler.optimize/optimize-cost) env term :lctx lctx)
        t   (:term opt)
        ids (sort > (keys lctx))
        lam (reduce (fn [body fid]
                      (e/lam (or (:name (lctx fid)) (str "s" fid)) (:type (lctx fid)) (e/abstract1 body fid) :default))
                    t ids)
        [names body] (loop [x lam, ns []] (if (e/lam? x) (recur (e/lam-body x) (conj ns (e/lam-name x))) [ns x]))
        form (phys/array-form env (plan/term->plan body) names)]
    (when form
      (eval (reduce (fn [inner nm] (list 'clojure.core/fn [(symbol nm)] inner)) form (reverse names))))))

(defn execute
  "THE dispatcher (cohesion audit item 1): the source TYPES pick the lowering — this is
   the one entry point behind 'the type picks the mode'. Given an elaborated
   `{:term :lctx}`, derive the pipeline mode from the source types, plan the term, and
   APPLY the γ-lowering:

     batch              → certified optimize + codegen          {:run (fn …)}
     :incremental       → pull DBSP view over Z-set deltas      {:run (Δs → results)}
     :async-incremental → PUSH-driven live graph (the default   {:push! :out :report}
                          for an async delta source; this is
                          how wandler.exec.live is reached —
                          you never wire it by hand)

   Options:
     :sizes  {:base-size :delta-size :fanout} — cost-gates the ∂ choice: a differential
             source is DOWNGRADED to recompute when |Δ| isn't ≪ base.
     :live?  force (true) or suppress (false) the push graph; default = async route.

   Every branch carries its :certificate; the differential stages and the batch rewrite
   are kernel-certified the same way (the route never changes the trust story).
   Returns {:mode :route :plan :certificate (:diff) (:run | :push! :out :report) …}."
  [env {:keys [term lctx]} & {:keys [sizes live? physical]}]
  (let [pm0 (pipeline-mode (lctx-types lctx))
        downgrade? (boolean (and (:diff pm0) sizes (= :batch-fuse (choose-rebuilder sizes))))
        pm (cond-> pm0 downgrade? (assoc :diff false))
        pl (plan/term->plan term)
        cost (when sizes (rebuilder-cost sizes))]
    (if (:diff pm)
      (let [dr (differentiate pl pm)
            base-join? (= :join (:op (:base dr)))
            push? (if (some? live?) live? (= :async (:sched pm)))
            impls (when base-join? (auto-impls env dr))
            base {:mode pm :route (:route dr) :plan pl :certificate (certificate dr) :diff dr}]
        (cond-> base
          cost (assoc :cost cost)
          (and base-join? (not push?))
          (assoc :run (to-zset-query dr impls))
          (and base-join? push?)
          (merge (let [report (mapv (fn [{:keys [stage cert] :as st}]
                                      {:op stage :certificate (first cert)
                                       :payload (stage-trust env st)})
                                    (:stages dr))]
                   ((requiring-resolve 'wandler.exec.live/from-stages)
                    (:stages dr) impls report)))))
      ;; batch runnable — one front door. The physical realization (:eager vs :transduce) is a
      ;; POST-optimize selector over the plan; :eager (batch-run) is the unchanged default, :transduce
      ;; emits a native Clojure transducer pipeline (opt-in via :physical until boundedness automates it).
      (let [want     (phys/physical-route pl :requested physical)
            run'     (try (case want
                            :array     (batch-run-array env term lctx)      ; raster/stratum, else nil
                            :transduce (batch-run-transduce env term lctx)  ; native Clojure xforms
                            nil)
                          (catch Throwable _ nil))
            brun     (or run' (try (batch-run env term lctx) (catch Throwable _ nil)))  ; eager fallback
            phys-tag (if run' want :eager)]
        (cond-> {:mode pm :route (route pm) :plan pl :physical phys-tag
                 :certificate (format "mode %s  ⟶  %s / %s  (%s)"
                                (select-keys pm [:diff :sched :clock]) (name (route pm)) (name phys-tag)
                                (if downgrade? "∂ downgraded — |Δ| not ≪ base, recompute cheaper" "no ∂ — recompute"))}
          cost       (assoc :cost cost)
          brun       (assoc :run brun)
          downgrade? (assoc :cost-downgraded? true))))))

(def ^{:doc "Deprecated name for `execute` (the pre-audit spelling)."}
  route-surface execute)

;; ── kernel install: the batch modality (Box), the zero Z-set (Zzero), and the ONE admitted law ───
(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- zsetOf [A] (e/app (e/const' (nm "Zset") []) A))
(defn- strmOf [A] (e/app (e/const' (nm "Strm") []) A))
(defn- eqZ [T x y] (e/app* (e/const' (nm "Eq") [L1]) T x y))
(defn- zaddE [A m1 m2] (e/app* (e/const' (nm "Zadd") []) A m1 m2))
(defn- zzeroOf [A] (e/app (e/const' (nm "Zzero") []) A))

(defn- box-def []
  ;; Box.{u} : Type u → Type u := fun A => A   — the □ STABLE/BATCH modality (can run any time).
  (kenv/mk-def (nm "Box") [] (e/forall' "A" type0 type0 :default)
               (e/lam "A" type0 (e/bvar 0) :default) :hints :opaque))

(defn- zzero-def []
  ;; Zzero : ∀ A, Zset A := fun A a => Int.ofNat 0   — the additive identity Z-set (empty relation).
  (let [zeroInt (e/app (e/const' (nm "Int.ofNat") []) (e/const' (nm "Nat.zero") []))]
    (kenv/mk-def (nm "Zzero") [] (e/forall' "A" type0 (zsetOf (e/bvar 0)) :default)
                 (e/lam "A" type0 (e/lam "a" (e/bvar 0) zeroInt :default) :default))))

(def ^:private natT (e/const' (nm "Nat") []))
(def ^:private n0 (e/const' (nm "Nat.zero") []))
(defn- nsucc [n] (e/app (e/const' (nm "Nat.succ") []) n))
(defn- zaddPart [A] (e/app (e/const' (nm "Zadd") []) A))
(defn- etrans [T x y w h1 h2] (e/app* (e/const' (nm "Eq.trans") [L1]) T x y w h1 h2))
(defn- esymm [T x y h] (e/app* (e/const' (nm "Eq.symm") [L1]) T x y h))
(defn- cong-q [A B q a1 a2 h] (e/app* (e/const' (nm "congrArg") [L1 L1]) (zsetOf A) (zsetOf B) a1 a2 q h))

(defn- prove-diff-async-dist []
  ;; Mode.diff_async_dist : the diff×async DISTRIBUTIVE LAW — PROVEN (induction on n via Strm.scan_step).
  ;; A LINEAR Z-set operator q (commutes with ⊞ AND preserves 0 — an LTI operator) commutes with stream
  ;; integration (Strm.scan over Zadd): integrating the stream of q-applied deltas equals q of the
  ;; integrated stream. The DBSP fact that linear operators commute with I.
  ;;   ∀ (A B : Type) (q : Zset A → Zset B),
  ;;     (hlin : ∀ a b, q (a ⊞ b) = q a ⊞ q b)          -- q additive
  ;;     (hz   : q 0 = 0)                                -- q preserves the empty relation
  ;;     ∀ (s : Strm (Zset A)) (n : Nat),
  ;;       scan ⊞ 0 (smap q s) n  =  q (scan ⊞ 0 s n)
  ;; Base n=0:  Zadd_B 0 (q s0) =[symm congr hz] Zadd_B (q 0)(q s0) =[symm hlin 0 s0] q(Zadd_A 0 s0).
  ;; Step:      scanB(n+1) =[scan_step] Zadd_B (scanB n)(q sₙ₊₁) =[ih] … =[symm hlin] q(Zadd_A (scanA n) sₙ₊₁)
  ;;            =[congr (symm scan_step)] q(scanA(n+1)).
  (let [A (e/fvar 1) B (e/fvar 2) q (e/fvar 3) hlin (e/fvar 4) hz (e/fvar 5) s (e/fvar 6)
        qA   (fn [x] (e/app q x))
        smap (e/app* (e/const' (nm "Strm.smap") []) (zsetOf A) (zsetOf B) q s)
        scanB-strm (e/app* (e/const' (nm "Strm.scan") []) (zsetOf B) (zsetOf B) (zaddPart B) (zzeroOf B) smap)
        scanA-strm (e/app* (e/const' (nm "Strm.scan") []) (zsetOf A) (zsetOf A) (zaddPart A) (zzeroOf A) s)
        scanB (fn [k] (e/app scanB-strm k))
        scanA (fn [k] (e/app scanA-strm k))
        sAt   (fn [k] (e/app s k))
        hlinAt (fn [aa bb] (e/app* hlin aa bb))
        M    (e/lam "n" natT (eqZ (zsetOf B) (scanB (e/bvar 0)) (qA (scanA (e/bvar 0)))) :default)
        ;; base
        s0 (sAt n0) zB0 (zzeroOf B) zA0 (zzeroOf A)
        congHz (cong-q B B (e/lam "w" (zsetOf B) (zaddE B (e/bvar 0) (qA s0)) :default) (qA zA0) zB0 hz)
        base (etrans (zsetOf B) (zaddE B zB0 (qA s0)) (zaddE B (qA zA0) (qA s0)) (qA (zaddE A zA0 s0))
                     (esymm (zsetOf B) (zaddE B (qA zA0) (qA s0)) (zaddE B zB0 (qA s0)) congHz)
                     (esymm (zsetOf B) (qA (zaddE A zA0 s0)) (zaddE B (qA zA0) (qA s0)) (hlinAt zA0 s0)))
        ;; step
        ssA (fn [n] (e/app* (e/const' (nm "Strm.scan_step") []) (zsetOf A) (zsetOf A) (zaddPart A) (zzeroOf A) s n))
        ssB (fn [n] (e/app* (e/const' (nm "Strm.scan_step") []) (zsetOf B) (zsetOf B) (zaddPart B) (zzeroOf B) smap n))
        nn (e/fvar 7) ih (e/fvar 8)
        sSn (sAt (nsucc nn)) IRn (scanB nn) ILn (scanA nn)
        stepbody
        (etrans (zsetOf B) (scanB (nsucc nn)) (zaddE B IRn (qA sSn)) (qA (scanA (nsucc nn)))
          (ssB nn)
          (etrans (zsetOf B) (zaddE B IRn (qA sSn)) (zaddE B (qA ILn) (qA sSn)) (qA (scanA (nsucc nn)))
            (cong-q B B (e/lam "w" (zsetOf B) (zaddE B (e/bvar 0) (qA sSn)) :default) IRn (qA ILn) ih)
            (etrans (zsetOf B) (zaddE B (qA ILn) (qA sSn)) (qA (zaddE A ILn sSn)) (qA (scanA (nsucc nn)))
              (esymm (zsetOf B) (qA (zaddE A ILn sSn)) (zaddE B (qA ILn) (qA sSn)) (hlinAt ILn sSn))
              (cong-q A B q (zaddE A ILn sSn) (scanA (nsucc nn))
                      (esymm (zsetOf A) (scanA (nsucc nn)) (zaddE A ILn sSn) (ssA nn))))))
        Mn   (eqZ (zsetOf B) (scanB nn) (qA (scanA nn)))
        step (e/lam "n" natT (e/abstract1 (e/lam "ih" Mn (e/abstract1 stepbody 8) :default) 7) :default)
        natrec (e/app* (e/const' (nm "Nat.rec") [z]) M base step)
        ;; the statement
        body-ty (e/forall' "n" natT (eqZ (zsetOf B) (scanB (e/bvar 0)) (qA (scanA (e/bvar 0)))) :default)
        hlin-ty (e/forall' "a" (zsetOf A)
                  (e/abstract1 (e/forall' "b" (zsetOf A)
                    (e/abstract1 (eqZ (zsetOf B) (qA (zaddE A (e/fvar 20) (e/fvar 21)))
                                   (zaddE B (qA (e/fvar 20)) (qA (e/fvar 21)))) 21) :default) 20) :default)
        hz-ty (eqZ (zsetOf B) (qA zA0) zB0)
        wrap (fn [t mk] (-> t (#(mk "s" (strmOf (zsetOf A)) 6 %)) (#(mk "hz" hz-ty 5 %)) (#(mk "hlin" hlin-ty 4 %))
                            (#(mk "q" (e/forall' "_" (zsetOf A) (zsetOf B) :default) 3 %))
                            (#(mk "B" type0 2 %)) (#(mk "A" type0 1 %))))]
    [(wrap body-ty (fn [nme t i b] (e/forall' nme t (e/abstract1 b i) :default)))
     (wrap natrec  (fn [nme t i b] (e/lam nme t (e/abstract1 b i) :default)))]))

(defonce ^:private cache (atom nil))

(defn install!
  "Install the mode-layer kernel constants (idempotent), after ensuring the Z-set + Strm laws the ∂ pass
   cites are present:
     Box                  — the □ stable/batch modality (def, opaque)
     Zzero                — the additive-identity Z-set (def)
     Mode.diff_async_dist — the diff×async distributive law, PROVEN by induction on n (Strm.scan_step +
                            linearity); a linear (additive, 0-preserving) Z-set op commutes with ∫."
  []
  ((requiring-resolve 'wandler.exec.zset/install!))
  ((requiring-resolve 'wandler.surface.streams/install!))
  ((requiring-resolve 'wandler.surface.streams/install-join!))
  (when-not (kenv/lookup (a/env) (nm "Mode.diff_async_dist"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [box  (box-def)
            zz   (zzero-def)
            _    (doseq [d [box zz]] (swap! a/ansatz-env kenv/check-constant d))
            [ty pf] (prove-diff-async-dist)
            thm  (kenv/mk-thm (nm "Mode.diff_async_dist") [] ty pf)
            _    (swap! a/ansatz-env kenv/check-constant thm)]
        (reset! cache [box zz thm]))))
  (a/env))
