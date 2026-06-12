;; Verified optimizer for collection / relational pipelines.
;;
;; THE IR IS THE KERNEL TERM. A pipeline is already a nested combinator term over
;; our ansatz data types — `List.foldl f init (List.filter p (List.map g xs))`,
;; `Map.group_by …`, `Map.join …`. There is no separate Plan IR to lift into; the
;; elaborated `a/defn` body *is* the plan. (The reducers `Plan` record demotes to
;; a human-readable explain-view.)
;;
;; THE REWRITER IS simp. The ported simp engine already does what a bespoke
;; optimizer would hand-roll: discrimination-tree matching, congruence descent,
;; fixpoint driving, and — crucially — it returns a PROOF term `orig = result`
;; (`SimpResult{:expr,:proof?}`). So the optimizer is a curated, ORIENTED lemma
;; set fed to simp:
;;   - Init fusion laws (free): map_map, filter_filter, foldl_map, map_id, …
;;   - our proven relational laws (added incrementally, like Map.insert_nodupkeys).
;;
;; This mirrors Lean's own `@[csimp]`: an optimized form is admitted only with a
;; proof it equals the original; the kernel checks the proof, the optimizer just
;; decides. Cost-directed SEARCH (DP join ordering, à la stratum/datahike) sits
;; ABOVE this as a later layer — it chooses which equivalent plan to keep; each
;; chosen rewrite is still certified here by a kernel-checked proof.

(ns wandler.optimize
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.simp :as simp])
  (:import [ansatz.kernel Env TypeChecker]))

(defn- mk-st
  "A tc-state, optionally carrying a local context `lctx` ({fvar-id → {:name
   :type}}) so terms with free variables (an in-progress `a/defn` body) type."
  [env lctx]
  (if (seq lctx) (tc/mk-tc-state-with-locals env lctx) (tc/mk-tc-state env)))

;; When true, a/defn's optimize-body uses EQUALITY SATURATION (the e-graph) instead of the greedy
;; one-at-a-time cost search — it considers all law combinations and extracts the globally cheapest
;; equivalent plan (catching reorders greedy misses), each round kernel-certified. Opt-in per the
;; cost (saturation is heavier): `(binding [opt/*use-egraph* true] (a/defn …))`. Default greedy.
(def ^:dynamic *use-egraph* false)

(def fusion-lemmas
  "Oriented Init fusion laws — CONFLUENT deforestation: each LHS→RHS removes an
   intermediate list, driving a map/filter/fold pipeline to a SINGLE pass.
     List.map_map        map g (map f l)       → map (g∘f) l
     List.filter_filter  filter p (filter q l) → filter (q && p) l
     List.foldl_map      foldl f i (map g l)   → foldl (f∘g-step) i l
     List.foldl_filter   foldl f i (filter p l)→ foldl (if p then f else id) i l
     List.map_id         map id l              → l
   A `foldl` over `map g (filter p xs)` cascades foldl_map then foldl_filter into
   ONE foldl over xs (stream fusion). filter_map / map_filter REORDER rather than
   deforest — they live in the cost layer (could break confluence here). Init only."
  ["List.map_map" "List.filter_filter" "List.foldl_map" "List.foldl_filter" "List.map_id"])

(def string-lemmas
  "String monoid simplifications (Init-only). `(String, ++, \"\")` is a MONOID —
   `String.append_assoc` + `String.append_empty` + `String.empty_append` — and `length`
   is a homomorphism to `(Nat, +, 0)` via `String.length_append`. The two IDENTITY laws
   are CONFLUENT (they only ever delete a redundant empty concat), so they ride the
   default fusion set; `append_assoc` is a normalizer kept OUT (it can loop). Note that
   string-ELEMENT pipelines (`map trim (map toUpper xs)`, filter by a string predicate)
   already fuse via the ordinary collection laws — strings ride `map_map`/`filter_filter`
   with no string-specific rule; these laws are only for `++`-chain simplification."
  ["String.append_empty" "String.empty_append"])

(def cost-rewrites
  "RELATIONAL / REORDERING laws — NOT confluent, so they are NOT in the default
   fusion set (they could loop with their inverse, and whether they help depends on
   COST). The phase-4 cost driver offers these and keeps one only if it both
   verifies AND lowers estimated cost.
     List.filter_map  filter p (map g l) → map g (filter (p∘g) l)  (filter before map)
   Relational pushdowns over Map.group_by / Map.join (filter-pushdown-into-join,
   etc.) register here too — each is just an Eq theorem (Init OR one we prove, like
   the Map.* laws), per the rule-from-theorem (`@[csimp]`) design. Provable via the
   same fvar-first method; List.filter_flatMap is the key supporting Init lemma.

     Map.filter_join_pushdown  filter (p∘fst) (Map.join … xs ys) → Map.join … (filter p xs) ys

   That law is our composed theorem (List.filter_flatMap_cond ∘
   List.filter_map_pair_eq_cond) — present in the env only once admitted; a name
   whose lookup fails is silently skipped by make-simp-lemmas. It is a SOAC-count-
   neutral REORDER, so the search gates on `pipeline-cost` (cardinality), not op
   count: filtering xs BEFORE the join is cheaper, so it is auto-adopted + certified
   (see wandler.filter-join-test).

     List.elem_filter_eq_index_probe  filter (elem · ys) xs →
       filter (isSome (lookup · (group_by id ys))) xs   (nested-loop → hash semijoin)

   The semijoin is NOT cardinality-neutral in the PREDICATE: elem is an O(|ys|) scan
   per element, the probe is O(1) after a one-time O(|ys|) index build. So
   `predicate-extra-cost` charges the scan (in·base) vs the build (base) and the
   search adopts the probe form (see wandler.semijoin-test for the certified law).

     List.elem_not_filter_eq_index_probe  the ANTI-join (NOT IN / set difference):
       filter (not ∘ elem · ys) xs → filter (not ∘ isSome (lookup · (group_by id ys))) xs

   Same predicate-cost story (Bool.not is transparent to the scan/build detection)."
  ["List.filter_map" "Map.filter_join_pushdown"
   "List.elem_filter_eq_index_probe" "List.elem_not_filter_eq_index_probe"
   ;; map+filter → ONE pass: map f (filter p l) = filterMap (λx. if p x then some (f x) else
   ;; none) l. SOAC-count win (2→1), so the cost driver adopts it. Built by
   ;; install-filtermap-fusion-law! (Init-only proof: filterMap_eq_map + filterMap_filter).
   "List.map_filter_filterMap"])

(defn optimize-term
  "Rewrite a pipeline kernel `term` under the oriented fusion lemma set (plus any
   `:extra-lemmas` — e.g. proven relational pushdown laws), via the ported simp
   engine. Returns {:term result, :proof (Expr | nil), :changed? bool}. `:proof`
   is a kernel term of type `term = result` (nil when nothing fired — i.e. rfl).
   The proof is checkable independently with `verified-rewrite?`."
  [^Env env term & {:keys [extra-lemmas max-depth lctx] :or {max-depth 40}}]
  (let [st (mk-st env lctx)
        lemmas (simp/make-simp-lemmas env (concat fusion-lemmas string-lemmas extra-lemmas))
        idx (simp/build-lemma-index st env lemmas)
        {:keys [expr proof?]} (simp/simp-expr-result st env idx term max-depth)]
    {:term expr :proof proof? :changed? (not (identical? expr term))}))

(defn- close-over-lctx
  "Abstract the `lctx` free variables (ascending id = telescope order) into `goal`
   (∀-binders) and `proof` (λ-binders), yielding a CLOSED theorem suitable for
   `check-constant`. Binder types may reference earlier fvars; `abstract1` is
   depth-aware, so abstracting from the innermost (highest id) outward keeps them
   well-scoped."
  [lctx goal proof]
  (reduce (fn [[g p] id]
            (let [{:keys [name type]} (get lctx id)
                  nm (or name "x")
                  ty (or type (e/sort' lvl/zero))]
              [(e/forall' nm ty (e/abstract1 g id) :default)
               (e/lam nm ty (e/abstract1 p id) :default)]))
          [goal proof]
          (reverse (sort (keys lctx)))))

(defn verified-rewrite?
  "The SOUNDNESS GATE: independently kernel-check that `result.proof` proves
   `orig = result.term`. Returns true iff the optimizer's proof genuinely
   certifies the rewrite.

   AUTHORITATIVE check: builds the goal `@Eq T orig term`, closes it (and the proof)
   over `lctx`'s free variables, and runs the kernel's STRICT `TypeChecker.check`
   (= Lean's `check` / infer_type_core(e, false)) on the proof — re-checking every
   application argument — then confirms its type is the goal. This is NOT the lenient
   `inferType` (which assumes well-typed input), and unlike `check-constant` it does not
   add to the env (safe on PSS/fork environments). Same strictness that admits mathlib
   declarations. A nil proof is sound only when nothing changed."
  [^Env env orig {:keys [term proof]} & {:keys [lctx]}]
  (if (nil? proof)
    (identical? orig term)
    (try
      (let [st (mk-st env lctx)
            t (tc/infer-type st orig)                    ; carrier type T (orig : T)
            t-sort (#'tc/cached-whnf st (tc/infer-type st t))
            u (if (e/sort? t-sort) (e/sort-level t-sort) lvl/zero)
            goal (e/app* (e/const' (name/from-string "Eq") [u]) t orig term)
            [goal* proof*] (close-over-lctx (or lctx {}) goal proof)
            tc (doto (TypeChecker. env) (.setFuel 50000000))
            proof-type (.check tc proof*)]              ; STRICT: re-checks every app arg
        (boolean (.isDefEq tc proof-type goal*)))
      (catch Throwable _ false))))

(defn optimize
  "Optimize + self-certify in one step. Returns the `optimize-term` result with
   `:verified?` set by the independent kernel check — the value a caller trusts.
   Pass `:lctx` for pipelines with free variables."
  [^Env env term & {:keys [lctx] :as opts}]
  (let [res (apply optimize-term env term (mapcat identity opts))]
    (assoc res :verified? (verified-rewrite? env term res :lctx lctx))))

(defn- ulvl [u] (if (zero? u) lvl/zero (lvl/succ lvl/zero)))
(defn- uconst [s us] (e/const' (name/from-string s) (mapv ulvl us)))

(defn install-filtermap-fusion-law!
  "Add the verified fusion law `map f (filter p l) = filterMap (λx. if p x then some (f x) else
   none) l` to `env` (idempotent; no-op if Init's filterMap_eq_map/filterMap_filter are absent).
   Proof: Eq.trans (Eq.symm (congrFun filterMap_eq_map (filter p l))) filterMap_filter — NO
   induction. Returns the (possibly augmented) env. Used by optimize-body so map∘filter fuses."
  [^Env env]
  (if (or (env/lookup env (name/from-string "List.map_filter_filterMap"))
          (not (env/lookup env (name/from-string "List.filterMap_filter"))))
    env
    (try
      (let [c uconst
            Type0 (e/sort' (lvl/succ lvl/zero))
            fa (e/fvar 9000) fb (e/fvar 9001) ff (e/fvar 9002) fp (e/fvar 9003) fl (e/fvar 9004)
            lctx {9000 {:name "α" :type Type0} 9001 {:name "β" :type Type0}
                  9002 {:name "f" :type (e/forall' "_" fa fb :default)}
                  9003 {:name "p" :type (e/forall' "_" fa (c "Bool" []) :default)}
                  9004 {:name "l" :type (e/app (c "List" [0]) fa)}}
            st (tc/mk-tc-state-with-locals env lctx)
            ListA (e/app (c "List" [0]) fa) ListB (e/app (c "List" [0]) fb)
            Optb (e/app (c "Option" [0]) fb)
            someF (e/app* (c "Function.comp" [1 1 1]) fa fb Optb (e/app (c "Option.some" [0]) fb) ff)
            filterPL (e/app* (c "List.filter" [0]) fa fp fl)
            fmSomeF (e/app* (c "List.filterMap" [0 0]) fa fb someF)
            mapF (e/app* (c "List.map" [0 0]) fa fb ff)
            cf (e/app* (c "congrFun" [1 1]) ListA (e/lam "_" ListA ListB :default)
                       fmSomeF mapF (e/app* (c "List.filterMap_eq_map" [0 0]) fa fb ff) filterPL)
            aT (e/app fmSomeF filterPL) bT (e/app mapF filterPL)
            symm (e/app* (c "Eq.symm" [1]) ListB aT bT cf)
            fmfilter (e/app* (c "List.filterMap_filter" [0 0]) fa fb fp someF fl)
            cT (nth (second (e/get-app-fn-args (tc/infer-type st fmfilter))) 2)
            proof (e/app* (c "Eq.trans" [1]) ListB bT aT cT symm fmfilter)
            [goal* proof*] (close-over-lctx lctx (tc/infer-type st proof) proof)
            cdef (env/mk-def (name/from-string "List.map_filter_filterMap") [] goal* proof*)]
        (env/check-constant env cdef 50000000)              ; verify (throws if unsound)
        (env/add-constant env cdef))
      (catch Throwable _ env))))

;; ---- cost-directed search layer (untrusted; each kept rewrite is certified) --

(def ^:private soac-names
  #{"List.map" "List.filter" "List.filterMap" "List.foldl" "List.foldr" "List.eraseDups"
    "List.mergeSort" "List.flatMap" "Map.group_by" "Map.join"})

(defn soac-cost
  "A static cost estimate: the number of SOAC applications in a term. Each
   List.map/filter/foldl/… is a traversal that (unless it's the single outer
   consumer) allocates an intermediate collection, so FEWER is cheaper — a proxy
   for passes + allocations that the benchmark shows dominates. Cheap, monotone
   under deforestation, and enough to drive the search; a fancier model (selectivity
   tiers à la stratum/datahike) plugs in here."
  [term]
  (let [c (volatile! 0)]
    (letfn [(walk [e]
              (cond
                (e/app? e) (let [[h args] (e/get-app-fn-args e)]
                             (when (and (e/const? h) (soac-names (name/->string (e/const-name h))))
                               (vswap! c inc))
                             (walk h) (run! walk args))
                (e/lam? e) (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                (e/forall? e) (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                :else nil))]
      (walk term))
    @c))

(defn soac-stages
  "Ordered SOAC op short-names in `term` (outermost-first, as encountered), e.g.
   `[\"map\" \"filter\"]` — the pipeline stages, for the plan/explain API."
  [term]
  (let [acc (volatile! [])]
    (letfn [(walk [e]
              (cond
                (e/app? e) (let [[h args] (e/get-app-fn-args e)]
                             (when (and (e/const? h) (soac-names (name/->string (e/const-name h))))
                               (let [n (name/->string (e/const-name h))]
                                 (vswap! acc conj (subs n (inc (.lastIndexOf n "."))))))
                             (walk h) (run! walk args))
                (e/lam? e) (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                (e/forall? e) (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                :else nil))]
      (walk term))
    @acc))

(defn- kernel-primitive?
  "A const we should NOT inline as a helper: a SOAC head or a kernel op (a dotted
   name like `List.map`/`Nat.add`). User helpers from `a/defn` are simple, undotted
   names (`step1`, `enrich`)."
  [nm]
  (or (soac-names nm) (boolean (re-find #"\." nm))))

(defn- user-helpers
  "Set of USER-HELPER const names applied in `term`: undotted consts with a value
   (an `a/defn`'d fn, not a kernel primitive) — the candidates to inline so a pipeline
   split across named steps fuses as if written inline. This is what makes ordinary
   Clojure — small named fns, composed — fuse for free."
  [^Env env term]
  (let [acc (volatile! #{})]
    (letfn [(walk [e]
              (cond
                (e/app? e) (let [[h args] (e/get-app-fn-args e)] (walk h) (run! walk args))
                (e/const? e) (let [nm (name/->string (e/const-name e))]
                               (when (and (not (kernel-primitive? nm))
                                          (not (@acc nm))
                                          (some-> (env/lookup env (name/from-string nm)) .getValue))
                                 (vswap! acc conj nm)
                                 ;; TRANSITIVE: a helper that calls deeper helpers (p3→p2→p1)
                                 ;; fuses end-to-end to ONE pass. `(not (@acc nm))` above
                                 ;; guards against recursive helpers looping.
                                 (walk (.getValue (env/lookup env (name/from-string nm))))))
                (e/lam? e) (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                (e/forall? e) (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                :else nil))]
      (walk term))
    @acc))

(defn- soac-cost-deep
  "`soac-cost`, but a user-helper call is counted by its INLINED body — so the gate
   sees the passes a helper boundary hides (`(map g (step1 xs))` truly costs 2, not 1).
   `seen` guards recursive helpers."
  [^Env env term]
  (let [c (volatile! 0), seen (volatile! #{})]
    (letfn [(walk [e]
              (cond
                (e/app? e) (let [[h args] (e/get-app-fn-args e)]
                             (when (e/const? h)
                               (let [nm (name/->string (e/const-name h))]
                                 (cond
                                   (soac-names nm) (vswap! c inc)
                                   (and (not (kernel-primitive? nm)) (not (@seen nm)))
                                   (when-let [v (some-> (env/lookup env (name/from-string nm)) .getValue)]
                                     (vswap! seen conj nm)
                                     (walk v)))))
                             (walk h) (run! walk args))
                (e/lam? e) (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                (e/forall? e) (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                :else nil))]
      (walk term))
    @c))

(defn unfold-eqn-ci
  "ConstantInfo for `<C>.eq_unfold : ∀args, C args = <whnf body>` (proof `Eq.refl`,
   valid since `C args` is defeq to its body), or nil. Lets simp INLINE the helper C
   during optimization. Sound regardless: the fused result is re-verified independently."
  [^Env env nm]
  (try
    (let [ci (env/lookup env (name/from-string nm))
          V (.getValue ci), T (.type ci)
          arity (loop [v V, a 0] (if (e/lam? v) (recur (e/lam-body v) (inc a)) a))]
      (when (pos? arity)
        (let [[ptys ret] (loop [t T, i 0, acc []]
                           (if (and (< i arity) (e/forall? t))
                             (recur (e/forall-body t) (inc i) (conj acc (e/forall-type t)))
                             [acc t]))]
          (when (= (count ptys) arity)
            (let [fvids (mapv #(+ 8360000 %) (range arity))
                  applied (reduce e/app (e/const' (name/from-string nm) []) (mapv e/fvar fvids))
                  ;; ONE delta-beta step: unfold C to its value, beta the params — yields the
                  ;; SURFACE body (`List.map f xs`), NOT a full whnf (which would expand
                  ;; List.map into brecOn and defeat map_map). `applied` ≡ rhs by defeq, so
                  ;; Eq.refl still proves it.
                  rhs (loop [v V, fids fvids]
                        (if (and (e/lam? v) (seq fids))
                          (recur (e/instantiate1 (e/lam-body v) (e/fvar (first fids))) (rest fids))
                          v))
                  u1 (lvl/succ lvl/zero)
                  mk-eq (fn [hd] (e/app* (e/const' (name/from-string hd) [u1]) ret applied))
                  eq-body (e/abstract-many (e/app (mk-eq "Eq") rhs) fvids)
                  proof-body (e/abstract-many (mk-eq "Eq.refl") fvids)
                  wrap (fn [b lam?]
                         (loop [i (dec arity) b b]
                           (if (neg? i) b
                               (recur (dec i) (if lam?
                                                (e/lam (str "p" i) (nth ptys i) b :default)
                                                (e/forall' (str "p" i) (nth ptys i) b :default))))))]
              (env/mk-thm (name/from-string (str nm ".eq_unfold")) []
                          (wrap eq-body false) (wrap proof-body true)))))))
    (catch Throwable _ nil)))

(defn- with-unfold-lemmas
  "Extend `env` with `<C>.eq_unfold` for each user helper applied in `term`; return
   [env' names]. Definitional lemmas used only to let simp inline helpers during
   optimization — the fused result doesn't reference them and is re-verified, so they
   can't affect soundness."
  [^Env env term]
  (reduce (fn [[e ns] nm]
            (let [un (str nm ".eq_unfold")]
              (cond
                (env/lookup e (name/from-string un)) [e (conj ns un)]
                :else (if-let [ci (unfold-eqn-ci e nm)]
                        (try [(env/check-constant e ci) (conj ns un)]
                             (catch Throwable _ [e ns]))
                        [e ns]))))
          [env []] (user-helpers env term)))

;; ── cardinality-propagation cost (datahike's estimate.cljc, made static) ──────
;; soac-cost counts ops; it can't tell a filter that runs BEFORE a join (small
;; input) from one that runs AFTER it (large input) — both are 2 ops. The cost
;; that the cost-search GATE actually needs is the number of elements PROCESSED,
;; which propagates cardinality through the pipeline. Heuristic, so it only
;; affects search QUALITY — every adopted rewrite is still kernel-certified.

(def ^:private soac-info
  "Per SOAC head: 0-based index of the DRIVING input list, a :kind describing how
   it transforms cardinality, the :pred index (filters) and :rhs list (joins)."
  {"List.map"       {:list 3 :kind :map}
   "List.filter"    {:list 2 :kind :filter :pred 1}
   "List.foldl"     {:list 4 :kind :fold}
   "List.foldr"     {:list 4 :kind :fold}
   "List.length"    {:list 1 :kind :fold}   ; count consumer — the order-invariant boundary
   "List.flatMap"   {:list 3 :kind :expand}
   "List.eraseDups" {:list 2 :kind :dedup}
   "List.mergeSort" {:list 1 :kind :sort}
   "Map.group_by"   {:list 4 :kind :group}
   "Map.join"       {:list 6 :kind :join :rhs 7}})

(def ^:private join-build-weight
  "Hash-join cost asymmetry: the INDEXED side (rhs, `group_by lf ys`) pays this per
   element to BUILD the index; the DRIVER side pays 1 per element to probe (O(1) each).
   >1 so indexing the SMALLER side is cheaper — which is exactly the `Map.join_comm`
   reorder, certifiable for count queries via the `Map.join_length_comm` Perm→Eq bridge."
  2.0)

(def ^:private default-selectivity
  "Static fallback pass-rates by the predicate's head comparator (datahike
   estimate.cljc): equality selective, ranges moderate, ≠ keeps most."
  {:eq 0.1 :range 0.33 :neq 0.9 :other 0.5})

(defn- pred-selectivity
  "Estimate a filter predicate's pass-rate from the comparator heading its
   β-reduced body; unknown predicates → 0.5. A measured profile or a
   refinement-derived bound overrides this via pipeline-cost's :selectivity."
  [pred]
  (let [body (loop [b pred] (if (e/lam? b) (recur (e/lam-body b)) b))
        [h _] (e/get-app-fn-args body)
        nm (when (e/const? h) (name/->string (e/const-name h)))]
    (case nm
      ("Eq" "BEq.beq" "Nat.beq" "Nat.decEq" "decide") (:eq default-selectivity)
      ("Nat.ble" "Nat.blt" "Nat.le" "Nat.lt" "LE.le" "LT.lt" "GE.ge" "GT.gt") (:range default-selectivity)
      ("Ne" "ne") (:neq default-selectivity)
      (:other default-selectivity))))

(def ^:private membership-scan-names
  "Predicate ops whose cost is the SIZE of the list they scan (a per-element O(m)
   membership test)."
  #{"List.elem" "List.contains" "List.elemBy" "List.any" "List.all"})

(def ^:private index-build-names
  "Predicate ops that BUILD a probe index — a one-time O(m) cost (loop-invariant,
   hoisted out of the filter), after which each probe is O(1)."
  #{"Map.group_by"})

(defn- predicate-extra-cost
  "Beyond the default O(1), estimate `[per-element-extra one-time-build]` for a
   filter predicate by scanning its body: a membership SCAN (List.elem … over a
   free list) costs `base` PER element; an index BUILD (Map.group_by) is a ONE-
   TIME `base` with O(1) probes thereafter. This is what lets the cardinality cost
   model value the verified semijoin — nested-loop elem-filter (in·base) versus
   build-once index probe (base + in)."
  [pred base]
  (let [per-el (atom 0.0) one-time (atom 0.0)]
    (letfn [(go [e]
              (cond
                (e/app? e)
                (do (let [[h _] (e/get-app-fn-args e)]
                      (when (e/const? h)
                        (let [n (name/->string (e/const-name h))]
                          (cond (membership-scan-names n) (swap! per-el + base)
                                (index-build-names n)      (swap! one-time + base)))))
                    (go (e/app-fn e)) (go (e/app-arg e)))
                (e/lam? e) (go (e/lam-body e))
                (e/forall? e) (go (e/forall-body e))))]
      (go pred))
    [@per-el @one-time]))

(defn pipeline-resources
  "RESOURCE PROFILE of a SOAC pipeline `term`: {:size <output cardinality> :time <elements
   processed> :memory <peak working set>}. :time is the cardinality-propagation cost (datahike-style,
   made static — each op pays its input size, filters shrink, join/flatMap expand, folds collapse).
   :memory is the MAX over the plan of each node's footprint: streaming ops (map/filter/expand/dedup)
   add NOTHING; join carries its build-side index (O(|build|)); sort/group carry their buffer
   (O(|input or keys|)). This is the dimension the memory-aware physical-strategy choice gates on
   (hoist the index iff build-side ≤ budget, else spill/sort-merge — see docs/PHYSICAL_PLANNING.md).

   Opts:
     :base        source-list size (default 1000)
     :fanout      expand/join multiplicity (default 3)
     :selectivity (fn pred→rate) OR (map pred-string→rate) — measured-profile / refinement override.
     :sizes       per-source {fvar-id→cardinality} (an engine's :estimate)."
  ([term] (pipeline-resources term {}))
  ([term {:keys [base fanout selectivity sizes] :or {base 1000.0 fanout 3.0}}]
   (let [sel (cond (fn? selectivity) selectivity
                   (map? selectivity) (fn [p] (or (get selectivity (e/->string p)) (pred-selectivity p)))
                   :else pred-selectivity)
         size-of (fn [e] (or (when (and sizes (e/fvar? e)) (get sizes (e/fvar-id e))) base))]
     (letfn [(walk [e]                          ; → [size time mem]   (mem = peak working set)
               (let [[h args] (e/get-app-fn-args e)
                     info (when (e/const? h) (soac-info (name/->string (e/const-name h))))]
                 (if (and info (> (count args) (long (:list info))))
                   (let [[in cin min*] (walk (nth args (long (:list info))))]
                     (case (:kind info)
                       :map    [in (+ cin in) min*]                          ; streaming: no extra mem
                       :filter (let [pred (nth args (long (:pred info)))
                                     [per-el one-time] (predicate-extra-cost pred base)]
                                 [(* in (double (sel pred))) (+ cin in (* in per-el) one-time) min*])
                       :fold   [1.0 (+ cin in) min*]                          ; scalar acc: O(1)
                       :expand [(* in fanout) (+ cin in) min*]
                       :dedup  [(* in 0.7) (+ cin in) min*]
                       :sort   [in (+ cin (* in (Math/log (max 2.0 in)))) (max min* in)]  ; in-mem sort buffer
                       :group  [in (+ cin in) (max min* in)]                  ; holds the grouped structure
                       :join   (let [[r cr mr] (walk (nth args (long (:rhs info))))]
                                 ;; OUTPUT order-invariant (min). TIME = probe driver `in` + BUILD the
                                 ;; INDEXED side `r` at join-build-weight (the only order-dependent
                                 ;; term → index the smaller side, Map.join_comm). MEMORY = the
                                 ;; build-side index footprint `r` (the thing a hoist materializes;
                                 ;; O(|keys|) once pre-aggregated). The memory-aware planner hoists
                                 ;; iff r ≤ budget, else spills.
                                 [(* (min in r) fanout) (+ cin cr in (* join-build-weight r)) (max min* mr r)])
                       [in cin min*]))
                   [(size-of e) 0.0 0.0])))]
       (let [[s t m] (walk term)] {:size s :time t :memory m})))))

(defn pipeline-cost
  "Estimated total elements PROCESSED by SOAC pipeline `term` (the :time projection of
   `pipeline-resources`): datahike-style cardinality propagation, made static. Lower is cheaper;
   drives optimize-cost's adopt gate so a SOAC-count-neutral REORDER is preferred by its cardinality
   win. See `pipeline-resources` for the full {time, memory} profile + opts."
  ([term] (pipeline-cost term {}))
  ([term opts] (:time (pipeline-resources term opts))))

;; ---- join reordering (#29): the Perm→Eq bridge, cost-driven --------------------

(defn- count-join
  "Match `List.length (Map.join K X Y dec kf lf xs ys)` — a COUNT over a join, the
   ORDER-INVARIANT boundary where the bag-equivalence `Map.join_comm` becomes a real
   Eq. Returns the join's 8 args (the reorder telescope), or nil."
  [term]
  (let [[h args] (e/get-app-fn-args term)]
    (when (and (e/const? h) (= "List.length" (name/->string (e/const-name h))) (>= (count args) 2))
      (let [[jh jargs] (e/get-app-fn-args (nth args 1))]
        (when (and (e/const? jh) (= "Map.join" (name/->string (e/const-name jh))) (>= (count jargs) 8))
          (vec (take 8 jargs)))))))

(defn try-join-reorder
  "Cost-driven JOIN REORDER for count queries, certified by the `Map.join_length_comm`
   Perm→Eq bridge. If `term` = length (join … kf lf xs ys) and the bridge law is admitted,
   it rewrites to length (join … lf kf ys xs) — swapping which side is INDEXED. Adopt iff
   that strictly lowers `pipeline-cost` (index the smaller side) AND the bridge proof
   strict-certifies the Eq (`verified-rewrite?`). Returns {:term :proof :verified? true
   :changed? true} or nil.

   This is the dedicated path the simp cost-rewrite pool CANNOT take: `Map.join_length_comm`
   is PERMUTATIVE (LHS ~ RHS modulo arg-swap), so simp's perm-guard would canonicalize it to
   a fixed orientation rather than choose by cost. Here we apply the law directly and let the
   cardinality cost decide — soundness still rests entirely on `verified-rewrite?`."
  [^Env env term & {:keys [lctx selectivity sizes]}]
  (when-let [jargs (count-join term)]
    (let [proof (apply e/app* (e/const' (name/from-string "Map.join_length_comm") []) jargs)
          st (mk-st env lctx)
          ;; infer-type fails gracefully (→ nil) if the bridge law isn't registered
          ptype (try (tc/infer-type st proof) (catch Throwable _ nil))
          [_ eqargs] (when ptype (e/get-app-fn-args ptype))]   ; @Eq Nat LHS RHS
      (when (and eqargs (>= (count eqargs) 3))
        (let [rhs (nth eqargs 2)
              res {:term rhs :proof proof :changed? true :rw :join-reorder}]
          (when (and (< (pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                        (pipeline-cost term {:selectivity selectivity :sizes sizes}))
                     (verified-rewrite? env term res :lctx lctx))
            (assoc res :verified? true)))))))

(defn try-count-factor
  "Cost-driven COUNT FACTORIZATION — aggregation-THROUGH-join (the FAQ asymptotic win,
   count instance). If `term` = length (Map.join … kf lf xs ys) and `Map.count_join_factor`
   is admitted, rewrite to  sum (map (λx. length (bucket (kf x) ys)) xs)  — count the join
   WITHOUT materializing the |xs|·|ys| product (no pairs built; pipeline-cost charges that
   product on the LHS, ~0 on the factored sum). Adopt iff it strictly lowers pipeline-cost
   AND the proof strict-certifies. Returns {:term :proof :verified? :changed? :rw} or nil.

   Same dedicated-path shape as `try-join-reorder`: applied directly (not via the simp pool)
   because the law's RHS is a different SOAC SHAPE the cost-search must choose by cardinality,
   not op-count (soac-cost actually RISES 1→2; the materialization win is only visible to
   pipeline-cost). Soundness rests entirely on `verified-rewrite?`. The law itself is proven
   on Map.join's flatMap form via length_flatMap+length_map (see wandler.factor-test)."
  [^Env env term & {:keys [lctx selectivity sizes]}]
  (when-let [jargs (count-join term)]
    (let [proof (apply e/app* (e/const' (name/from-string "Map.count_join_factor") []) jargs)
          st (mk-st env lctx)
          ptype (try (tc/infer-type st proof) (catch Throwable _ nil))   ; nil if law absent
          [_ eqargs] (when ptype (e/get-app-fn-args ptype))]             ; @Eq Nat LHS RHS
      (when (and eqargs (>= (count eqargs) 3))
        (let [rhs (nth eqargs 2)
              res {:term rhs :proof proof :changed? true :rw :count-factor}]
          (when (and (< (pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                        (pipeline-cost term {:selectivity selectivity :sizes sizes}))
                     (verified-rewrite? env term res :lctx lctx))
            (assoc res :verified? true)))))))

(declare compose-trans mentions-const?)

(defn- fold-join
  "Match `List.foldl op e (Map.join K X Y dec kf lf xs ys)` — ANY aggregate (count/sum/max/…) folded
   over a join. Returns {:S :op :e :jargs} (jargs = the join's 8 args), or nil."
  [term]
  (let [[h args] (e/get-app-fn-args term)]
    (when (and (e/const? h) (= "List.foldl" (name/->string (e/const-name h))) (>= (count args) 5))
      (let [[S _PXY op ini lst] (take 5 args)
            [jh jargs] (e/get-app-fn-args lst)]
        (when (and (e/const? jh) (= "Map.join" (name/->string (e/const-name jh))) (>= (count jargs) 8))
          {:S S :op op :e ini :jargs (vec (take 8 jargs))})))))

(defn try-fold-factor
  "Cost-driven AGGREGATION-THROUGH-JOIN factorization, GENERAL over the aggregate (count/sum/max/any
   foldl — `Map.foldl_join_factor`, no monoid axioms). FUSES first (so `foldl op e (map proj (join))`
   collapses via foldl_map to `foldl op' e (join)`), then if it's a foldl over a Map.join, rewrites
   to the per-key nested foldl that NEVER materializes the |xs|·|ys| pairs:
     foldl op e (join kf lf xs ys) = foldl (λacc x. foldl (λacc' y. op acc' (x,y)) acc (bucket x)) e xs
   Adopt iff it strictly lowers pipeline-cost (the LHS pays the join product, the RHS ~0) AND the
   composed (fuse ∘ factor) proof certifies. Soundness rests on `verified-rewrite?`."
  [^Env env term & {:keys [lctx selectivity sizes]}]
  (when (mentions-const? term "Map.join")          ; cheap guard — skip the internal fuse otherwise
   (let [fused  (optimize env term :lctx lctx)
         fterm  (if (:verified? fused) (:term fused) term)
         fproof (when (:verified? fused) (:proof fused))]
    (when-let [{:keys [S op e jargs]} (fold-join fterm)]
      (let [[K X Y dec kf lf xs ys] jargs
            factor-pf (e/app* (e/const' (name/from-string "Map.foldl_join_factor") [])
                              K X Y S dec op e kf lf xs ys)
            st (mk-st env lctx)
            ptype (try (tc/infer-type st factor-pf) (catch Throwable _ nil))   ; nil if law absent
            [_ eqargs] (when ptype (e/get-app-fn-args ptype))]                 ; @Eq S LHS RHS
        (when (and eqargs (>= (count eqargs) 3))
          (let [rhs (nth eqargs 2)
                proof (compose-trans env lctx term fterm rhs fproof factor-pf)
                res {:term rhs :proof proof :changed? true :rw :fold-factor}]
            (when (and (< (pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                          (pipeline-cost term {:selectivity selectivity :sizes sizes}))
                       (verified-rewrite? env term res :lctx lctx))
              (assoc res :verified? true)))))))))

(defn- compose-trans
  "Eq.trans of `p1` (a=b) and `p2` (b=c) → a proof of a=c. nil proofs are identities
   (a=a), so `(compose-trans … a a c nil p2) = p2` and `(… a b b p1 nil) = p1`. Builds
   `@Eq.trans.{u} T a b c p1 p2` with T = type of `a`, u its sort level."
  [^Env env lctx a b c p1 p2]
  (cond
    (nil? p1) p2
    (nil? p2) p1
    :else (let [st (mk-st env lctx)
                t (tc/infer-type st a)
                t-sort (#'tc/cached-whnf st (tc/infer-type st t))
                u (if (e/sort? t-sort) (e/sort-level t-sort) lvl/zero)]
            (e/app* (e/const' (name/from-string "Eq.trans") [u]) t a b c p1 p2))))

(defn try-grace-hash
  "PHYSICAL grace-hash spill: when the join's build-side index would EXCEED the memory budget,
   evaluate `foldl op e (Map.join xs ys)` in budget-sized BLOCKS of the build side (O(block) peak
   memory). Rewrites to `foldl (λacc blk. foldl op acc (join xs blk)) e (List.chunk B ys)` and
   certifies it by composing  congrArg (List.flatten_chunk B ys).symm  with  Map.foldl_join_blockfold
   — exactly the chain proven in wandler.grace-hash-test. The left-commutativity hypothesis is built
   as `rfl` (sound for COUNT and any p-independent aggregate; the kernel rejects it for non-lcomm ops,
   so verified-rewrite? gates correctness). Fires only when an explicit `memory-budget` is set AND the
   index estimate exceeds it. B (block size) is a heuristic from the budget; correctness is independent
   of B, only the peak-memory guarantee depends on it."
  [^Env env term & {:keys [lctx selectivity sizes memory-budget block-size]}]
  (when (and memory-budget (mentions-const? term "Map.join"))
    (let [fused  (optimize env term :lctx lctx)
          fterm  (if (:verified? fused) (:term fused) term)
          fproof (when (:verified? fused) (:proof fused))]
      (when-let [{:keys [S op e jargs]} (fold-join fterm)]
        (let [[K X Y dec kf lf xs ys] jargs
              idx-mem (:memory (pipeline-resources term {:selectivity selectivity :sizes sizes}))]
          (when (> (double idx-mem) (double memory-budget))
            (let [nm   (fn [s] (name/from-string s))
                  z    lvl/zero  L1 (lvl/succ z)
                  PXY  (e/app* (e/const' (nm "Prod") [z z]) X Y)
                  listY (e/app (e/const' (nm "List") [z]) Y)
                  B    (e/lit-nat (long (max 1 (or block-size (long (/ (double memory-budget) 1000.0))))))
                  chunked (e/app* (e/const' (nm "List.chunk") []) Y B ys)
                  flatChunked (e/app* (e/const' (nm "List.flatten") [z]) Y chunked)
                  joinW (fn [w] (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs w))
                  foldlG (fn [l] (e/app* (e/const' (nm "List.foldl") [z z]) S PXY op e l))
                  midL (foldlG (joinW ys)) midR (foldlG (joinW flatChunked))
                  fc    (e/app* (e/const' (nm "List.flatten_chunk") []) Y B ys)
                  fcSym (e/app* (e/const' (nm "Eq.symm") [L1]) listY flatChunked ys fc)
                  motive (e/lam "w" listY (e/app* (e/const' (nm "List.foldl") [z z]) S PXY op e (joinW (e/bvar 0))) :default)
                  congr (e/app* (e/const' (nm "congrArg") [L1 L1]) listY S ys flatChunked motive fcSym)
                  lc   (e/lam "a" S (e/lam "u" PXY (e/lam "v" PXY
                         (e/app* (e/const' (nm "Eq.refl") [L1]) S
                                 (e/app* op (e/app* op (e/bvar 2) (e/bvar 1)) (e/bvar 0))) :default) :default) :default)
                  bf   (e/app* (e/const' (nm "Map.foldl_join_blockfold") []) K X Y dec kf lf S op lc e xs chunked)
                  st   (mk-st env lctx)
                  bftype (try (tc/infer-type st bf) (catch Throwable _ nil))   ; @Eq S midR rhs (nil if law absent)
                  [_ bfargs] (when bftype (e/get-app-fn-args bftype))]
              (when (and bfargs (>= (count bfargs) 3))
                (let [rhs    (nth bfargs 2)
                      result-pf (e/app* (e/const' (nm "Eq.trans") [L1]) S midL midR rhs congr bf)
                      proof  (compose-trans env lctx term fterm rhs fproof result-pf)
                      res {:term rhs :proof proof :changed? true :rewrites [:grace-hash]
                           :physical {:strategy :grace-hash :index-est idx-mem :budget memory-budget}
                           :cost (pipeline-cost rhs {:selectivity selectivity :sizes sizes})}]
                  (when (verified-rewrite? env term res :lctx lctx)
                    (assoc res :verified? true)))))))))))

(defn- separable-sum-g
  "Detect a SEPARABLE additive aggregate op: `λacc:Nat. λp:(X×Y). Nat.add acc (g (Prod.snd X Y p))`
   where `g : Y → Nat` reads only the right (build) side. Returns g (a CLOSED Y→Nat term, i.e. no
   dependence on acc/p) or nil. This is the exact op shape `Map.foldl_join_sum_factor` is stated for,
   so a match means the law's LHS is def-eq to the term and the pre-aggregated index applies."
  [op]
  (when (e/lam? op)
    (let [b1 (e/lam-body op)]
      (when (e/lam? b1)
        (let [body (e/lam-body b1)
              [h args] (e/get-app-fn-args body)]
          (when (and (e/const? h) (= "Nat.add" (name/->string (e/const-name h))) (= 2 (count args))
                     (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                     (e/app? (second args)))
            (let [a2 (second args) G (e/app-fn a2) sndt (e/app-arg a2)
                  [sh sargs] (e/get-app-fn-args sndt)]
              (when (and (e/const? sh) (= "Prod.snd" (name/->string (e/const-name sh)))
                         (= 3 (count sargs)) (e/bvar? (nth sargs 2)) (= 0 (e/bvar-idx (nth sargs 2)))
                         (not (e/has-loose-bvars? G)))
                G))))))))

(defn try-pre-agg-index
  "PHYSICAL pre-aggregated (FAQ) index for a SEPARABLE SUM aggregate over a join — the O(distinct-keys)
   in-memory strategy. When `foldl (λacc p. acc + g (snd p)) e (Map.join … xs ys)` (sum of a right-side
   field), rewrite via `Map.foldl_join_sum_factor` to `foldl (λacc x. acc + getD (lookup (kf x) PREIDX)
   0) e xs`, where PREIDX = the group-by index with each bucket PRE-SUMMED once — held memory O(distinct
   keys), not O(|ys|). Certified by composing fusion ∘ the sum-factor law (proven in proofs.clj §6 from
   foldl_join_factor + foldl_congr + foldl_add_init + lookup_map_kv + getD_map). The `:ndv` oracle
   (HyperLogLog / datahike schema / stratum estimate, à la DuckDB `cardinality_estimator.cpp`) gives the
   held-index estimate (≤ |ys|); soundness of the SMALL estimate rests on the index actually being
   pre-summed (which the law proves). Soundness of the rewrite rests on `verified-rewrite?`."
  [^Env env term & {:keys [lctx selectivity sizes memory-budget ndv]}]
  (when (mentions-const? term "Map.join")
    (let [fused  (optimize env term :lctx lctx)
          fterm  (if (:verified? fused) (:term fused) term)
          fproof (when (:verified? fused) (:proof fused))]
      (when-let [{:keys [S op e jargs]} (fold-join fterm)]
        (when (and (e/const? S) (= "Nat" (name/->string (e/const-name S))))
          (when-let [g (separable-sum-g op)]
            (let [[K X Y dec kf lf xs ys] jargs
                  ;; PRE-AGG is an ndv-DRIVEN choice (DuckDB PerfectHashAggregate gating): adopt only
                  ;; when the oracle gives a build-side distinct-count STRICTLY below the raw build size,
                  ;; i.e. a real held-memory win (O(distinct keys) ≪ O(|ys|)). Without ndv, the default
                  ;; fold-factor (+ hoist) plan stands — pre-agg's win isn't visible to the static model.
                  build-mem (:memory (pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                  ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
              (when (and ndv-est (< (double ndv-est) (double build-mem)))
                (let [law (e/app* (e/const' (name/from-string "Map.foldl_join_sum_factor") [])
                                  K X Y dec g kf lf e xs ys)
                      st (mk-st env lctx)
                      ptype (try (tc/infer-type st law) (catch Throwable _ nil))   ; nil if law absent
                      [_ eqargs] (when ptype (e/get-app-fn-args ptype))]           ; @Eq Nat LHS RHS
                  (when (and eqargs (>= (count eqargs) 3))
                    (let [rhs (nth eqargs 2)
                          proof (compose-trans env lctx term fterm rhs fproof law)
                          res {:term rhs :proof proof :changed? true :rewrites [:pre-agg-index]
                               :physical {:strategy :in-memory-hash :index-est (double ndv-est) :budget (or memory-budget 1.0e8)}
                               :cost (pipeline-cost rhs {:selectivity selectivity :sizes sizes})}]
                      (when (and (< (pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                                    (pipeline-cost term {:selectivity selectivity :sizes sizes}))
                                 (verified-rewrite? env term res :lctx lctx))
                        (assoc res :verified? true)))))))))))))

;; ---- physical: loop-invariant index hoisting (LICM), memory-gated ----------------
(defn- collect-closed-group-bys
  "Distinct CLOSED (no loose bvars ⇒ loop-invariant) `Map.group_by` subterms that occur UNDER a
   binder — the index builds a factorized join recomputes per row. (Under-binder only, so an already
   hoisted top-level index isn't re-collected.)"
  [term]
  (let [acc (atom [])]
    (letfn [(go [t under?]
              (let [[h _] (e/get-app-fn-args t)
                    hn (when (e/const? h) (name/->string (e/const-name h)))]
                (when (and under? (= hn "Map.group_by") (not (e/has-loose-bvars? t))
                           (not (some #(.equals ^Object % t) @acc)))
                  (swap! acc conj t))
                (cond (e/app? t)    (do (go (e/app-fn t) under?) (go (e/app-arg t) under?))
                      (e/lam? t)    (do (go (e/lam-type t) under?) (go (e/lam-body t) true))
                      (e/forall? t) (do (go (e/forall-type t) under?) (go (e/forall-body t) true)))))]
      (go term false))
    @acc))

(defn- replace-closed
  "Replace every occurrence of the CLOSED subterm `s` with `F` (also closed) in `t`."
  [t s F]
  (cond (.equals ^Object t s) F
        (e/app? t)    (e/app (replace-closed (e/app-fn t) s F) (replace-closed (e/app-arg t) s F))
        (e/lam? t)    (e/lam (e/lam-name t) (replace-closed (e/lam-type t) s F)
                             (replace-closed (e/lam-body t) s F) (e/lam-info t))
        (e/forall? t) (e/forall' (e/forall-name t) (replace-closed (e/forall-type t) s F)
                                 (replace-closed (e/forall-body t) s F) (e/forall-info t))
        :else t))

(defn hoist-invariant-indices
  "LICM (the in-memory-hash physical strategy): lift loop-invariant index builds — closed
   `Map.group_by` subterms inside a fold — into β-redexes ABOVE the fold, so each index is built
   ONCE instead of re-bucketed per row (O(N) instead of O(N²)). The result is BETA-EQUIVALENT to
   `term`, so an existing `orig ≡ term` certificate still holds (def-eq absorbs the β-step). The
   caller MEMORY-GATES this (hoist iff the held index fits the budget). See docs/PHYSICAL_PLANNING.md."
  [^Env env lctx term]
  (let [st (mk-st env lctx)
        ;; only SATURATED group_bys (type = a Map value, not a function) — a partial `Map.group_by f`
        ;; used as a higher-order fn is not a built index and would codegen under-applied.
        gbs (->> (collect-closed-group-bys term)
                 (keep (fn [s] (let [T (try (tc/infer-type st s) (catch Throwable _ nil))]
                                 (when (and T (not (e/forall? (#'tc/cached-whnf st T)))) [s T])))))
        tagged (map-indexed (fn [i [s T]] [s (+ 990000 i) T]) gbs)]
    (if (empty? tagged)
      term
      (let [term' (reduce (fn [t [s F _]] (replace-closed t s (e/fvar F))) term tagged)]
        (reduce (fn [body [s F T]] (e/app (e/lam "idx" T (e/abstract1 body F) :default) s))
                term' tagged)))))

(def ^:private rewrite-descriptions
  {:fold-factor  "aggregation pushed THROUGH the join (the |L|·|R| product is never materialized)"
   :count-factor "count pushed through the join"
   :join-reorder "join REORDERED to index the smaller side"
   :hoist-index  "in-memory HASH join — index built once, hoisted out of the row loop"
   :nested-loop  "NESTED-LOOP join — per-row filter, no held index"
   :grace-hash   "GRACE-HASH spill — build side processed in budget-sized blocks (List.chunk)"
   :pre-agg-index "PRE-AGGREGATED index — each join bucket pre-summed once (held memory O(distinct keys))"
   :egraph       "e-graph equality saturation"})

(defn explain
  "Human-readable account of what `optimize-cost` did — the relational/PHYSICAL strategy
   (in-memory hash vs nested-loop) with the MEMORY reasoning behind the choice, the algebraic
   rewrites, and the certificate. For the REPL: `(println (opt/explain res))`. The resource-aware
   physical decision is legible: which strategy, and why (index estimate vs budget)."
  [result]
  (let [rw (:rewrites result)
        phys (:physical result)
        rewrites (keep rewrite-descriptions rw)
        strlaws  (filter string? rw)]
    (str "verified plan" (when-not (:changed? result) " (unchanged)") "\n"
         (when (seq rewrites) (str "  rewrites: " (clojure.string/join "; " rewrites) "\n"))
         (when phys
           (str "  physical: "
                (case (:strategy phys)
                  :in-memory-hash "IN-MEMORY HASH (build the index once)"
                  :nested-loop    "NESTED-LOOP (stream, no held index)"
                  :grace-hash     "GRACE-HASH (spill: build side in budget-sized blocks)"
                  :pre-agg-index  "PRE-AGGREGATED HASH (buckets pre-summed; O(distinct keys))"
                  (str (:strategy phys)))
                (format " — index est ~%.0f %s budget %s\n"
                        (double (:index-est phys))
                        (if (<= (double (:index-est phys)) (double (:budget phys))) "≤" ">")
                        (if (>= (double (:budget phys)) 1.0e8) "(default)" (format "%.0f" (double (:budget phys)))))))
         (when (seq strlaws) (str "  laws:     " (clojure.string/join ", " strlaws) "\n"))
         "  proof:    " (if (:verified? result) "optimized ≡ original (kernel-certified)" "UNVERIFIED"))))

(defn optimize-cost
  "Cost-directed optimization (the SEARCH layer). Always applies the confluent
   fusion set; then GREEDILY tries cost-rewrites (filter_map, relational
   pushdowns) — adopting one only when the re-optimized term both VERIFIES and has
   strictly lower `soac-cost`. The search is untrusted; soundness rests entirely
   on each adopted step being kernel-certified (`verified?`). Returns the
   `optimize` result plus `:rewrites` (the cost-rewrites adopted) and `:cost`.

   FIRST tries a certified, cost-lowering JOIN REORDER (`try-join-reorder`, the
   `Map.join_comm` Perm→Eq bridge for count queries). If it fires, the REORDERED term
   is then fused, and the reorder proof is composed with the fusion proof via
   `Eq.trans` — so a count-join is reordered AND deforested in one kernel-certified
   step. Falls back to the no-reorder search if the composed proof doesn't verify.

   `:selectivity` (a map pred-string→rate, or fn pred→rate) is threaded to
   `pipeline-cost` — pass a MEASURED profile here to drive the search with real
   per-predicate pass-rates (see `ansatz.core/measure-selectivity`). Defaults to
   the static heuristic.

   `:use-egraph?` swaps the greedy one-at-a-time search for EQUALITY SATURATION
   (`wandler.optimize.egraph/saturate-and-extract`): saturate the e-graph with all
   laws and extract the cost-minimal equivalent plan, interleaved with simp fusion.
   Explores rewrite COMBINATIONS greedy ordering can miss; each step still
   kernel-certified. Falls back to the greedy result if saturation doesn't verify."
  [^Env env term & {:keys [lctx pool selectivity sizes use-egraph? skip-reorder? extra-lemmas memory-budget ndv] :or {pool cost-rewrites}}]
  (let [pc (fn [t] (pipeline-cost t {:selectivity selectivity :sizes sizes}))
        ;; PHYSICAL pre-aggregated index (FAQ): a SEPARABLE SUM over a join holds an O(distinct-keys)
        ;; pre-summed index — the best in-memory plan when ndv ≪ |ys|. Try FIRST; adopt when its held
        ;; estimate fits the budget (DuckDB PerfectHashAggregate gating). Certified rewrite.
        pre-agg (when (not skip-reorder?)
                  (try-pre-agg-index env term :lctx lctx :selectivity selectivity :sizes sizes
                                     :memory-budget memory-budget :ndv ndv))
        ;; PHYSICAL grace-hash: if a memory budget is set and the join index would exceed it, spill
        ;; the build side into budget-sized blocks BEFORE factorization (grace-hash is an ALTERNATIVE
        ;; to the in-memory hash/factor, operating on the raw foldl-over-join). Certified rewrite.
        gh (when (and memory-budget (not skip-reorder?))
             (try-grace-hash env term :lctx lctx :selectivity selectivity :sizes sizes :memory-budget memory-budget))
        ;; dedicated count-over-join paths, cost-chosen + certified directly (not via the simp
        ;; pool): FIRST factorize the join away (aggregation-through-join, biggest win), else
        ;; reorder which side is indexed. Both reduce to length/sum over xs, then fuse normally.
        reorder (when-not skip-reorder?
                  (or (try-count-factor env term :lctx lctx :selectivity selectivity :sizes sizes)
                      (try-fold-factor  env term :lctx lctx :selectivity selectivity :sizes sizes)
                      (try-join-reorder env term :lctx lctx :selectivity selectivity :sizes sizes)))]
    (cond
      ;; pre-agg wins when its held index (O(distinct keys)) fits the budget — strictly better than the
      ;; raw factor (O(|ys|) buckets) for separable sums. Else fall through to grace-hash / factor.
      (and pre-agg (:verified? pre-agg)
           (<= (double (:index-est (:physical pre-agg))) (double (or memory-budget 1.0e8))))
      pre-agg
      (:verified? gh) gh
      (and reorder (:verified? reorder))
      ;; a pre-rewrite fired → fuse its result, then compose proofs (pre ∘ fuse).
      (let [sub (optimize-cost env (:term reorder) :lctx lctx :pool pool :extra-lemmas extra-lemmas
                               :selectivity selectivity :sizes sizes :use-egraph? use-egraph? :skip-reorder? true)
            composed (compose-trans env lctx term (:term reorder) (:term sub)
                                    (:proof reorder) (:proof sub))
            res {:term (:term sub) :proof composed :changed? true
                 :rewrites (into [(:rw reorder)] (:rewrites sub)) :cost (:cost sub)}
            ;; PHYSICAL strategy: hoist loop-invariant index builds out of the fold (the in-memory
            ;; hash join), making a factorized join O(N) not O(N²). β-equivalent → the composed proof
            ;; still certifies. MEMORY-GATED: only when the held index fits the budget (default
            ;; generous; aggregation-through-join indices are O(distinct keys)).
            res (let [h (hoist-invariant-indices env lctx (:term res))
                      ;; the held-index footprint ≈ the build side: estimate from the ORIGINAL term
                      ;; (which still has the Map.join node; the factorized/hoisted term doesn't).
                      idx-mem (:memory (pipeline-resources term {:selectivity selectivity :sizes sizes}))]
                  (cond
                    ;; FITS the budget → in-memory HASH: hoist the index (β-equiv, proof unchanged).
                    (and (not (.equals ^Object h (:term res))) (<= idx-mem (or memory-budget 1.0e8)))
                    (assoc res :term h :rewrites (conj (:rewrites res) :hoist-index)
                           :physical {:strategy :in-memory-hash :index-est idx-mem :budget (or memory-budget 1.0e8)})
                    ;; EXCEEDS an explicit budget → NESTED-LOOP: bucket_content removes the O(|ys|)
                    ;; index → a per-row filter (O(bucket) memory, no held index). Certified by an
                    ;; Eq law, so compose: orig ≡ factorized (res.proof) ∘ factorized ≡ nested-loop.
                    (and memory-budget (> idx-mem memory-budget))
                    (let [nl (optimize env (:term res) :lctx lctx :extra-lemmas ['Map.bucket_content])]
                      (if (and (:changed? nl) (:verified? nl) (:proof nl))
                        (assoc res :term (:term nl) :rewrites (conj (:rewrites res) :nested-loop)
                               :proof (compose-trans env lctx term (:term res) (:term nl) (:proof res) (:proof nl))
                               :physical {:strategy :nested-loop :index-est idx-mem :budget memory-budget})
                        res))
                    :else res))
            res (assoc res :verified? (verified-rewrite? env term res :lctx lctx))]
        (if (:verified? res)
          res
          ;; composition didn't certify — fall back to the plain (no-reorder) search
          (optimize-cost env term :lctx lctx :pool pool :selectivity selectivity :sizes sizes :extra-lemmas extra-lemmas
                         :use-egraph? use-egraph? :skip-reorder? true)))
      :else
      ;; no reorder → the cost-directed search
      (let [base (optimize env term :lctx lctx :extra-lemmas extra-lemmas)
            base (if (:verified? base) base {:term term :verified? true :changed? false})]
        (if use-egraph?
          ;; e-graph saturation search (resolved lazily to avoid a namespace cycle)
          (let [sat ((requiring-resolve 'wandler.optimize.egraph/saturate-and-extract)
                     env term :lctx lctx :selectivity selectivity)]
            (if (and sat (:verified? sat) (:changed? sat)
                     (< (pc (:term sat)) (pc (:term base))))
              (assoc sat :rewrites [:egraph] :cost (soac-cost (:term sat)))
              (assoc base :rewrites [] :cost (soac-cost (:term base)))))
          ;; greedy cost-directed search (default)
          (loop [best base, remaining pool, applied []]
            (let [cands (keep (fn [r]
                                (let [v (optimize env term :lctx lctx
                                                  :extra-lemmas (concat extra-lemmas (conj applied r)))]
                                  ;; GATE on pipeline-cost (cardinality), not op-count, so a
                                  ;; SOAC-neutral reorder (filter→join) is kept for its
                                  ;; cardinality win. `:cost` still reports soac-cost.
                                  (when (and (:verified? v) (< (pc (:term v)) (pc (:term best))))
                                    [r v])))
                              remaining)]
              (if (empty? cands)
                (assoc best :rewrites applied :cost (soac-cost (:term best)))
                (let [[r v] (apply min-key (comp pc :term second) cands)]
                  (recur v (remove #{r} remaining) (conj applied r)))))))))))

(defn- mentions-const?
  "True if expr `e` mentions the constant named `cname` anywhere (used by the pre-check to keep a
   SOAC-trivial body that nonetheless has a rewritable costly predicate, e.g. List.elem)."
  [e cname]
  (cond
    (e/const? e)  (= cname (name/->string (e/const-name e)))
    (e/app? e)    (or (mentions-const? (e/app-fn e) cname) (mentions-const? (e/app-arg e) cname))
    (e/lam? e)    (or (mentions-const? (e/lam-type e) cname) (mentions-const? (e/lam-body e) cname))
    (e/forall? e) (or (mentions-const? (e/forall-type e) cname) (mentions-const? (e/forall-body e) cname))
    :else false))

(defn optimize-body
  "Optimize the pipeline INSIDE a function body `λp0…λp_{n-1}. pipeline`. Opens
   the `n` parameter binders with fresh fvars (so the pipeline is optimized in
   its proper context, not as a whole-function term that η-collapses), certifies
   the inner rewrite, then re-abstracts. Returns {:term body', :verified?,
   :changed?}; `:term` is the original body unless the rewrite verified. This is
   what `a/defn` calls to get a faster — but proven-equivalent — runtime term."
  [^Env env body n & {:keys [extra-lemmas]}]
  (loop [e body, i 0, fvids [], types [], names []]
    (if (and (< i n) (e/lam? e))
      (let [fid (+ 8800000 i)]
        (recur (e/instantiate1 (e/lam-body e) (e/fvar fid)) (inc i)
               (conj fvids fid) (conj types (e/lam-type e)) (conj names (e/lam-name e))))
      (let [lctx (into {} (map (fn [fid nm ty] [fid {:name (str nm) :type ty}]) fvids names types))
            ;; INLINE named helpers: a pipeline split across `v/defn` steps fuses as if
            ;; written inline (the `.eq_unfold` rules are definitional, generated on the
            ;; fly into env+). Deep cost counts the passes a helper boundary hides, so the
            ;; pre-check + keep-gate are honest.
            [env0 unfold-names] (with-unfold-lemmas env e)
            ;; ensure the map∘filter→filterMap law is available to the cost driver (idempotent;
            ;; verified once, used only for this optimization — does not touch the global env)
            env+ (install-filtermap-fusion-law! env0)
            cost-before (soac-cost-deep env e)
            ;; cheap pre-check: nothing to fuse with < 2 (deep) SOAC ops — skip simp entirely
            ;; (keeps the default-on path free for non-pipeline bodies). EXCEPTION: a single
            ;; `filter` over a membership scan (List.elem) is SOAC-trivial but the scan is O(in·ys)
            ;; — the verified SEMIJOIN rewrites it to a build-once index probe, so don't skip it.
            res (if (and (< cost-before 2) (not (mentions-const? e "List.elem")))
                  {:term e :verified? true :changed? false :rewrites []}
                  ;; cost-directed search (confluent fusion + cost-gated reorderings),
                  ;; each adopted step kernel-certified; helper unfolds inline named steps
                  (optimize-cost env+ e :lctx lctx :use-egraph? *use-egraph*
                                 :extra-lemmas (concat extra-lemmas unfold-names)))
            ;; keep iff verified + changed; AND when helpers were inlined, only if the
            ;; honest SOAC cost strictly DROPPED — so inlining that doesn't fuse (would
            ;; just duplicate code) is reverted to the compact original.
            ok (and (:verified? res) (:changed? res)
                    (or (empty? unfold-names)
                        (< (soac-cost (:term res)) cost-before)))
            reabstract (fn [t]
                         (loop [t t, j (dec (count fvids))]
                           (if (neg? j) t
                               (recur (e/lam (str (nth names j)) (nth types j)
                                             (e/abstract1 t (nth fvids j)) :default)
                                      (dec j)))))]
        {:term (if ok (reabstract (:term res)) body)
         :verified? (:verified? res)
         :changed? (boolean ok)
         :rewrites (:rewrites res)
         ;; plan/explain info: the pipeline stages + pass counts, before/after fusion
         :stages-before (soac-stages e)
         :stages-after (soac-stages (if ok (:term res) e))
         :passes-before cost-before
         :passes-after (soac-cost (if ok (:term res) e))}))))
