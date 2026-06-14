;; Split from the wandler.optimize monolith (cohesion audit item 5): the CERTIFIER —
;; simp-driven rewriting that returns proof terms, and the strict kernel gate
;; (verified-rewrite?). Soundness lives here; everything else is policy.
(ns wandler.optimize.certify
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.simp :as simp])
  (:import [ansatz.kernel Env TypeChecker]))


(defn mk-st
  "A tc-state, optionally carrying a local context `lctx` ({fvar-id → {:name
   :type}}) so terms with free variables (an in-progress `a/defn` body) type."
  [env lctx]
  (if (seq lctx) (tc/mk-tc-state-with-locals env lctx) (tc/mk-tc-state env)))


(def fusion-lemmas
  "Oriented Init fusion laws — CONFLUENT deforestation: each LHS→RHS removes an
   intermediate list, driving a map/filter/fold pipeline to a SINGLE pass.
     List.map_map        map g (map f l)       → map (g∘f) l
     List.filter_filter  filter p (filter q l) → filter (q && p) l
     List.foldl_map      foldl f i (map g l)   → foldl (f∘g-step) i l
     List.foldl_filter   foldl f i (filter p l)→ foldl (if p then f else id) i l
     List.map_id         map id l              → l
     List.map_flatMap    map g (flatMap f l)   → flatMap (map g ∘ f) l
     List.flatMap_map    flatMap f (map g l)   → flatMap (f ∘ g) l
     List.filter_flatMap    filter p (flatMap f l)     → flatMap (filter p ∘ f) l
     List.foldl_flatMap     foldl f i (flatMap g l)    → foldl (λa x. foldl f a (g x)) i l
     List.foldr_flatMap     foldr f i (flatMap g l)    → foldr (λx a. foldr f a (g x)) i l
     List.map_filterMap     map g (filterMap f l)      → filterMap (g <$> ∘ f) l
     List.filterMap_map     filterMap f (map g l)      → filterMap (f ∘ g) l
     List.filterMap_filterMap filterMap g (filterMap f l) → filterMap (f >=> g) l
     List.filterMap_flatMap filterMap g (flatMap f l)  → flatMap (filterMap g ∘ f) l
   (filter_flatMap pushes filter into a flatMap body whose fn may return a literal list, which
   simp reduces by unfolding List.filter into its `match_1` auxiliary — ansatz.codegen now
   unfolds match auxiliaries to the `.rec` path, so this codegens cleanly.)
   A `foldl` over `map g (filter p xs)` cascades foldl_map then foldl_filter into
   ONE foldl over xs (stream fusion). The flatMap (mapcat) and filterMap laws extend
   the SAME deforestation to mapcat-/filterMap-bearing pipelines (each LHS→RHS still
   strictly removes an intermediate list, so confluence is preserved). filter_map /
   map_filter REORDER rather than deforest — they live in the cost layer (could break
   confluence here). Init only."
  ["List.map_map" "List.filter_filter" "List.foldl_map" "List.foldl_filter" "List.map_id"
   "List.map_flatMap" "List.flatMap_map" "List.filter_flatMap" "List.foldl_flatMap" "List.foldr_flatMap"
   "List.map_filterMap" "List.filterMap_map" "List.filterMap_filterMap" "List.filterMap_flatMap"])


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


(def soac-names
  #{"List.map" "List.filter" "List.filterMap" "List.foldl" "List.foldr" "List.eraseDups"
    "List.mergeSort" "List.flatMap" "Map.group_by" "Map.join"})

(defn kernel-primitive?
  "A const we should NOT inline as a helper: a SOAC head or a kernel op (a dotted
   name like `List.map`/`Nat.add`). User helpers from `a/defn` are simple, undotted
   names (`step1`, `enrich`)."
  [nm]
  (or (soac-names nm) (boolean (re-find #"\." nm))))

(defn user-helpers
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

(defn with-unfold-lemmas
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
