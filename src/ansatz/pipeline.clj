;; Wandler runtime — the a/defn CODEGEN + define-verified ENGINE + optimizer REPORTING,
;; carved out of ansatz.core (the pure DSL: kernel-term builder + tactics + a/theorem/a/inductive).
;; This namespace is what makes a verified function actually RUN and OPTIMIZE. Loaded when wandler
;; is present; ansatz.core's `defn`/`explain` shells delegate here via requiring-resolve.
(ns ansatz.pipeline
  "Wandler runtime: a/defn codegen, define-verified engine, optimizer reporting (carved from ansatz.core)."
  (:require [clojure.java.io]
            [clojure.string]
            [clojure.core.reducers :as ccr]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.omega :as omega]
            [ansatz.inductive :as inductive]
            [ansatz.surface.match :as surface-match]
            [ansatz.config :as config]
            [ansatz.core :as a
             :refer [sexp->ansatz parse-params build-telescope structure-registry
                     run-tactic context try-synthesize-instance auto-elaborate
                     get-arg-type whnf-ty resolve-basic-instance record-field-hint
                     *scope-types* *current-lctx* *optimize* *verbose*
                     ansatz-env ansatz-instance-index env instance-index make-context fork-context]])
  (:import [ansatz.kernel ConstantInfo]))

(declare explain plan plan-str compute-arity nary-op prim-tag monoid-fold-op
         emit-hinted-fn eta-saturate ansatz->clj walk-subterms filter-predicates
         measure-selectivity profile-selectivity optimize-measured replace-rec-calls
         build-invimage-type discharge-decreasing-proof tag-kernel-fn custom-sizeof-fn
         wrap-measure-with-sizeof nullary-ctor-name inductive-rep ctor-rec-fields
         structuralize-body define-verified-wf record-coerce-form record-entry-coerce
         inject-record-coercions define-verified)

;; ===== moved from core.clj lines 79,86 =====
;; Arity registry for Clojure compilation — following Lean 4's LCNF arity analysis.
;; Maps Name-string → {:arity n :erased k} where n = explicit params, k = erased prefix.
;; Used by ansatz->clj to emit flat multi-arg calls (FAP) instead of curried calls.
(defonce ^{:doc "Arity registry for compiled functions."} arity-registry (atom {}))

(defonce ^{:doc "Per-fn optimization summary (set by define-verified when *optimize*):
                 {fn-name-str → {:changed? :verified? :rewrites :cost}}. Read via `explain`."}
  optimization-registry (atom {}))

;; ===== moved from core.clj lines 88,139 =====
(clojure.core/defn explain
  "What the verified optimizer did to `fn-name` (a symbol/string): a map with
   :changed? (was the runtime term rewritten), :verified? (kernel-checked
   orig=optimized), :rewrites (cost-rewrites adopted beyond confluent fusion),
   and :cost (final SOAC-op count). nil if the fn wasn't defined under *optimize*."
  [fn-name]
  (when-let [info (get @optimization-registry (str fn-name))]
    (select-keys info [:changed? :verified? :rewrites])))

(clojure.core/defn plan
  "A datahike-`explain`-style report of how the verified optimizer compiled `fn-name` (the
   pipeline plan): the SOAC stages and pass count before vs after fusion, the laws applied, and
   whether the rewrite is kernel-certified (optimized ≡ naive). Pass `samples` (a seq of inputs)
   to also PROFILE: input/output cardinality, overall selectivity, and the fused runtime in ms —
   measured, NOT forcing any boundary verification. Returns a map; see `plan-str` to print it."
  [fn-name & [samples]]
  (when-let [info (get @optimization-registry (str fn-name))]
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

(clojure.core/defn plan-str
  "Render `(plan fn-name samples)` as a human-readable string (for printing)."
  [fn-name & [samples]]
  (if-let [p (apply plan fn-name (when samples [samples]))]
    (let [arrow (fn [stages] (if (seq stages) (clojure.string/join " → " stages) "(none)"))]
      (str "plan " (:fn p) "\n"
           "  naive:  " (arrow (:stages-before p)) "   (" (:passes-before p) " passes)\n"
           "  fused:  " (arrow (:stages-after p))  "   (" (:passes-after p) " passes)\n"
           "  laws:   " (if (seq (:laws p)) (clojure.string/join ", " (:laws p)) "confluent fusion") "\n"
           "  proof:  " (if (:verified? p) "optimized ≡ naive (kernel-certified)" "unverified") "\n"
           (when (:n-in p)
             (str "  sample: " (:n-in p) " in → " (:n-out p) " out"
                  (when (:selectivity p) (str "  (selectivity " (format "%.2f" (:selectivity p)) ")"))
                  "  in " (format "%.3f" (:runtime-ms p)) " ms\n"))))
    (str "plan " fn-name ": no optimization record (defined under *optimize* false?)")))

;; ===== moved from core.clj lines 224,235 =====
(clojure.core/defn- compute-arity
  "Compute the runtime arity of a function type.
   Returns {:arity n :erased k} where n = explicit params, k = erased (implicit/inst) prefix."
  [fn-type]
  (loop [t fn-type explicit 0 erased 0 in-prefix true]
    (if (e/forall? t)
      (let [bi (e/forall-info t)]
        (if (= :default bi)
          (recur (e/forall-body t) (inc explicit) erased false)
          (recur (e/forall-body t) explicit (if in-prefix (inc erased) erased) in-prefix)))
      {:arity explicit :erased erased})))


;; ===== moved from core.clj lines 1583,1605 =====
(clojure.core/defn- nary-op
  "Emit `(op a b)` when a binary primitive is fully applied (≥2 compiled args),
   else a `partial` — so an eta-reduced / partially-applied op (simp turns
   `(fun y => Nat.ble k y)` into the partial `(Nat.ble k)`) still lowers to a
   runnable fn rather than blowing an arity assumption."
  [op ca]
  (cond
    (>= (count ca) 2) (list op (nth ca 0) (nth ca 1))
    (= (count ca) 1)  (list 'clojure.core/partial op (nth ca 0))
    :else op))

(clojure.core/defn- prim-tag
  "JVM primitive type hint INDUCED from a binder's kernel type, or nil. `Nat`/`Int`/
   `UInt*` → `long`, `Float`/`Real` → `double`. Hinting a (curried, 1-arg) element fn lets
   Clojure emit a primitive `invokePrim` arity, so the fn BODY does primitive arithmetic
   (no per-op boxing) — the unboxed half of the perf story, alongside Int64 literals."
  [ty]
  (when (e/const? ty)
    (case (name/->string (e/const-name ty))
      ("Nat" "Int" "UInt8" "UInt16" "UInt32" "UInt64") 'long
      ("Float" "Real") 'double
      nil)))


;; ===== moved from core.clj lines 1790,2562 =====
(def ^:dynamic *parallel-fold*
  "When true (default), a foldl recognized as a proven associative monoid (Item B)
   lowers to the parallel fork-join `apfoldl` (vector path); set false to force the
   sequential `afoldl`. The long[] unboxed path is unaffected either way."
  true)

(def ^:private monoid-fold-ops
  "Kernel op const-name → {:clj <2-arg Clojure op>, :id <identity literal>,
   :laws [associativity + identity theorem names]}. Parallel emission is GATED on
   the laws being present in the env: fork-join re-associates the fold, which is
   sound iff the op is an associative monoid with `init` its identity — these Init
   lemmas certify exactly that, so the proof is the licence to parallelize."
  {"Nat.add" {:clj '+ :id 0 :laws ["Nat.add_assoc" "Nat.zero_add" "Nat.add_zero"]}
   "Nat.mul" {:clj '* :id 1 :laws ["Nat.mul_assoc" "Nat.one_mul" "Nat.mul_one"]}
   "Int.add" {:clj '+ :id 0 :laws ["Int.add_assoc" "Int.zero_add" "Int.add_zero"]}
   "Int.mul" {:clj '* :id 1 :laws ["Int.mul_assoc" "Int.one_mul" "Int.mul_one"]}})

(clojure.core/defn- monoid-fold-op
  "If foldl step `f-expr` is `acc ⊕ h(x)` (a fused λacc.λx. ⊕ acc rhs with acc NOT
   free in rhs) or a bare `⊕` const, for a registered associative-monoid op ⊕, AND
   `init-clj` is ⊕'s identity, AND ⊕'s kernel laws are present in `env`, return the
   Clojure combine op symbol for apfoldl; else nil (→ sequential afoldl)."
  [env f-expr init-clj]
  (let [opn (cond
              ;; bare op const: (reduce + 0 xs) → step is the const Nat.add itself
              (e/const? f-expr) (name/->string (e/const-name f-expr))
              ;; fused step λ acc. λ x. (⊕ acc rhs); acc = bvar 1, must not occur in rhs
              (and (e/lam? f-expr) (e/lam? (e/lam-body f-expr)))
              (let [body (e/lam-body (e/lam-body f-expr))
                    [h hargs] (e/get-app-fn-args body)]
                (when (and (e/const? h) (>= (count hargs) 2))
                  (let [a   (nth hargs (- (count hargs) 2))
                        rhs (nth hargs (- (count hargs) 1))]
                    (when (and (e/bvar? a) (= 1 (e/bvar-idx a))   ; left operand IS acc
                               (<= (e/bvar-range rhs) 1))          ; acc (bvar 1) unused in rhs
                      (name/->string (e/const-name h)))))))
        spec (get monoid-fold-ops opn)]
    (when (and spec
               (= init-clj (:id spec))
               (every? #(some? (env/lookup env (name/from-string %))) (:laws spec)))
      (:clj spec))))

(declare ansatz->clj)
(declare inductive-rep)

(clojure.core/defn- emit-hinted-fn
  "Codegen a kernel lambda `f-expr` as a Clojure fn with up to `arity` params, each
   ^long/^double-hinted from its binder's kernel type, AND a primitive RETURN hint
   `rtag` on the param vector — so Clojure generates the primitive IFn$LL/IFn$LLL/IFn$DD
   arity and the element/step call is invoked via invokePrim with ZERO boxing (without the
   return hint a `^long`-param fn is still Object-returning, so every call boxes). A bare
   op / eta-reduced step (not a lambda) is emitted as-is."
  [env f-expr arity rtag names]
  (if (e/lam? f-expr)
    (loop [e f-expr, ps [], ns names]
      (if (and (< (count ps) arity) (e/lam? e))
        ;; name by ABSOLUTE binder depth (count of names in scope), NOT the local param index —
        ;; otherwise nested step-fns both restart at p0/p1 and an outer reference (a deeper de
        ;; Bruijn index, correctly resolved by position) is emitted with a name the INNER binder
        ;; shadows ⇒ Clojure lexical capture (e.g. a nested-loop bucket filter comparing the order
        ;; key to ITSELF instead of the outer row key). Depth-unique names match the `v<n>` scheme.
        (let [n (str "p" (count ns))
              tag (prim-tag (e/lam-type e))
              sym (if tag (with-meta (symbol n) {:tag tag}) (symbol n))]
          (recur (e/lam-body e) (conj ps sym) (conj ns n)))
        (list 'fn (if rtag (with-meta ps {:tag rtag}) ps) (ansatz->clj env e ns))))
    (ansatz->clj env f-expr names)))

(clojure.core/defn- eta-saturate
  "Eta-expand an under-applied known op for codegen. `saturated` maps the FULL compiled-arg vector
   to a Clojure form. If `ca` already has ≥ `arity` args, apply it directly; otherwise emit
   (fn [g…] (saturated ca++g)) supplying the missing args — handles e.g. a join that unfolds to
   `map (Prod.mk α β x) bucket` (Prod.mk applied to 3 of 4 args, used as the map fn)."
  [ca arity saturated]
  (if (>= (count ca) arity)
    (saturated ca)
    (let [gs (mapv (fn [_] (gensym "eta")) (range (- arity (count ca))))]
      (list 'clojure.core/fn gs (saturated (into ca gs))))))

(clojure.core/defn ansatz->clj
  "Compile Ansatz Expr to Clojure form for eval."
  [env expr names]
  (cond
    ;; INT64 codegen: lower Nat/Int literals to primitive `long` (not BigInteger), so the
    ;; fused runtime does native long arithmetic — the perf unlock. Trusted + gen-tested:
    ;; faithful on the in-range domain (the kernel Nat is unbounded; the generative bridge
    ;; check surfaces the long-overflow boundary). Falls back to the big value if it can't
    ;; fit in a long (correctness over speed at the extreme).
    (e/lit-nat? expr) (let [v (e/lit-nat-val expr)] (try (long v) (catch Exception _ v)))
    (e/lit-str? expr) (e/lit-str-val expr)
    (e/bvar? expr) (let [i (e/bvar-idx expr)]
                     (if (< i (count names))
                       (symbol (nth names (- (count names) i 1)))
                       (symbol (str "_" i))))
    (e/lam? expr) ;; depth-unique binder name (bvars resolve positionally, so the
                  ;; actual name only needs to be unique + a valid symbol — Lean /
                  ;; simp-instantiated binders may be Name objects or hygienic names
                  ;; that aren't, and duplicates would shadow incorrectly).
                  (let [n (str "v" (count names))
                        tag (prim-tag (e/lam-type expr))
                        param (if tag (with-meta (symbol n) {:tag tag}) (symbol n))]
                    (list 'fn [param]
                          (ansatz->clj env (e/lam-body expr) (conj names n))))
    (e/app? expr)
    (let [[head args] (e/get-app-fn-args expr)]
      ;; Subtype is a refinement erased at runtime — handle BEFORE compiling args
      ;; (its type/predicate args aren't runtime values): the value passes through.
      (cond
        (and (e/const? head) (= "Subtype.val" (name/->string (e/const-name head))) (= 3 (count args)))
        (ansatz->clj env (nth args 2) names)
        (and (e/const? head) (= "Subtype.mk" (name/->string (e/const-name head))) (>= (count args) 3))
        (ansatz->clj env (nth args 2) names)
        :else
      (if (e/const? head)
        (let [h (name/->string (e/const-name head))
              ca (mapv #(ansatz->clj env % names) args)]
          (case h
            ;; dite α cond dec then-fn else-fn → (if bool-cond then else)
            ;; then-fn = λ h => body, else-fn = λ h => body (h is proof, erased at runtime)
            "dite"
            (let [;; args: [α, cond, dec-inst, then-fn, else-fn]
                  then-fn (nth args 3)   ;; Ansatz lambda: λ h => then-body
                  else-fn (nth args 4)   ;; Ansatz lambda: λ h => else-body
                  ;; Peel lambda, compile body (the h arg is a proof — not used at runtime)
                  then-body (if (e/lam? then-fn)
                              (ansatz->clj env (e/lam-body then-fn) (conj names "_h"))
                              (nth ca 3))
                  else-body (if (e/lam? else-fn)
                              (ansatz->clj env (e/lam-body else-fn) (conj names "_h"))
                              (nth ca 4))
                  ;; Build runtime condition from the Decidable instance.
                  ;; Decidable.decide returns Bool; or for Nat.decEq a b, use ==
                  dec-expr (nth args 2) ;; Ansatz expr for Decidable instance
                  [dec-head dec-args] (e/get-app-fn-args dec-expr)
                  bool-cond (if (and (e/const? dec-head)
                                     (= "Nat.decEq" (name/->string (e/const-name dec-head))))
                              ;; Nat.decEq a b → (== a b) at runtime
                              (list '== (ansatz->clj env (nth dec-args 0) names)
                                    (ansatz->clj env (nth dec-args 1) names))
                              ;; Generic: compile the decidable instance (may not work for all cases)
                              (nth ca 2))]
              (list 'if bool-cond then-body else-body))
            ;; WellFounded.Nat.fix α motive measure F x → letfn recursive call
            ;; F = λ x (λ IH body) — compile body with IH→self-call, dropping proof args
            "WellFounded.Nat.fix"
            (if (= 5 (count ca))
              ;; Full application: WF.Nat.fix α motive measure F x
              (let [f-expr (nth args 3) ;; F as Ansatz Expr
                    x-arg (nth ca 4)    ;; compiled x
                    self-sym (gensym "wf_")
                    ;; F = λ x. λ IH. body
                    ;; Peel two lambdas
                    f-body-1 (when (e/lam? f-expr) (e/lam-body f-expr))
                    f-body-2 (when (and f-body-1 (e/lam? f-body-1)) (e/lam-body f-body-1))
                    x-name (when (e/lam? f-expr) (or (e/lam-name f-expr) "x"))
                    ih-name (when (and f-body-1 (e/lam? f-body-1))
                              (or (e/lam-name f-body-1) "IH"))
                    compiled-body (when f-body-2
                                    (ansatz->clj env f-body-2
                                                 (conj names x-name ih-name)))
                    ;; Replace IH calls: (IH arg proof) → (self arg)
                    ;; In compiled form, IH is a symbol. Calls look like ((IH arg) proof).
                    ;; We need to replace (IH-sym arg proof) patterns with (self arg).
                    ih-sym (symbol ih-name)
                    replace-ih (fn replace-ih [form]
                                 (cond
                                   ;; ((IH y) proof) → (self y)
                                   (and (seq? form) (= 2 (count form))
                                        (seq? (first form)) (= 2 (count (first form)))
                                        (= ih-sym (ffirst form)))
                                   (list self-sym (second (first form)))
                                   (seq? form) (apply list (map replace-ih form))
                                   (vector? form) (mapv replace-ih form)
                                   :else form))
                    final-body (replace-ih compiled-body)]
                (list 'letfn [(list self-sym [(symbol x-name)] final-body)]
                      (list self-sym x-arg)))
              ;; Partial application (shouldn't happen normally)
              (list 'apply (ansatz->clj env head names) ca))
            "HAdd.hAdd" (list '+ (nth ca 4) (nth ca 5))
            "HMul.hMul" (list '* (nth ca 4) (nth ca 5))
            ;; HSub: Nat truncates at 0 (Nat.sub semantics); Int/Float are SIGNED.
            ;; Decide from the element type arg (args[0]).
            "HSub.hSub" (let [tn (let [[th _] (e/get-app-fn-args (nth args 0))]
                                   (when (e/const? th) (name/->string (e/const-name th))))]
                          (if (= tn "Nat")
                            (list 'max 0 (list '- (nth ca 4) (nth ca 5)))
                            (list '- (nth ca 4) (nth ca 5))))
            "HDiv.hDiv" (list 'quot (nth ca 4) (nth ca 5))
            "HPow.hPow" (list 'long (list 'Math/pow (nth ca 4) (nth ca 5)))
            "Nat.add" (nary-op '+ ca)
            "Nat.mul" (nary-op '* ca)
            "Nat.div" (list 'quot (nth ca 0) (nth ca 1))
            ;; Int arithmetic → Clojure long ops (signed). Int.ofNat is a no-op at
            ;; runtime (both are JVM long). The Int64 trust decision applies.
            "Int.add" (nary-op '+ ca)
            "Int.mul" (nary-op '* ca)
            "Int.sub" (nary-op '- ca)
            "Int.div" (list 'quot (nth ca 0) (nth ca 1))
            "Int.ofNat" (nth ca 0)
            "Int.neg" (list '- (nth ca 0))
            "Float.ofNat" (list 'double (nth ca 0))
            "Nat.pow" (list 'long (list 'Math/pow (nth ca 0) (nth ca 1)))
            "Nat.succ" (list 'inc (nth ca 0))
            "Bool.true" true
            "Bool.false" false
            "Bool.not" (list 'not (nth ca 0))
            ;; Function.comp α β γ f g [x] → (comp f g) or (f (g x)). Produced by
            ;; map∘map fusion (List.map_map rewrites to map (f ∘ g)).
            "Function.comp" (if (>= (count ca) 6)
                              (list (nth ca 3) (list (nth ca 4) (nth ca 5)))
                              (list 'clojure.core/comp (nth ca 3) (nth ca 4)))
            "Nat.zero" 0
            ;; Float literal: OfScientific.ofScientific Float inst m s e → m × 10^±e.
            ;; (args: α inst mantissa exponentSign decimalExponent) — type/inst erase.
            "OfScientific.ofScientific"
            (let [m (nth ca 2) s (nth ca 3) ex (nth ca 4)]
              (if (and (number? m) (number? ex) (boolean? s))
                (* (double m) (Math/pow 10.0 (double (if s (- ex) ex))))   ; computed literal
                (list '* (list 'double m) (list 'Math/pow 10.0 (list 'if s (list '- ex) ex)))))
            ;; Float arithmetic → Clojure double ops (type/instance args erase).
            "Float.add" (list '+ (nth ca 0) (nth ca 1))
            "Float.mul" (list '* (nth ca 0) (nth ca 1))
            "Float.sub" (list '- (nth ca 0) (nth ca 1))
            "Float.div" (list '/ (nth ca 0) (nth ca 1))
            ;; String ops → Clojure string ops. String.append a b → concat; the
            ;; (String, ++, "") monoid: String.append IS the concat. length → count.
            "String.append" (list 'clojure.core/str (nth ca 0) (nth ca 1))
            "String.length" (list 'clojure.core/count (nth ca 0))
            "String.toUpper" (list 'clojure.string/upper-case (nth ca 0))
            "String.toLower" (list 'clojure.string/lower-case (nth ca 0))
            "String.isPrefixOf" (list 'clojure.string/starts-with? (nth ca 1) (nth ca 0))
            ;; List.elem K beq x ys → x ∈ ys (beq erases to structural =). args: K beq x ys.
            "List.elem" (list 'clojure.core/boolean
                              (list 'clojure.core/some
                                    (list 'fn ['__e] (list 'clojure.core/= '__e (nth ca 2)))
                                    (nth ca 3)))
            ;; List.all/any α l p → every?/some over the list (boolean). args: α l p.
            "List.all" (list 'clojure.core/boolean (list 'clojure.core/every? (nth ca 2) (nth ca 1)))
            "List.any" (list 'clojure.core/boolean (list 'clojure.core/some (nth ca 2) (nth ca 1)))
            "String.toList" (list 'clojure.core/vec (nth ca 0))     ; String → seq of chars
            "Char.toNat" (list 'clojure.core/int (nth ca 0))        ; char → code point (Nat)
            "Float.beq" (list 'clojure.core/== (nth ca 0) (nth ca 1))
            ;; Decidable.decide P inst → the Bool. P is the decided proposition (an
            ;; ordering/equality over Int/Float); read the comparison off P's head.
            ;; (args: P inst — both erase; we recompute the boolean from P's operands.)
            "Decidable.decide"
            (let [prop (nth args 0)
                  [ph pa] (e/get-app-fn-args prop)
                  pn (when (e/const? ph) (name/->string (e/const-name ph)))]
              (case pn
                ("Int.lt" "Float.lt" "Nat.lt") (list '< (ansatz->clj env (nth pa 0) names) (ansatz->clj env (nth pa 1) names))
                ("Int.le" "Float.le" "Nat.le") (list '<= (ansatz->clj env (nth pa 0) names) (ansatz->clj env (nth pa 1) names))
                "Eq" (list 'clojure.core/= (ansatz->clj env (nth pa 1) names) (ansatz->clj env (nth pa 2) names))
                (nth ca 1)))
            "ite" (list 'if (nth ca 1) (nth ca 3) (nth ca 4))
            ;; Eq as a runtime condition (e.g. the `p x = true` guard in a fused
            ;; foldl_filter step): Bool equalities collapse to the bool itself.
            "Eq" (let [rhs-head (first (e/get-app-fn-args (nth args 2)))
                       rhs-name (when (e/const? rhs-head) (name/->string (e/const-name rhs-head)))]
                   (case rhs-name
                     "Bool.true" (nth ca 1)
                     "Bool.false" (list 'not (nth ca 1))
                     (list 'clojure.core/= (nth ca 1) (nth ca 2))))
            ;; Nat comparison → Clojure primitives (arity-tolerant for eta-reduced partials)
            "Nat.blt" (nary-op '< ca)
            "Nat.ble" (nary-op '<= ca)
            "Nat.beq" (nary-op '== ca)
            ;; BEq equality: BEq.beq α inst a b → (= a b) (type/instance erased).
            "BEq.beq" (list 'clojure.core/= (nth ca 2) (nth ca 3))
            ;; Prod projections: Prod.mk compiles to a [fst snd] vector, so fst/snd
            ;; are positional. (args: α β p)
            ;; Prod is a plain pair at runtime: Prod.mk α β a b → [a b] (NOT the tagged-ctor [0 a b]),
            ;; matching Prod.fst/snd's nth 0/1. args: α β a b.
            "Prod.mk"  (eta-saturate ca 4 (fn [f] (list 'clojure.core/vector (nth f 2) (nth f 3))))
            "Prod.fst" (eta-saturate ca 3 (fn [f] (list 'clojure.core/nth (nth f 2) 0)))
            "Prod.snd" (eta-saturate ca 3 (fn [f] (list 'clojure.core/nth (nth f 2) 1)))
            ;; List operations → Clojure persistent list
            "List.cons" (list 'clojure.core/cons (nth ca 1) (nth ca 2))
            "List.nil" nil
            "List.length" (list 'count (nth ca 1))
            ;; List SOACs (args: types…, then runtime values) → native Clojure.
            ;; A foldl step is acc→elem→acc. An inline-fn step compiles to a CURRIED
            ;; lambda, but clojure.core/reduce invokes it (f acc x) — flat. So peel a
            ;; lambda step's two binders into one flat param vector. A bare const step
            ;; (e.g. + ← Nat.add) is already a flat 2-arg fn — pass it through.
            "List.foldl"
            (let [f-expr (nth args 2)
                  ;; the step's RESULT type is the accumulator type (args[0]); a primitive
                  ;; return hint makes the step an IFn$LLL/DDD → afoldl/apfoldl invoke it
                  ;; via invokePrim (zero boxing), not the boxed fallback.
                  step (emit-hinted-fn env f-expr 2 (prim-tag (nth args 0)) names)
                  ;; Item B: if this is a proven associative-monoid fold, lower to
                  ;; the parallel fork-join apfoldl (vector path); else sequential afoldl.
                  mop (when *parallel-fold* (monoid-fold-op env f-expr (nth ca 3)))]
              (if mop
                (list 'ansatz.core/apfoldl mop step (nth ca 3) (nth ca 4))
                (list 'ansatz.core/afoldl step (nth ca 3) (nth ca 4))))
            ;; map fn α→β: hint param α + RETURN β so it's IFn$LL/DD (amapl invokePrim).
            ;; prefix/suffix + head/tail → Clojure runtime ops. take/take-while/drop are
            ;; LAZY (a bounded terminal makes an infinite lazy pipeline consumable).
            ;; (args: α [n|pred] coll — type erases.) head?/getLast? are Option → value-or-nil.
            "List.take" (list 'clojure.core/take (nth ca 1) (nth ca 2))
            "List.drop" (list 'clojure.core/drop (nth ca 1) (nth ca 2))
            "List.chunk" (list 'clojure.core/partition-all (nth ca 1) (nth ca 2))  ; grace-hash spill blocks (α B l)
            ;; windowed stream observation: pull ≤ n from a coalgebra (seed,step) — runs over an
            ;; infinite/lazy source, forcing only the window. (args: A S step n s — types erase.)
            "Stream.unfoldTake" (list 'ansatz.core/unfold-take (nth ca 2) (nth ca 3) (nth ca 4))
            ;; Strm A = Nat → A (the infinite-stream surface). A stream is a Clojure fn Nat→A;
            ;; range = identity, smap = post-compose, take = materialize the window [0..n-1].
            "Strm.range" 'clojure.core/identity                                     ; λn. n
            "Strm.smap" (list 'clojure.core/comp (nth ca 2) (nth ca 3))             ; A B g s → g∘s
            "Strm.take" (list 'clojure.core/mapv (nth ca 2) (list 'clojure.core/range (nth ca 1)))  ; A n s → (mapv s (range n))
            ;; Strm.scan op init s : Strm B — the running aggregate. Certified ≡ the incremental
            ;; recurrence (Strm.scan_step), which licenses the O(n) lazy `reductions` impl: the m-th
            ;; running aggregate is `(nth (reductions op init (map s (range))) m)`.
            "Strm.scan" (let [nn (gensym "n")]                                       ; A B op init s
                          (list 'clojure.core/fn [nn]
                                (list 'clojure.core/nth
                                      (list 'clojure.core/reductions (nth ca 2) (nth ca 3)
                                            (list 'clojure.core/map (nth ca 4) (list 'clojure.core/range)))
                                      (list 'clojure.core/inc nn))))
            ;; LSeq A = Nat → Option A (possibly-finite). Runtime = a real lazy seq; smap = lazy map,
            ;; take = lazy take → vector (stops at seq end OR n, whichever first). A passed-in lazy seq
            ;; IS the value (no wrapping). Works on infinite lazy seqs, forcing only the window.
            "LSeq.smap" (list 'clojure.core/map (nth ca 2) (nth ca 3))              ; A B g s → (map g s)
            "LSeq.take" (list 'clojure.core/vec (list 'clojure.core/take (nth ca 1) (nth ca 2)))  ; A n s → (vec (take n s))
            "List.getD" (list 'clojure.core/nth (nth ca 1) (nth ca 2) (nth ca 3))   ; nth coll i default
            "List.range" (list 'clojure.core/range (nth ca 0))                       ; (range n)
            "List.takeWhile" (list 'clojure.core/take-while (nth ca 1) (nth ca 2))
            "List.dropWhile" (list 'clojure.core/drop-while (nth ca 1) (nth ca 2))
            "List.head?" (list 'clojure.core/first (nth ca 1))
            "List.getLast?" (list 'clojure.core/last (nth ca 1))
            "List.tail" (list 'clojure.core/rest (nth ca 1))
            "List.reverse" (list 'clojure.core/reverse (nth ca 1))
            "List.append" (list 'clojure.core/concat (nth ca 1) (nth ca 2))      ; args: α a b
            "List.intersperse" (list 'clojure.core/interpose (nth ca 1) (nth ca 2)) ; args: α sep coll
            ;; flatMap/filterMap (mapcat/keep) — args: α β f coll. filterMap's f returns
            ;; Option β (value-or-nil at runtime), exactly what clojure.core/keep wants.
            "List.flatMap" (list 'clojure.core/mapcat (nth ca 2) (nth ca 3))
            "List.filterMap" (list 'clojure.core/keep (nth ca 2) (nth ca 3))
            ;; mapIdx (map-indexed) — args: α β f coll. emit-hinted-fn flattens the curried
            ;; step to a 2-arg (fn [i x] …) (handles bare ops too); map-indexed calls (f i x).
            "List.mapIdx" (list 'clojure.core/map-indexed
                                (emit-hinted-fn env (nth args 2) 2 nil names)
                                (nth ca 3))
            ;; scanl (reductions) — args: acc elem f init coll. Same 2-arg-step flattening.
            "List.scanl" (list 'clojure.core/reductions
                               (emit-hinted-fn env (nth args 2) 2 nil names)
                               (nth ca 3) (nth ca 4))
            ;; eraseReps (dedupe) — args: α beq coll → drop consecutive dups.
            "List.eraseReps" (list 'clojure.core/dedupe (nth ca 2))
            ;; EXTRINSIC alist map: kernel denotation = List(K×V), runtime = hash-map.
            ;; empty→{}, get→(get m k d), put→(assoc m k v). args carry [K V deceq …].
            "AList.empty" {}
            "AList.get" (list 'clojure.core/get (nth ca 5) (nth ca 3) (nth ca 4))   ; k d l → (get l k d)
            "AList.put" (list 'clojure.core/assoc (nth ca 5) (nth ca 3) (nth ca 4)) ; k v l → (assoc l k v)
            ;; Option eliminators — runtime rep of Option is value-or-nil. (Caveat: a `some
            ;; nil` collapses to none — fine for non-nilable element types.)
            "Option.some" (nth ca 1)                                  ; α x → x
            "Option.none" nil                                         ; α → nil
            "Option.isSome" (list 'clojure.core/some? (nth ca 1))     ; α opt
            "Option.isNone" (list 'clojure.core/nil? (nth ca 1))      ; α opt
            "Option.getD" (let [o (gensym "o")]                       ; α opt default
                            (list 'clojure.core/let [o (nth ca 1)]
                                  (list 'if (list 'clojure.core/nil? o) (nth ca 2) o)))
            "Option.elim" (let [o (gensym "o")]                       ; α β opt none somefn
                            (list 'clojure.core/let [o (nth ca 2)]
                                  (list 'if (list 'clojure.core/nil? o) (nth ca 3) (list (nth ca 4) o))))
            "Option.map" (let [o (gensym "o")]                        ; α β f opt
                           (list 'clojure.core/let [o (nth ca 3)]
                                 (list 'if (list 'clojure.core/nil? o) nil (list (nth ca 2) o))))
            "Option.bind" (let [o (gensym "o")]                       ; α β opt f
                            (list 'clojure.core/let [o (nth ca 2)]
                                  (list 'if (list 'clojure.core/nil? o) nil (list (nth ca 3) o))))
            "List.map" (list 'ansatz.core/amapl
                             (emit-hinted-fn env (nth args 2) 1 (prim-tag (nth args 1)) names)
                             (nth ca 3))
            ;; filter pred α→Bool: hint param α (return Bool stays Object → IFn$LO for afilter).
            "List.filter" (list 'ansatz.core/afilter
                                (emit-hinted-fn env (nth args 1) 1 nil names)
                                (nth ca 2))
            ;; assoc lookup: List.lookup α β (BEq α) k l → value-or-nil. The
            ;; runtime list is a seq of [k v] pairs (Prod.mk erases to a vector),
            ;; so (into {} l) is the map; Option β is modeled as value-or-nil
            ;; (some v ↔ v, none ↔ nil — idiomatic Clojure get). (args: α β beq k l)
            "List.lookup" (list 'get (list 'into {} (nth ca 4)) (nth ca 3))
            ;; Verified Map ops lower to a REAL Clojure hash-map (O(1) probe / O(n) build), NOT the
            ;; assoc-list — the kernel rep is `{List(K×V) // NodupKeys}` but the runtime is a hash-map, which
            ;; is observationally equal for the Map operations (lookup/insert/group_by/entries) and what makes
            ;; joins scale. Map.insert: [K V inst k v m]; Map.lookup: [K V inst k m].
            "Map.insert" (list 'assoc (nth ca 5) (nth ca 3) (nth ca 4))   ; (assoc m k v) — overwrites, NodupKeys
            "Map.lookup" (list 'get (nth ca 4) (nth ca 3))                ; (get m k) — O(1), value-or-nil ≈ Option
            "Map.empty" {}
            ;; group-by over a hash-map: O(n) build, buckets = items per key. (args: K V deceq f xs)
            "Map.group_by" (list 'clojure.core/group-by (nth ca 3) (nth ca 4))
            ;; ->map boundary: the Map is already a Clojure hash-map. (args: K V m)
            "Map.entries" (nth ca 2)
            ;; join: group ys by lf, pair each x with matches by kf. (args: K X Y D kf lf xs ys)
            ;; The pair multiset matches the kernel; order is join-irrelevant.
            "Map.join"
            (let [grp (gensym "g") xx (gensym "x") yy (gensym "y")
                  kf (nth ca 4) lf (nth ca 5) xs (nth ca 6) ys (nth ca 7)]
              (list 'let [grp (list 'clojure.core/group-by lf ys)]
                    (list 'vec (list 'clojure.core/mapcat
                                     (list 'fn [xx]
                                           (list 'clojure.core/mapv (list 'fn [yy] [xx yy])
                                                 (list 'get grp (list kf xx) [])))
                                     xs))))
            ;; distinct: List.eraseDups α (BEq α) xs → (distinct xs). The BEq
            ;; instance is erased — Clojure's distinct uses structural =, which
            ;; agrees with BEq on the value types we admit.
            "List.eraseDups" (list 'clojure.core/vec (list 'clojure.core/distinct (nth ca 2)))
            ;; sort: List.mergeSort α xs cmp → (sort cmp3 xs) where cmp3 is a
            ;; faithful 3-way comparator built from the kernel Bool comparator
            ;; (a≤b). Flatten a lambda comparator's two binders into a flat 2-arg
            ;; fn (mergeSort calls it (cmp a b)); a bare const (Nat.ble→<=) is
            ;; already flat.
            "List.mergeSort"
            (let [c-expr (nth args 2)
                  cmp (if (e/lam? c-expr)
                        (loop [e c-expr, ps [], ns names]
                          (if (and (< (count ps) 2) (e/lam? e))
                            (let [n (or (e/lam-name e) (str "p" (count ps)))]
                              (recur (e/lam-body e) (conj ps (symbol n)) (conj ns n)))
                            (list 'fn ps (ansatz->clj env e ns))))
                        (nth ca 2))
                  a (gensym "a") b (gensym "b")]
              (list 'clojure.core/sort
                    (list 'fn [a b]
                          (list 'if (list cmp a b)
                                (list 'if (list cmp b a) 0 -1) 1))
                    (nth ca 1)))
            ;; Constructor application
            ;; For structures (defrecord): use ->RecordName constructor
            ;; For other inductives: tagged vector [field1 field2 ...]
            (if-let [ctor-ci (when-let [ci (env/lookup env (e/const-name head))]
                               (when (.isCtor ^ConstantInfo ci) ci))]
              (let [np (.numParams ctor-ci)
                    nf (.numFields ctor-ci)
                    fields (subvec ca np (+ np nf))
                    ;; Check if this is a structure with a defrecord
                    ind-name (subs h 0 (max 0 (- (count h) (count (name/->string (.name ctor-ci)))
                                                 -1 (count h))))
                    ;; Get the inductive name from the ctor name: T.mk → T
                    ctor-str (name/->string (.name ctor-ci))
                    dot-idx (.lastIndexOf ^String ctor-str ".")
                    struct-name (when (pos? dot-idx) (subs ctor-str 0 dot-idx))
                    struct-info (when struct-name (get @structure-registry struct-name))]
                (cond
                  ;; Structure with defrecord: use ->RecordName constructor
                  (and struct-info (= nf (count (:fields struct-info))))
                  (apply list (:ctor-sym struct-info) fields)
                  ;; General TAGGED inductive (≥3 ctors / 2-with-fields, e.g. Value): the
                  ;; leading ctor index makes ctors distinguishable so casesOn can dispatch.
                  ;; 0-field ctors get [cidx] (NOT a bare index) so the rep is uniform. (#59)
                  (= :tagged (inductive-rep env struct-name))
                  (vec (cons (.cidx ctor-ci) fields))
                  ;; 0-field ctor (enum / leaf-node reps): use index for enum dispatch
                  (zero? nf)
                  (let [cidx (.cidx ctor-ci)]
                    (if (zero? cidx) nil cidx))
                  ;; Default: untagged vector (leaf-node node rep)
                  :else (vec fields)))
              ;; Generic recursor compilation: *.rec → case dispatch with recursion
              (if-let [rec-ci (when (.endsWith ^String h ".rec")
                                (env/lookup env (e/const-name head)))]
                (when (.isRecursor ^ConstantInfo rec-ci)
                  (let [np (.numParams rec-ci)
                        nm (.numMotives rec-ci)
                        nmin (.numMinors rec-ci)
                        minor-start (+ np nm)
                        major-idx (+ minor-start nmin)
                        major (nth ca major-idx)
                        rules (.rules rec-ci)
                      ;; Determine which fields are recursive per constructor
                        ind-name-str (subs h 0 (- (count h) 4)) ;; remove ".rec"
                        ind-ci (env/lookup env (name/from-string ind-name-str))
                      ;; Build a letfn with self-recursive function
                        self-sym (gensym "rec_")
                        ;; Unique prefix for field names to avoid shadowing in nested matches
                        field-prefix (str "f" (gensym "") "_")
                        clauses
                        (map-indexed
                         (fn [i ^ansatz.kernel.ConstantInfo$RecursorRule rule]
                           (let [nf (.nfields rule)
                                 minor (nth ca (+ minor-start i))
                                 minor-ansatz-expr (nth args (+ minor-start i))
                                 ctor-name (.ctor rule)
                                 ctor-ci (env/lookup env ctor-name)
                                ;; Find recursive field indices
                                 rec-indices
                                 (when (.isRec ind-ci)
                                   (let [ct (.type ctor-ci)]
                                     (loop [ty ct skip (.numParams ctor-ci) j 0 acc []]
                                       (if (or (not (e/forall? ty)) (>= j nf))
                                         acc
                                         (if (pos? skip)
                                           (recur (e/forall-body ty) (dec skip) j acc)
                                           (let [ft (e/forall-type ty)
                                                 is-rec (ansatz.inductive/occurs-in?
                                                         ft (name/from-string ind-name-str))]
                                             (recur (e/forall-body ty) 0 (inc j)
                                                    (if is-rec (conj acc j) acc))))))))
                                 field-syms (mapv #(symbol (str field-prefix %)) (range nf))
                                 ih-syms (mapv #(symbol (str "ih" (gensym "") "_" %)) (or rec-indices []))]
                             {:idx i :nfields nf :minor minor :minor-ansatz minor-ansatz-expr
                              :field-syms field-syms
                              :rec-indices (or rec-indices []) :ih-syms ih-syms}))
                         rules)]
                  ;; Generate case dispatch
                    (let [t-sym (gensym "t_")
                          all-zero (every? #(zero? (:nfields %)) clauses)
                          has-rec (some #(seq (:rec-indices %)) clauses)
                          apply-minor (fn [clause args]
                                        (reduce (fn [f a] (list f a))
                                                (:minor clause) args))
                          body
                          (cond
                          ;; Enum: all ctors have 0 fields (Bool, Color, etc.)
                            (and all-zero (= 2 (count clauses)))
                          ;; Bool-like: (if value minor_1 minor_0)
                          ;; ctor 0 = falsy (nil/false), ctor 1 = truthy
                            (list 'if t-sym
                                  (:minor (second clauses))
                                  (:minor (first clauses)))

                            all-zero  ;; 3+ ctor enum
                            (list* 'case t-sym
                                   (mapcat (fn [{:keys [idx minor]}] [idx minor])
                                           clauses))

                          ;; Nat.rec: Nat is native longs, not nil/vector
                            (and (= ind-name-str "Nat")
                                 (= 2 (count clauses))
                                 (zero? (:nfields (first clauses))))
                            (let [leaf-c (first clauses)
                                  node-c (second clauses)
                                  pred-sym (first (:field-syms node-c))
                                ;; Nat.succ has 1 field: predecessor
                                  bindings [pred-sym (list 'dec t-sym)]
                                  minor-ansatz (:minor-ansatz node-c)
                                  n-ih (count (:rec-indices node-c))
                                  all-names (into (mapv str (:field-syms node-c))
                                                  (mapv str (:ih-syms node-c)))
                                  minor-body (loop [e minor-ansatz n (+ 1 n-ih)]
                                               (if (and (pos? n) (e/lam? e))
                                                 (recur (e/lam-body e) (dec n))
                                                 e))
                                  compiled-body (ansatz->clj env minor-body
                                                             (into names all-names))
                                  ih-replacements
                                  (into {} (map (fn [j ri]
                                                  [(nth (:ih-syms node-c) j)
                                                   (list self-sym (nth (:field-syms node-c) ri))])
                                                (range n-ih) (:rec-indices node-c)))
                                  major-sym (when (symbol? major) major)
                                  inline-all (fn inline-all [form]
                                               (cond
                                                 (and (symbol? form) (contains? ih-replacements form))
                                                 (get ih-replacements form)
                                                 (and major-sym (symbol? form) (= form major-sym))
                                                 t-sym
                                                 (seq? form) (apply list (map inline-all form))
                                                 (vector? form) (mapv inline-all form)
                                                 :else form))
                                  node-body (inline-all compiled-body)]
                              (list 'if (list 'zero? t-sym)
                                    (:minor leaf-c)
                                    (list 'let bindings node-body)))

                          ;; Leaf + node: first ctor 0 fields, others have fields
                            (and (= 2 (count clauses))
                                 (zero? (:nfields (first clauses))))
                            (let [leaf-c (first clauses)
                                  node-c (second clauses)
                                  nf (:nfields node-c)
                                ;; Field bindings: [color (nth t 0) left (nth t 1) ...]
                                ;; For List: use first/rest instead of nth (native seq interop)
                                ;; Also bind the discriminant name to t-sym so that
                                ;; references to the matched value inside the body
                                ;; see the current node, not the outer parameter.
                                  is-list (= ind-name-str "List")
                                  bindings (vec (mapcat (fn [i]
                                                          [(nth (:field-syms node-c) i)
                                                           (if is-list
                                                             (case (int i)
                                                               0 (list 'first t-sym)
                                                               1 (list 'rest t-sym))
                                                             (list 'nth t-sym i))])
                                                        (range nf)))
                                ;; Unwrap minor Ansatz lambdas to get the body
                                ;; Then compile body with field names + IH inlined as (rec field)
                                  minor-ansatz (:minor-ansatz node-c)
                                ;; Unwrap nf + n-ih lambdas
                                  n-ih (count (:rec-indices node-c))
                                  all-names (into (mapv str (:field-syms node-c))
                                                  (mapv str (:ih-syms node-c)))
                                  minor-body (loop [e minor-ansatz n (+ nf n-ih)]
                                               (if (and (pos? n) (e/lam? e))
                                                 (recur (e/lam-body e) (dec n))
                                                 e))
                                ;; Compile body with names for fields + IH symbols
                                  compiled-body (ansatz->clj env minor-body
                                                             (into names all-names))
                                ;; Replace IH symbols with inline recursive calls
                                ;; ih_sym → (self_fn field_sym) — lazy, only evaluated when needed
                                  ih-replacements
                                  (into {} (map (fn [j ri]
                                                  [(nth (:ih-syms node-c) j)
                                                   (list self-sym (nth (:field-syms node-c) ri))])
                                                (range n-ih) (:rec-indices node-c)))
                                  ;; Replace major-premise references with t-sym.
                                  ;; When the body references the matched value (e.g., `l`
                                  ;; in `(cons x l)` inside a match on `l`), it should
                                  ;; refer to the current node in the recursion, not the
                                  ;; outer function parameter.
                                  major-sym (when (symbol? major) major)
                                  inline-all (fn inline-all [form]
                                               (cond
                                                 (and (symbol? form) (contains? ih-replacements form))
                                                 (get ih-replacements form)
                                                 (and major-sym (symbol? form) (= form major-sym))
                                                 t-sym
                                                 (seq? form) (apply list (map inline-all form))
                                                 (vector? form) (mapv inline-all form)
                                                 :else form))
                                  node-body (inline-all compiled-body)]
                              ;; For List: use (not (seq t)) since (rest (cons x nil)) = ()
                              (list 'if (if is-list
                                          (list 'not (list 'seq t-sym))
                                          (list 'nil? t-sym))
                                    (:minor leaf-c)
                                    (list 'let bindings node-body)))

                          ;; General TAGGED inductive (e.g. EDN Value): the ctor codegen emits
                          ;; [cidx field…]. Dispatch on (nth t 0); field i lives at (nth t (inc i)).
                          ;; Per-clause body compiles exactly like leaf-node (unwrap nf+n-ih
                          ;; minor lambdas, inline IH calls + major→t). (#59)
                            (= :tagged (inductive-rep env ind-name-str))
                            (let [major-sym (when (symbol? major) major)
                                  clause-body
                                  (fn [{:keys [nfields minor-ansatz field-syms rec-indices ih-syms]}]
                                    (let [n-ih (count rec-indices)
                                          all-names (into (mapv str field-syms)
                                                          (mapv str ih-syms))
                                          mbody (loop [e minor-ansatz n (+ nfields n-ih)]
                                                  (if (and (pos? n) (e/lam? e))
                                                    (recur (e/lam-body e) (dec n)) e))
                                          compiled (ansatz->clj env mbody (into names all-names))
                                          ih-repl (into {} (map (fn [j ri]
                                                                  [(nth ih-syms j)
                                                                   (list self-sym (nth field-syms ri))])
                                                                (range n-ih) rec-indices))
                                          inline-all (fn inline-all [form]
                                                       (cond
                                                         (and (symbol? form) (contains? ih-repl form))
                                                         (get ih-repl form)
                                                         (and major-sym (symbol? form) (= form major-sym))
                                                         t-sym
                                                         (seq? form) (apply list (map inline-all form))
                                                         (vector? form) (mapv inline-all form)
                                                         :else form))
                                          body (inline-all compiled)
                                          bindings (vec (mapcat
                                                         (fn [i] [(nth field-syms i)
                                                                  (list 'nth t-sym (inc i))])
                                                         (range nfields)))]
                                      (if (seq bindings) (list 'let bindings body) body)))]
                              (list* 'case (list 'nth t-sym 0)
                                     (concat
                                      (mapcat (fn [c] [(:idx c) (clause-body c)]) clauses)
                                      ;; default: unreachable (tag always a valid cidx)
                                      [(list 'throw (list 'ex-info "bad ctor tag"
                                                          {:tag (list 'nth t-sym 0)}))])))

                            :else
                            (list 'throw (list 'ex-info "unsupported rec pattern" {})))]
                    ;; Wrap in letfn only if recursive, otherwise just inline
                      (let [rec-result
                            (if has-rec
                              (list 'letfn [(list self-sym [t-sym] body)]
                                    (list self-sym major))
                              ;; Non-recursive: just apply directly
                              (list 'let [t-sym major] body))
                            ;; Extra args beyond major? Apply them (fuel-based WF pattern).
                            extra-args (subvec ca (inc major-idx))]
                        (reduce (fn [f a] (list f a)) rec-result extra-args)))))
            ;; User-defined function: arity-aware compilation (Lean 4 FAP/PAP).
            ;; Check the arity registry to determine call style.
                (let [{:keys [arity erased]} (get @arity-registry h)]
                  (if (and arity (> arity 1) (>= (count ca) (+ arity erased)))
                    ;; FAP (full application): flat multi-arg call, skip erased prefix
                    (let [rt-args (subvec ca erased (+ erased arity))]
                      (apply list (symbol h) rt-args))
                    ;; Curried (unknown arity, single-arg, or partial application)
                    (reduce (fn [f a] (list f a)) (symbol h) ca)))))))
        (let [compiled (mapv #(ansatz->clj env % names) (cons head args))]
          (reduce (fn [f a] (list f a)) compiled)))))
    (e/const? expr) (let [cn (name/->string (e/const-name expr))]
                      (case cn
                        "Nat.zero" 0 "Bool.true" true "Bool.false" false
                        ;; Strm.range : Strm Nat = λn. n — a bare stream value is the Nat→A fn.
                        "Strm.range" 'clojure.core/identity
                        ;; Bare arithmetic constants used as FUNCTION values (e.g.
                        ;; passed to reduce/map) → the Clojure fn. (Int/Float as well as
                        ;; Nat, so `(reduce + 0 int-list)` lowers to +, not unresolved Int.add.)
                        "Nat.add" '+ "Nat.mul" '* "Nat.succ" 'inc
                        "Int.add" '+ "Int.mul" '* "Int.sub" '-
                        "Float.add" '+ "Float.mul" '* "Float.sub" '-
                        ;; Bare comparators used as function values (sort/lookup).
                        "Nat.ble" '<= "Nat.blt" '< "Nat.beq" '==
                        ;; Check if it's a constructor
                        (if-let [ci (env/lookup env (e/const-name expr))]
                          (if (.isCtor ^ConstantInfo ci)
                            (if (zero? (.numFields ci))
                              ;; 0-field ctor used as a value. For a TAGGED inductive it must be
                              ;; [cidx] (uniform with applied ctors so casesOn dispatches); for
                              ;; enum/leaf-node reps it's the bare index (ctor 0 = nil). (#59)
                              (let [cidx (.cidx ci)
                                    dot (.lastIndexOf cn ".")
                                    ind (when (pos? dot) (subs cn 0 dot))]
                                (if (= :tagged (inductive-rep env ind))
                                  [cidx]
                                  (if (zero? cidx) nil cidx)))
                              (symbol cn))
                            (symbol cn))
                          (symbol cn))))
    ;; Projection: Expr.proj type-name idx struct
    ;; For structures with defrecord: keyword access (:field-name struct)
    ;; For others: (nth struct idx)
    (e/proj? expr)
    (let [type-name-str (name/->string (e/proj-type-name expr))
          idx (e/proj-idx expr)
          struct-expr (ansatz->clj env (e/proj-struct expr) names)
          struct-info (get @structure-registry type-name-str)]
      (if (and struct-info (< idx (count (:fields struct-info))))
        (let [fname (nth (:fields struct-info) idx)
              fhint (record-field-hint (nth (:field-types struct-info) idx nil))
              rclass (:record-class struct-info)]
          (if (and fhint rclass)
            ;; PRIMITIVE field on a known defrecord class → direct `.field` access (no
            ;; boxing). The receiver is tagged with the record's FQN class so the JVM emits
            ;; a direct field read, not reflection. Records are made defrecords at the
            ;; pipeline boundary (and by ctors), so the receiver is always an instance.
            (list (symbol (str "." fname)) (with-meta struct-expr {:tag (symbol rclass)}))
            ;; Object field (String/Bool/nested) → keyword access (works on map OR record).
            (list (keyword fname) struct-expr)))
        ;; Fallback: nth on vector
        (list 'nth struct-expr idx)))
    (e/let? expr) (let [n (or (e/let-name expr) "x")]
                    ;; NOTE: we do NOT prim-hint the local — Clojure rejects `^long y` when
                    ;; the init form isn't a primitive at the Clojure level (boxed call /
                    ;; field read), which the kernel type can't guarantee.
                    (list 'let [(symbol n) (ansatz->clj env (e/let-value expr) names)]
                          (ansatz->clj env (e/let-body expr) (conj names n))))
    :else expr))

;; ============================================================
;; Tactic runner
;; ============================================================


;; ============================================================
;; Measured selectivity — the data-driven / JIT cost input
;; ============================================================
;; The optimizer's cost model (ansatz.optimize/pipeline-cost) defaults to STATIC
;; selectivity heuristics. Here we MEASURE real pass-rates on a workload — the
;; verified analogue of a JIT profiler: feed the result back to optimize-cost via
;; :selectivity for cardinality-accurate planning. A wrong measurement can only
;; change which (still kernel-certified) plan is chosen, never the result.


;; ===== moved from core.clj lines 2563,2632 =====
(clojure.core/defn- walk-subterms
  "Apply `f` to `e` and every sub-expression (best-effort structural recursion)."
  [f e]
  (when (instance? ansatz.kernel.Expr e)
    (f e)
    (cond
      (e/app? e)    (do (walk-subterms f (e/app-fn e)) (walk-subterms f (e/app-arg e)))
      (e/lam? e)    (do (walk-subterms f (e/lam-type e)) (walk-subterms f (e/lam-body e)))
      (e/forall? e) (do (walk-subterms f (e/forall-type e)) (walk-subterms f (e/forall-body e)))
      (e/proj? e)   (walk-subterms f (e/proj-struct e))
      :else nil)))

(clojure.core/defn filter-predicates
  "Every `List.filter`/`List.filterv` predicate appearing in `term` (distinct)."
  [term]
  (let [acc (volatile! [])]
    (walk-subterms
      (fn [e]
        (let [[h args] (e/get-app-fn-args e)]
          (when (and (e/const? h)
                     (#{"List.filter" "List.filterv"} (name/->string (e/const-name h)))
                     (>= (count args) 2))
            (vswap! acc conj (nth args 1)))))
      term)
    (distinct @acc)))

(clojure.core/defn measure-selectivity
  "MEASURE a filter predicate's pass-rate on a real workload — datahike's
   sample-predicate-selectivity, for our terms. `pred` is a kernel `α → Bool`
   lambda; `sample` is a seq of representative α-VALUES (compiled Clojure values).
   Compiles `pred`, runs it over the sample, returns the observed rate ∈ [0.01, 1]."
  [env pred sample]
  (let [f (eval (ansatz->clj env pred []))
        n (count sample)]
    (if (zero? n) 0.5
      (-> (count (clojure.core/filter f sample)) (/ (double n)) (max 0.01) (double) (min 1.0)))))

(clojure.core/defn profile-selectivity
  "Build a `:selectivity` profile {pred-string → rate} for `optimize-cost` by
   measuring every `List.filter` predicate in `term` against `sample` (a seq of
   representative element values). Filters that share an element domain can use one
   sample; deep filters over transformed data want their own (call
   `measure-selectivity` per predicate and assemble the map yourself)."
  [env term sample]
  (into {} (clojure.core/map (fn [p] [(e/->string p) (measure-selectivity env p sample)])
                             (filter-predicates term))))

(clojure.core/defn optimize-measured
  "The CLOSED measure→replan loop (the verified JIT). MEASURE the pipeline's filter
   selectivities on `sample` data, then re-optimize `term` with those REAL cardinalities
   (datahike-style adaptive planning) — every adopted rewrite still kernel-re-certified, so
   adapting the plan to the observed workload can't make it unsound. Returns the
   `optimize-cost` result plus `:profile` (the measured `{pred→rate}` used). This is what
   turns the static `:selectivity` hook into an actual measure-and-optimize cycle: run it
   again as the workload drifts and the plan re-adapts, re-proven each time.

   `:compare?` also returns `:static` (the plan WITHOUT the measured profile) so a caller
   can see whether measurement changed the chosen plan."
  [env term sample & {:keys [lctx compare?]}]
  (let [oc (requiring-resolve 'ansatz.optimize/optimize-cost)
        profile (profile-selectivity env term sample)
        res (assoc (oc env term :lctx lctx :selectivity profile) :profile profile)]
    (if compare?
      (assoc res :static (oc env term :lctx lctx))
      res)))

;; ============================================================
;; Extensible registries (Lean 4's @[tactic], @[simproc], elab_rules)
;; ============================================================


;; ===== moved from core.clj lines 2897,3134 =====
(clojure.core/defn- replace-rec-calls
  "Walk expr, replacing calls to fn-name with IH applications.
   For fuel-based recursion: fn-name(arg) → ih(arg), no proof args.

   ih-depth: de Bruijn depth of the IH bvar relative to the current position.
   fn-name: Name of the function being defined.
   fn-arity: number of user-visible args the function takes.
   discr-expr: unused in fuel-based approach (kept for API compatibility)."
  [expr fn-name fn-arity ih-depth discr-expr]
  (let [walk
        (fn walk [e depth-offset discr]
          (cond
            ;; Application: check for recursive call or recursor
            (e/app? e)
            (let [[head args] (e/get-app-fn-args e)]
              (cond
                ;; Found a recursive call: replace with IH(arg, proof)
                (and (e/const? head)
                     (= (name/->string (e/const-name head))
                        (name/->string fn-name))
                     (= fn-arity (count args)))
                ;; Fuel-based: replace fn-name(args...) with ih(args...), no proof needed
                (let [walked-args (mapv #(walk % depth-offset discr) args)
                      ih-ref (e/bvar (+ ih-depth depth-offset))]
                  (reduce e/app ih-ref walked-args))

                ;; Detect Nat.rec application and specialize IH per branch
                ;; Generic application: walk children
                :else
                (reduce e/app (walk head depth-offset discr)
                        (mapv #(walk % depth-offset discr) args))))
            ;; Lambda: descend, incrementing depth
            (e/lam? e)
            (e/lam (e/lam-name e) (walk (e/lam-type e) depth-offset discr)
                   (walk (e/lam-body e) (inc depth-offset) discr)
                   (e/lam-info e))
            ;; Forall: descend
            (e/forall? e)
            (e/forall' (e/forall-name e) (walk (e/forall-type e) depth-offset discr)
                       (walk (e/forall-body e) (inc depth-offset) discr)
                       (e/forall-info e))
            ;; Let: descend
            (e/let? e)
            (e/let' (e/let-name e) (walk (e/let-type e) depth-offset discr)
                    (walk (e/let-value e) depth-offset discr)
                    (walk (e/let-body e) (inc depth-offset) discr))
            ;; Leaf nodes
            :else e))]
    (walk expr 0 discr-expr)))

(clojure.core/defn- build-invimage-type
  "Build InvImage (· < ·) measure y x as an Expr.
   y and x are Expr (typically bvars)."
  [env alpha-level alpha measure-lam y x]
  (let [nat (e/const' (name/from-string "Nat") [])
        lt-rel (e/lam "x1" nat
                      (e/lam "x2" nat
                             (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                                     nat (e/const' (name/from-string "instLTNat") [])
                                     (e/bvar 1) (e/bvar 0)) :default) :default)]
    (e/app* (e/const' (name/from-string "InvImage") [alpha-level (lvl/succ lvl/zero)])
            alpha nat lt-rel measure-lam y x)))

(clojure.core/defn- discharge-decreasing-proof
  "Build a proof of measure(rec-arg) < measure(current-arg).
   Uses omega to discharge the obligation.
   param-name, param-type: the function parameter (will be universally quantified).
   measure-form: the raw measure expression (in terms of bvar 0 = param).
   rec-arg-form: the argument to the recursive call (in terms of bvar 0 = param).
   Returns a lambda: λ (param : Type) => proof-of-lt."
  [env param-name param-type measure-ansatz rec-arg-ansatz]
  (let [nat (e/const' (name/from-string "Nat") [])
        ;; Build goal: ∀ (param : Type), measure(rec-arg) < measure(param)
        ;; measure-ansatz and rec-arg-ansatz are in terms of bvar 0 = param
        m-rec (e/app (e/lam (str param-name) param-type measure-ansatz :default) rec-arg-ansatz)
        m-cur measure-ansatz ;; measure(param) where param = bvar 0
        lt-goal (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                        nat (e/const' (name/from-string "instLTNat") [])
                        m-rec m-cur)
        ;; Wrap in forall: ∀ (param : Type), lt-goal
        full-goal (e/forall' (str param-name) param-type lt-goal :default)
        ;; Create proof state, intro param, then omega
        [ps _] (proof/start-proof env full-goal)
        ps (basic/intros ps [(str param-name)])
        ps (omega/omega ps)]
    (when-not (proof/solved? ps)
      (throw (ex-info (str "Cannot prove termination obligation."
                           "\nGoal: " (e/->string env full-goal))
                      {:goal full-goal})))
    ;; Extract gives us: λ (param) => proof-term
    (extract/extract ps)))

(clojure.core/defn- tag-kernel-fn
  "Attach the kernel constant name to a compiled runtime fn so downstream tools
   (e.g. `ansatz.reducers`) can certify it without a manual wrapper.  The runtime
   fn is compiled from the same definition as the kernel constant, so the link is
   sound by construction.  Returns the fn unchanged if it cannot carry metadata."
  [clj-fn fn-name]
  (if (instance? clojure.lang.IObj clj-fn)
    (with-meta clj-fn {:ansatz.core/kernel-name fn-name})
    clj-fn))

(clojure.core/defn- custom-sizeof-fn
  "If `type-expr` is a non-parametric custom inductive (has a recursor, not a
   primitive like Nat/Int), return its structural sizeOf as a closed `T → Nat`
   Expr, built via the recursor. Else nil."
  [env type-expr]
  (let [[head targs] (e/get-app-fn-args type-expr)]
    (when (and (e/const? head) (empty? targs))
      (let [ind-name (name/->string (e/const-name head))]
        (when-not (#{"Nat" "Int" "Bool" "String" "Char" "Fin"} ind-name)
          (let [rec-name (str ind-name ".rec")]
            (when-let [rci (env/lookup env (name/from-string rec-name))]
              (when (.isRecursor rci)
                (let [build (requiring-resolve 'ansatz.inductive.brecon/build-sizeof)]
                  (:val (build (ansatz.kernel.TypeChecker. env) env rec-name
                               (str ind-name ".sizeOf") (.numParams rci))))))))))))

(clojure.core/defn- wrap-measure-with-sizeof
  "The fuel-based recursion needs a `Nat` measure. When `:termination-by` yields a
   value of a custom inductive type, auto-wrap it with that type's structural
   `sizeOf` so the recursion bound is well-typed. `Nat` measures pass through."
  [env measure-ansatz param-types]
  (try
    (let [lam (loop [i (dec (count param-types)) b measure-ansatz]
                (if (< i 0) b (recur (dec i) (e/lam "p" (nth param-types i) b :default))))
          mtype (loop [t (.inferType (ansatz.kernel.TypeChecker. env) lam) i 0]
                  (if (and (< i (count param-types)) (e/forall? t))
                    (recur (e/forall-body t) (inc i)) t))]
      (if (and (e/const? mtype) (= "Nat" (name/->string (e/const-name mtype))))
        measure-ansatz
        (if-let [sf (custom-sizeof-fn env mtype)]
          (e/app sf measure-ansatz)
          measure-ansatz)))
    (catch Throwable _ measure-ansatz)))

(clojure.core/defn- nullary-ctor-name
  "A nullary (0-field) constructor Name of inductive `ind-name`, or nil. Used as the
   UNREACHABLE base-case default for a recursive function whose RETURN type is that custom
   inductive — the base must merely type-check against the return type (it's never hit with
   correct fuel), and a nullary ctor like `Value.vnil` does, whereas the old `0` fallback gave
   a Nat → \"Nat.rec mismatch\". (#58)"
  [env ind-name]
  (when-let [^ConstantInfo ci (env/lookup env (name/from-string ind-name))]
    (when (.isInduct ci)
      (some (fn [cn] (let [^ConstantInfo cci (env/lookup env cn)]
                       (when (and cci (zero? (.numFields cci))) cn)))
            (seq (.ctors ci))))))

(clojure.core/defn inductive-rep
  "Runtime representation tag for inductive `ind-name`. The CONSTRUCTOR codegen and the
   RECURSOR (casesOn) codegen MUST agree on this. Special-cased reps are UNtagged and preserved:
     :nat        — native longs (Nat)
     :list       — native seq, nil/cons (List)
     :enum       — every ctor 0-field → ctor index (Bool, Color, …)
     :leaf-node  — exactly 2 ctors, ctor0 nullary → nil / [field…] (binary trees, Option-ish)
   Everything else (≥3 ctors, or 2 ctors both carrying fields — e.g. EDN `Value`, `Either`) uses
   the general :tagged rep `[cidx field…]`: the leading ctor index lets casesOn dispatch. (#59)"
  [env ind-name]
  (cond
    (= ind-name "Nat")  :nat
    (= ind-name "List") :list
    :else
    (when-let [^ConstantInfo ci (env/lookup env (name/from-string ind-name))]
      (when (.isInduct ci)
        (let [nfs (mapv (fn [cn] (.numFields ^ConstantInfo (env/lookup env cn)))
                        (seq (.ctors ci)))]
          (cond
            (every? zero? nfs)                          :enum
            (and (= 2 (count nfs)) (zero? (first nfs)))  :leaf-node
            :else                                        :tagged))))))

(clojure.core/defn- ctor-rec-fields
  "For constructor `ctor-sym` of inductive `ind-name`: a map {value-field-position → field binder
   name} for the fields whose type is the inductive itself (the recursive fields). The match
   elaborator names that field's IH `ih_<binder-name>`."
  [env ind-name ctor-sym]
  (when-let [^ConstantInfo ci (env/lookup env (name/from-string (str ind-name "." ctor-sym)))]
    (loop [ty (.type ci) skip (.numParams ci) j 0 acc {}]
      (if-not (e/forall? ty)
        acc
        (if (pos? skip)
          (recur (e/forall-body ty) (dec skip) j acc)
          (recur (e/forall-body ty) 0 (inc j)
                 (if (ansatz.inductive/occurs-in? (e/forall-type ty) (name/from-string (str ind-name)))
                   (assoc acc j (e/forall-name ty))
                   acc)))))))

(clojure.core/defn- structuralize-body
  "Lean-style structural recursion. If `body` is an IMMEDIATE-structural self-recursive
   `(match scrut Ind Ret …)` on a parameter — every self-call is `(self field other-params…)` with
   `field` a recursive field bound by that clause and the other args the function's other params
   verbatim — rewrite each such self-call to the recursor IH `ih_<ctor-field>` and return the
   rewritten body. It then compiles to the inductive's recursor (DEFINITIONAL constructor equations,
   so proofs `rfl`-reduce) AND runs via the #59 recursor codegen. Returns nil if `body` isn't such a
   match or any self-call isn't immediate-structural — the caller then uses the fuel encoding.
   `params` = parse-params pairs. A no-op (returns nil) for non-self-recursive bodies."
  [env self-name params body]
  (when (and (seq? body) (= 'match (first body)) (>= (count body) 4))
    (let [scrut    (nth body 1)
          ind-form (nth body 2)
          ind-name (if (seq? ind-form) (first ind-form) ind-form)
          psyms    (mapv first params)
          sidx     (.indexOf ^java.util.List psyms scrut)
          others   (vec (keep-indexed (fn [i p] (when (not= i sidx) p)) psyms))
          saw-self (clojure.core/atom false)
          ok       (clojure.core/atom true)]
      (when (and (>= sidx 0) (symbol? ind-name))
        (letfn [(rw [pfields recs form]
                  (cond
                    (and (seq? form) (= self-name (first form)))
                    (do (reset! saw-self true)
                        (let [args    (vec (rest form))
                              rec-arg (when (< sidx (count args)) (nth args sidx))
                              fpos    (if rec-arg (.indexOf ^java.util.List pfields rec-arg) -1)
                              arg-oth (vec (keep-indexed (fn [i a] (when (not= i sidx) a)) args))]
                          (if (and (>= fpos 0) (contains? recs fpos)
                                   (= (count args) (count psyms))
                                   (= arg-oth others))
                            (symbol (str "ih_" (get recs fpos)))
                            (do (reset! ok false) form))))
                    (seq? form)    (apply list (map #(rw pfields recs %) form))
                    (vector? form) (mapv #(rw pfields recs %) form)
                    :else form))]
          (let [new-clauses
                (mapv (fn [clause]
                        (if (and (seq? clause) (>= (count clause) 3) (vector? (second clause)))
                          (let [ctor    (first clause)
                                pfields (vec (second clause))
                                recs    (or (ctor-rec-fields env ind-name ctor) {})]
                            (list ctor pfields (rw pfields recs (nth clause 2))))
                          clause))
                      (drop 4 body))]
            (when (and @saw-self @ok)
              (concat (take 4 body) new-clauses))))))))

(declare define-verified)


;; ===== moved from core.clj lines 3135,3431 =====
(clojure.core/defn define-verified-wf
  "Define a verified function with well-founded recursion.
   Uses WellFounded.Nat.fix from the environment.
   Returns compiled Clojure fn."
  [fn-name params ret-type-form body-form measure-form]
  ;; NOTE: this fuel path is kept AS-IS for `:termination-by` defns. To get the recursor
  ;; (definitional equations), OMIT `:termination-by` — `define-verified` then auto-detects
  ;; immediate-structural self-recursion and compiles to T.rec (see structuralize-body). We do not
  ;; auto-route `:termination-by` defns to the recursor: the recursor codegen has op gaps the fuel
  ;; codegen covers (e.g. Bool.and), so changing existing fuel defns would regress them (task #65).
  (let [env (env)
        pairs (parse-params params)
        n (count pairs)

        ;; Build the function type: ∀ params → ret-type (same as define-verified)
        scope-full (into {} (map-indexed (fn [i [p _]] [p i]) pairs))
        ret-ansatz (sexp->ansatz env scope-full n ret-type-form)
        type-ansatz (loop [i (dec n) body ret-ansatz]
                      (if (< i 0) body
                          (let [[pn pt binfo] (nth pairs i)
                                s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))
                                ty (sexp->ansatz env s i pt)]
                            (recur (dec i) (e/forall' (str pn) ty body binfo)))))

        ;; Compile param types
        param-types (mapv (fn [[_ pt-form]]
                            (sexp->ansatz env {} 0 pt-form))
                          pairs)
        cname (name/from-string (str fn-name))

        ;; Fork env and add temporary axiom for self-reference
        tmp-ci (env/mk-axiom cname [] type-ansatz)
        tmp-env (env/add-constant (env/fork env) tmp-ci)

        ;; Compile body on forked env — self-calls resolve to the axiom const
        body-ansatz (binding [surface-match/*use-cases-on?* true]
                      (build-telescope tmp-env {} 0 pairs body-form e/lam))

        ;; Peel all outer lambdas to get the raw body
        raw-body (loop [e body-ansatz i 0]
                   (if (and (< i n) (e/lam? e))
                     (recur (e/lam-body e) (inc i))
                     e))

        ;; Compile measure expression — uses all params in scope
        ;; Bind *scope-types* so auto-elaborate can infer implicit args from param types
        nat (e/const' (name/from-string "Nat") [])
        scope-types-map (into {} (map (fn [[p _ _] pt] [p pt]) pairs param-types))
        measure-ansatz (binding [*scope-types* scope-types-map]
                         (sexp->ansatz env scope-full n measure-form))
        ;; Fuel-based recursion needs a Nat measure; auto-wrap a custom-inductive
        ;; measure with its structural sizeOf.
        measure-ansatz (wrap-measure-with-sizeof env measure-ansatz param-types)

        ;; Universe level for return type
        tc-tmp (ansatz.kernel.TypeChecker. env)
        _ (.setFuel tc-tmp (long config/*default-fuel*))
        ret-sort (.inferType tc-tmp ret-ansatz)
        ret-level (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))

        ;; Fuel-based approach: Nat.rec on fuel (matching Lean 4's kernel-level pattern).
        ;; For n params: step = λ fuel ih p1 p2 ... pn => body[fn(a1..an) → ih(a1..an)]
        ;; raw-body has params at bvar 0..n-1 (p1=bvar 0, p2=bvar 1, etc.)
        ;; In the step body: pn=bvar 0, ..., p1=bvar n-1, ih=bvar n, fuel=bvar n+1
        ;; Since raw-body's bvar layout matches the step's param layout, no lifting needed.
        ;; ih is at depth n relative to the step body.
        replaced-body (replace-rec-calls raw-body cname n n nil)

        ;; Build multi-arg arrow type: p1 → p2 → ... → ret
        arrow-type (loop [i (dec n) ty ret-ansatz]
                     (if (< i 0) ty
                         (recur (dec i)
                                (e/forall' (str (first (nth pairs i)))
                                           (nth param-types i) ty :default))))

        ;; Build Nat.rec components
        nat-rec (e/const' (name/from-string "Nat.rec") [ret-level])
        motive-nr (e/lam "fuel" nat arrow-type :default)
        ;; base: λ p1 p2 ... pn => default (unreachable with correct fuel)
        ;; Use type-appropriate default value
        default-val (let [[rh ra] (e/get-app-fn-args ret-ansatz)]
                      (cond
                        ;; Nat → 0
                        (and (e/const? ret-ansatz)
                             (= "Nat" (name/->string (e/const-name ret-ansatz))))
                        (e/lit-nat 0)
                        ;; List α → List.nil α
                        (and (e/const? rh)
                             (= "List" (name/->string (e/const-name rh))))
                        (e/app (e/const' (name/from-string "List.nil") [lvl/zero])
                               (first ra))
                        ;; Bool → false
                        (and (e/const? ret-ansatz)
                             (= "Bool" (name/->string (e/const-name ret-ansatz))))
                        (e/const' (name/from-string "Bool.false") [])
                        ;; custom inductive (no params) with a nullary ctor, e.g. Value.vnil —
                        ;; base case is unreachable, just needs the return TYPE (#58).
                        (and (e/const? rh) (empty? ra)
                             (nullary-ctor-name env (name/->string (e/const-name rh))))
                        (e/const' (nullary-ctor-name env (name/->string (e/const-name rh))) [])
                        ;; Fallback: try Inhabited.default
                        :else
                        (let [inh-inst (try-synthesize-instance
                                        env (e/app (e/const' (name/from-string "Inhabited") [(lvl/succ lvl/zero)])
                                                   ret-ansatz))]
                          (if inh-inst
                            (e/app* (e/const' (name/from-string "Inhabited.default") [(lvl/succ lvl/zero)])
                                    ret-ansatz inh-inst)
                            ;; Last resort: use lit-nat 0 (may cause type error if reached)
                            (e/lit-nat 0)))))
        base-nr (loop [i (dec n) body default-val]
                  (if (< i 0) body
                      (recur (dec i)
                             (e/lam (str (first (nth pairs i)))
                                    (nth param-types i) body :default))))
        ;; step: λ fuel ih p1 p2 ... pn => replaced-body
        step-nr (e/lam "fuel" nat
                       (e/lam "ih" arrow-type
                              (loop [i (dec n) body replaced-body]
                                (if (< i 0) body
                                    (recur (dec i)
                                           (e/lam (str (first (nth pairs i)))
                                                  (nth param-types i) body :default))))
                              :default) :default)
        ;; fuel = Nat.succ (measure(params)) where params are bvar 0..n-1 in the outer lambda
        fuel-expr (e/app (e/const' (name/from-string "Nat.succ") []) measure-ansatz)
        ;; Full: λ p1 ... pn => (Nat.rec motive base step fuel) p1 ... pn
        ;; Build inner: apply Nat.rec result to all params
        inner-app (reduce (fn [f i] (e/app f (e/bvar (- n 1 i))))
                          (e/app* nat-rec motive-nr base-nr step-nr fuel-expr)
                          (range n))
        ;; Wrap in outer lambdas
        final-body (loop [i (dec n) body inner-app]
                     (if (< i 0) body
                         (recur (dec i)
                                (e/lam (str (first (nth pairs i)))
                                       (nth param-types i) body :default))))

        ;; Type-check on the real env
        tc (ansatz.kernel.TypeChecker. env)
        _ (.setFuel tc (long config/*default-fuel*))
        _ (.inferType tc final-body)

        ;; Add to environment (swap! to avoid stale env race)
        ci (env/mk-def cname [] type-ansatz final-body)
        _ (swap! ansatz-env env/check-constant-replace ci)
        ;; Register arity for Clojure compilation (FAP/PAP dispatch)
        _ (swap! arity-registry assoc (str fn-name) (compute-arity type-ansatz))
        _ (when *verbose* (println (str "✓ " fn-name " defined (well-founded recursion)")))

        ;; Generate equation theorem: fn(args) = body[fn → fn]
        ;; For the fuel-based Nat.rec approach, this is true by computation:
        ;; Nat.rec motive base step (succ k) args = step k (Nat.rec ... k) args
        ;; which is = body[ih → fn] (the original body with recursive calls intact).
        ;; The proof is just Eq.refl (fn args).
        _ (try
            (let [env' @ansatz-env
                  ;; Build: ∀ params, fn(params) = body-with-fn
                  ;; Create fvars for params
                  fv-base 8300000
                  param-fvids (mapv #(+ fv-base %) (range n))
                  param-fvars (mapv e/fvar param-fvids)
                  ;; fn(params) applied
                  fn-applied (reduce e/app (e/const' cname []) param-fvars)
                  ;; body with fn instead of ih — compile original body with params as fvars
                  ;; Actually, fn-applied WHNF-reduces to the step body. So Eq.refl works.
                  ;; Build eq type: fn(p1,...,pn) = fn(p1,...,pn) — trivially true
                  ;; But we want a useful equation: fn(args) = user-body
                  ;; For that, WHNF fn(args) and use the result as the RHS.
                  tc-eq (ansatz.kernel.TypeChecker. env')
                  _ (.setFuel tc-eq (long config/*default-fuel*))
                  _ (doseq [i (range n)]
                      (.addLocal tc-eq (long (nth param-fvids i))
                                 (str (first (nth pairs i)))
                                 (nth param-types i)))
                  rhs (.whnf (.getReducer tc-eq) fn-applied)
                  ;; Eq type: fn(args) = rhs
                  eq-type (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                  ret-ansatz fn-applied rhs)
                  ;; Wrap in foralls
                  eq-full-type (loop [i (dec n) body eq-type]
                                 (if (< i 0) body
                                     (recur (dec i)
                                            (e/forall' (str (first (nth pairs i)))
                                                       (nth param-types i) body :default))))
                  ;; Proof: Eq.refl (fn(args)) — works because fn(args) def-eq rhs
                  proof-core (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                     ret-ansatz fn-applied)
                  ;; Abstract fvars back to bvars
                  proof-abs (e/abstract-many proof-core param-fvids)
                  ;; Wrap in lambdas
                  proof-full (loop [i (dec n) body proof-abs]
                               (if (< i 0) body
                                   (recur (dec i)
                                          (e/lam (str (first (nth pairs i)))
                                                 (nth param-types i) body :default))))
                  eq-name (name/from-string (str fn-name ".eq_unfold"))
                  eq-ci (env/mk-thm eq-name [] eq-full-type proof-full)]
              (swap! ansatz-env env/check-constant-replace eq-ci)
              (when *verbose*
                (println (str "  ✓ " fn-name ".eq_unfold equation theorem"))))
            (catch Exception e
              (when *verbose*
                (println (str "  ⚠ equation theorem generation failed: " (.getMessage e))))))

        ;; Compile to Clojure — uncurry for multi-arg
        clj-form (ansatz->clj @ansatz-env final-body [])
        ;; The compiled form is curried: (fn [p1] (fn [p2] ... body ...))
        ;; Wrap in uncurried version: (fn [p1 p2 ...] ((curried p1) p2) ...)
        ;; For multi-arg: create a function that accepts both curried and uncurried calls.
        ;; Curried: ((f x) y) — needed when called from other compiled code
        ;; Uncurried: (f x y) — needed for ergonomic Clojure usage
        clj-fn (if (<= n 1)
                 (eval clj-form)
                 (let [param-syms (mapv (fn [[p _]] (gensym (str p "_"))) pairs)
                       curried-call (reduce (fn [f s] (list f s))
                                            (list clj-form (first param-syms))
                                            (rest param-syms))]
                   (eval
                     ;; Multi-arity: 1-arg returns curried, n-arg calls directly
                    `(fn
                       (~[(first param-syms)]
                         ;; Curried: return a fn that takes the remaining args
                        ~(if (= n 2)
                           `(fn [~(second param-syms)] ~curried-call)
                            ;; 3+ args: nested currying
                           (reduce (fn [body s] `(fn [~s] ~body))
                                   curried-call
                                   (reverse (rest param-syms)))))
                       (~param-syms ~curried-call)))))]
    (tag-kernel-fn clj-fn fn-name)))

;; ============================================================
;; Public API
;; ============================================================

(clojure.core/defn- record-coerce-form
  "Form coercing `v` (a map or record) to the defrecord for structure `tname`, RECURSIVELY
   for nested-record fields — so every field (and nested field) is an unboxed defrecord and
   `.field` access is always safe. Reads the structure-registry for the ctor + field types."
  [tname v]
  (let [reg @structure-registry
        {:keys [ctor-sym fields field-types]} (get reg tname)]
    (cons ctor-sym
          (map (fn [fname ftype]
                 (let [fv (list (keyword fname) v)]
                   (if (and (symbol? ftype) (get reg (str ftype)))
                     (record-coerce-form (str ftype) fv)   ; nested record → recurse
                     fv)))
               fields field-types))))

(clojure.core/defn- record-entry-coerce
  "Coercion form for an input param `sym` of a record / List-of-record type → defrecord(s),
   or nil if the type isn't a record. The pipeline-entry boundary that makes `.field` safe.
   GUARDED with `instance?` so an already-converted record passes through untouched — the
   conversion is meant to happen ONCE at the data boundary (the user builds records once),
   not per call; a value that's already a record costs only the instance check."
  [type-form sym]
  (let [reg @structure-registry
        guarded (fn [tname v]
                  (let [cls (symbol (:record-class (get reg tname)))]
                    (list 'if (list 'instance? cls v) v (record-coerce-form tname v))))]
    (cond
      (and (seq? type-form) (= 'List (first type-form)) (symbol? (second type-form))
           (get reg (str (second type-form))))
      (let [r (gensym "r")
            cls (symbol (:record-class (get reg (str (second type-form)))))]
        ;; PER-LIST guard: if the input is already a seq of records, pass it through
        ;; untouched (O(1) — check the first element) — only a map-list pays the one-time
        ;; conversion. Avoids reallocating the spine every call on already-converted data.
        (list 'if (list 'if (list 'clojure.core/seq sym) (list 'instance? cls (list 'clojure.core/first sym)) true)
              sym
              (list 'clojure.core/mapv (list 'fn [r] (record-coerce-form (str (second type-form)) r)) sym)))
      (and (symbol? type-form) (get reg (str type-form)))
      (guarded (str type-form) sym)
      :else nil)))

(clojure.core/defn- inject-record-coercions
  "Wrap a compiled curried `clj-form` so each record-typed param is coerced to a defrecord
   on entry (so the body's `.field` reads are unboxed). No-op when no param is a record."
  [clj-form pairs]
  (let [coerces (keep-indexed
                 (fn [i [_ tform]]
                   (when-let [c (record-entry-coerce tform (symbol (str "v" i)))]
                     [(symbol (str "v" i)) c]))
                 pairs)]
    (if (empty? coerces)
      clj-form
      (let [n (count pairs)
            [pvs body] (loop [f clj-form, k n, acc []]
                         (if (and (pos? k) (seq? f) (= 'fn (first f)))
                           (recur (nth f 2) (dec k) (conj acc (second f)))
                           [acc f]))]
        (reduce (fn [b pv] (list 'fn pv b))
                (list 'let (vec (mapcat identity coerces)) body)
                (reverse pvs))))))


;; ===== moved from core.clj lines 3432,4009 =====
(clojure.core/defn define-verified
  "Define a verified function. Returns compiled Clojure fn."
  [fn-name params ret-type-form body-form]
  (let [env (env)
        pairs (parse-params params)
        ;; Immediate-structural self-recursion (e.g. `(matchEps a)` on a match field) → rewrite the
        ;; self-calls to the recursor IHs so it compiles to T.rec (definitional equations) with no
        ;; `:termination-by` needed. No-op for non-self-recursive bodies.
        body-form (or (structuralize-body env fn-name pairs body-form) body-form)
        body-ansatz (build-telescope env {} 0 pairs body-form e/lam)
        ;; Body elaboration may synthesize new types into the global env (e.g. a
        ;; select-keys result record); refresh so they are visible to the return
        ;; type and the type-checker. The global env ⊇ the captured env — sound.
        venv @ansatz-env
        n (count pairs)
        scope-full (into {} (map-indexed (fn [i [p _]] [p i]) pairs))
        ;; Return-type inference: a `_` return type is inferred from the body.
        ;; The body is the full lambda telescope, so its inferred type IS the
        ;; function's ∀-type — handy when the result type is synthesized (and
        ;; thus unnameable in the signature), e.g. a select-keys projection.
        tc (ansatz.kernel.TypeChecker. venv)
        infer-ret? (= '_ ret-type-form)
        inferred-type (when infer-ret? (.inferType tc body-ansatz))
        ;; ret-ansatz = the codomain (return type): declared, or peeled from the
        ;; inferred ∀-type. Kept as a top-level binding (used by eqn theorems).
        ret-ansatz (if infer-ret?
                     (loop [t inferred-type i 0]
                       (if (and (< i n) (e/forall? t)) (recur (e/forall-body t) (inc i)) t))
                     (sexp->ansatz venv scope-full n ret-type-form))
        type-ansatz (if infer-ret?
                      inferred-type
                      (loop [i (dec n) body ret-ansatz]
                        (if (< i 0) body
                            (let [[pn pt binfo] (nth pairs i)
                                  s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))
                                  ty (sexp->ansatz venv s i pt)]
                              (recur (dec i) (e/forall' (str pn) ty body binfo))))))
        ;; Type-check (inference already validated the body above)
        _ (when-not infer-ret? (.inferType tc body-ansatz))
        ;; Add to environment (swap! to avoid stale env race)
        cname (name/from-string (str fn-name))
        ci (env/mk-def cname [] type-ansatz body-ansatz)
        _ (swap! ansatz-env env/check-constant-replace ci)
        ;; Register arity for Clojure compilation (FAP/PAP dispatch)
        _ (swap! arity-registry assoc (str fn-name) (compute-arity type-ansatz))
        ;; Generate equation theorems for simp (Lean 4's getEqnsFor? pattern).
        ;; Uses fvar-based open/close: create fvars for params+fields,
        ;; WHNF-reduce with fvars, then abstract-many to get correct bvars.
        _ (try
            (let [env' @ansatz-env
                  ;; Find the outermost recursor in the body
                  peeled (loop [e body-ansatz i 0]
                           (if (and (< i n) (e/lam? e))
                             (recur (e/lam-body e) (inc i))
                             e))
                  [rec-head _] (e/get-app-fn-args peeled)]
              (when (and (e/const? rec-head)
                         (.endsWith ^String (name/->string (e/const-name rec-head)) ".rec"))
                (let [^ConstantInfo rci (env/lookup env' (e/const-name rec-head))
                      np (.numParams rci)
                      ind-name-str (subs (name/->string (e/const-name rec-head)) 0
                                         (- (count (name/->string (e/const-name rec-head))) 4))
                      ^ConstantInfo ind-ci (env/lookup env' (name/from-string ind-name-str))
                      ctor-names (.ctors ind-ci)
                      ;; Determine discriminant position from recursor major premise.
                      ;; The major premise is the last rec arg and is a bvar.
                      ;; bvar(k) in the peeled body = param at position (n - 1 - k).
                      rec-args-raw (vec (e/get-app-args peeled))
                      major-arg (peek rec-args-raw)
                      discr-pos (if (e/bvar? major-arg)
                                  (- n 1 (e/bvar-idx major-arg))
                                  (dec n))  ;; fallback: last param
                      n-non-discr (dec n)]
                  (doseq [i (range (count ctor-names))]
                    (try
                      (let [ctor-name (nth ctor-names i)
                            ^ConstantInfo ctor-ci (env/lookup env' ctor-name)
                            nf (.numFields ctor-ci)
                            cnp (.numParams ctor-ci)
                            ;; Create fvars for non-discriminant params and ctor fields
                            fv-base 8200000
                            param-fvids (mapv #(+ fv-base %) (range n-non-discr))
                            field-fvids (mapv #(+ fv-base n-non-discr %) (range nf))
                            all-fvids (vec (concat param-fvids field-fvids))
                            param-fvars (mapv e/fvar param-fvids)
                            field-fvars (mapv e/fvar field-fvids)
                            ;; Get actual inductive type params from recursor args
                            rec-args (vec (e/get-app-args peeled))
                            ind-type-params (vec (take np rec-args))
                            ;; Constructor levels
                            ctor-levels (let [clps (vec (.levelParams ctor-ci))
                                              rlps (vec (.levelParams rci))
                                              rlevs (e/const-levels rec-head)]
                                          (mapv (fn [clp]
                                                  (let [idx (.indexOf rlps clp)]
                                                    (if (>= idx 0) (nth rlevs idx) lvl/zero)))
                                                clps))
                            ;; Build ctor-app and LHS with fvars.
                            ;; Place ctor-app at the discriminant position, other params around it.
                            ctor-app (reduce e/app (e/const' ctor-name ctor-levels)
                                             (concat ind-type-params field-fvars))
                            lhs-args (let [pv (vec param-fvars)]
                                       (into (into (subvec pv 0 discr-pos) [ctor-app])
                                             (subvec pv discr-pos)))
                            lhs (reduce e/app (e/const' cname []) lhs-args)
                            ;; Get field types by peeling ctor type (with levels instantiated)
                            ctor-type-inst (let [clps (vec (.levelParams ctor-ci))
                                                 subst (zipmap clps ctor-levels)]
                                             (if (seq subst)
                                               (e/instantiate-level-params (.type ctor-ci) subst)
                                               (.type ctor-ci)))
                            field-types (loop [t ctor-type-inst skip cnp j 0 acc []]
                                          (if (or (not (e/forall? t)) (>= j nf)) acc
                                              (if (pos? skip)
                                                (let [sub (if (< (- cnp skip) (count ind-type-params))
                                                            (nth ind-type-params (- cnp skip))
                                                            (e/sort' lvl/zero))]
                                                  (recur (e/instantiate1 (e/forall-body t) sub) (dec skip) j acc))
                                                (recur (e/instantiate1 (e/forall-body t) (nth field-fvars j))
                                                       0 (inc j) (conj acc (e/forall-type t))))))
                            ;; Non-discriminant param indices (all except discr-pos)
                            non-discr-indices (vec (remove #{discr-pos} (range n)))
                            ;; Register fvars in TC's lctx for WHNF reduction
                            param-types (mapv (fn [j]
                                                (let [orig-idx (nth non-discr-indices j)
                                                      [pn pt-form] (nth (vec pairs) orig-idx)]
                                                  (sexp->ansatz env'
                                                                (into {} (map-indexed (fn [k [p _]] [p k]) (take orig-idx (vec pairs))))
                                                                orig-idx pt-form)))
                                              (range n-non-discr))
                            st' (reduce (fn [s [fid nm tp]]
                                          (update s :lctx red/lctx-add-local fid nm tp))
                                        (tc/mk-tc-state env')
                                        (concat (map vector param-fvids
                                                     (map #(str (first (nth (vec pairs) (nth non-discr-indices %)))) (range n-non-discr))
                                                     param-types)
                                                (map vector field-fvids
                                                     (map #(str "f" %) (range nf))
                                                     field-types)))
                            ;; Build RHS using RESTRICTED WHNF (Lean 4: withReducible).
                            ;; Use transparency mode 0 (reducible) with only the function
                            ;; being defined + its recursor in the allow set.
                            ;; This reduces the match/recursor (iota) but NOT + or other fns.
                            rhs-raw
                            (let [tc-eq (ansatz.kernel.TypeChecker. env')
                                  allow-set (java.util.HashSet.)
                                  rec-name-obj (e/const-name rec-head)]
                              ;; Allow ONLY the function being defined to be delta-unfolded.
                              ;; Iota reduction (recursor matching) is always allowed — it's
                              ;; not delta. This means: llen unfolds → List.rec exposed →
                              ;; iota selects cons branch → result has 1 + llen tail.
                              ;; The + is NOT unfolded because it's not in the allow set.
                              (.add allow-set cname)
                              (.setFuel tc-eq 5000000)
                              (.setTransparency tc-eq 0)
                              (.setDeltaAllowSet tc-eq allow-set)
                              ;; Add fvars to lctx
                              (doseq [[fid nm tp] (concat
                                                   (map vector param-fvids
                                                        (map #(str (first (nth (vec pairs) (nth non-discr-indices %)))) (range n-non-discr))
                                                        param-types)
                                                   (map vector field-fvids
                                                        (map #(str "f" %) (range nf))
                                                        field-types))]
                                (.addLocal tc-eq (long fid) (str nm) tp))
                              ;; WHNF with restricted transparency
                              (.whnf (.getReducer tc-eq) lhs))
                            ;; Replace recursive recursor patterns with function calls.
                            ;; Lean 4: equation theorems show f(args) not raw recursors.
                            ;; The rec parameter in the cons-case gets substituted during
                            ;; iota reduction with the full recursor applied to the tail.
                            ;; We compute that exact expression and replace all occurrences
                            ;; with f(tail_fvar). This is Lean 4's replaceRecApps equivalent.
                            rec-args (vec (e/get-app-args peeled))
                            ;; The rec value = full recursor applied to the tail fvar.
                            ;; It's the same as the function body but with tail fvar as scrutinee.
                            ;; Identify which field is the recursive one (type matches the inductive)
                            rec-field-idx (first (keep-indexed
                                                  (fn [j ft]
                                                    (let [[fh _] (e/get-app-fn-args ft)]
                                                      (when (and (e/const? fh)
                                                                 (= (name/->string (e/const-name fh)) ind-name-str))
                                                        j)))
                                                  field-types))
                            rhs-clean
                            (if rec-field-idx
                              (try
                              ;; Build the rec-value by instantiating the body with the
                              ;; ACTUAL constructor args (including l=ctor-app), then
                              ;; replacing the major premise with tail-fvar.
                              ;; Lean 4: replaceRecApps finds .brecOn/.below references.
                              ;; Our approach: the rec-value has l=ctor-app baked in
                              ;; (from the outer beta reduction), matching the RHS.
                                (let [tail-fvar (nth field-fvars rec-field-idx)
                                    ;; Instantiate body with params + ctor-app for the discriminant
                                      ^ConstantInfo fn-ci (env/lookup env' cname)
                                      fn-body (.value fn-ci)
                                    ;; Instantiate outer lambdas with param fvars and ctor-app
                                    ;; Args in original parameter order: insert ctor-app at discr-pos
                                      inst-args (let [pv (vec param-fvars)]
                                                  (into (into (subvec pv 0 discr-pos) [ctor-app])
                                                        (subvec pv discr-pos)))
                                      inst-body (loop [b fn-body fvs inst-args]
                                                  (if (empty? fvs) b
                                                      (recur (e/instantiate1 (e/lam-body b) (first fvs))
                                                             (rest fvs))))
                                    ;; inst-body is the rec application with all params substituted
                                    ;; Replace major premise (last arg) with tail-fvar
                                      [inst-head inst-args] (e/get-app-fn-args inst-body)
                                      rec-val (reduce e/app inst-head
                                                      (conj (vec (butlast inst-args)) tail-fvar))
                                    ;; The function call to replace with
                                    ;; Place tail-fvar at discriminant position
                                      f-call-args (let [pv (vec param-fvars)]
                                                    (into (into (subvec pv 0 discr-pos) [tail-fvar])
                                                          (subvec pv discr-pos)))
                                      f-call (reduce e/app (e/const' cname []) f-call-args)
                                    ;; Find and replace rec-val with f-call in the RHS
                                      replace-fn (fn replace-rv [expr]
                                                   (if (= expr rec-val)
                                                     f-call
                                                     (case (e/tag expr)
                                                       :app (let [nf (replace-rv (e/app-fn expr))
                                                                  na (replace-rv (e/app-arg expr))]
                                                              (if (and (identical? nf (e/app-fn expr))
                                                                       (identical? na (e/app-arg expr)))
                                                                expr (e/app nf na)))
                                                       :lam (let [nb (replace-rv (e/lam-body expr))]
                                                              (if (identical? nb (e/lam-body expr))
                                                                expr (e/lam (e/lam-name expr) (e/lam-type expr)
                                                                            nb (e/lam-info expr))))
                                                       expr)))]
                                  (replace-fn rhs-raw))
                                (catch Exception _ rhs-raw))
                              rhs-raw)
                            ;; Create auxiliary matcher definitions for stuck inner recursors
                            ;; (Lean 4: each match expression becomes a named matcher).
                            ;; Replace stuck recursors in the RHS with calls to auxiliaries.
                            ;; Each auxiliary gets its own equation theorems.
                            rhs-with-aux
                            (try
                              (let [aux-counter (atom 0)
                                    create-aux (fn create-aux [rhs depth]
                                                 (if (> depth 3) rhs
                                                     (let [[h as] (e/get-app-fn-args rhs)]
                                                       (if (and (e/const? h)
                                                                (.endsWith ^String (name/->string (e/const-name h)) ".rec")
                                                                (seq as) (e/fvar? (last as)))
                                            ;; Found a stuck recursor — create auxiliary definition
                                                         (let [scrut-fvar-id (e/fvar-id (last as))
                                                  ;; Collect all fvars actually used in this stuck expression.
                                                  ;; This ensures deeper recursive calls capture the right context.
                                                               expr-fvars (let [acc (atom #{})]
                                                                            (letfn [(walk [e]
                                                                                      (when (e/has-fvar-flag e)
                                                                                        (case (e/tag e)
                                                                                          :fvar (swap! acc conj (e/fvar-id e))
                                                                                          :app (do (walk (e/app-fn e)) (walk (e/app-arg e)))
                                                                                          :lam (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                                                                                          :forall (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                                                                                          nil)))]
                                                                              (walk rhs))
                                                                            @acc)
                                                               all-fv-ids (vec (remove #{scrut-fvar-id}
                                                                                       (sort (disj expr-fvars scrut-fvar-id))))
                                                  ;; The auxiliary takes: all free vars + the scrutinee as last param
                                                               aux-fvids (conj all-fv-ids scrut-fvar-id)
                                                               aux-n (swap! aux-counter inc)
                                                               aux-name-str (str fn-name "._match_" aux-n)
                                                               aux-cname (name/from-string aux-name-str)
                                                  ;; Build aux body: abstract fvars from rhs, wrap in lambdas
                                                               aux-body-abs (e/abstract-many rhs aux-fvids)
                                                               aux-fvar-types (mapv (fn [fid]
                                                                                      (let [d (get-in st' [:lctx fid])]
                                                                                        (or (:type d) (e/sort' lvl/zero))))
                                                                                    aux-fvids)
                                                               aux-body (loop [j (dec (count aux-fvids)) body aux-body-abs]
                                                                          (if (< j 0) body
                                                                              (let [fid (nth aux-fvids j)
                                                                                    ft (nth aux-fvar-types j)
                                                                                    nm (or (:name (get-in st' [:lctx fid])) (str "x" j))]
                                                                                (recur (dec j) (e/lam nm ft body :default)))))
                                                  ;; Infer aux type from body
                                                               aux-type (try
                                                                          (let [tc-aux (ansatz.kernel.TypeChecker. @ansatz-env)]
                                                                            (.setFuel tc-aux (int config/*default-fuel*))
                                                                            (.inferType tc-aux aux-body))
                                                                          (catch Exception _ nil))]
                                                           (if-not aux-type
                                                             rhs  ;; fallback: return original stuck expr
                                                             (do ;; Register the auxiliary definition
                                                               (swap! ansatz-env env/check-constant-replace
                                                                      (env/mk-def aux-cname [] aux-type aux-body))
                                                ;; Generate equation theorems for the auxiliary
                                                ;; (Use a simple approach: the aux matches on its last param)
                                                               (try
                                                                 (let [irci (env/lookup @ansatz-env (e/const-name h))
                                                                       iind-str (let [s (name/->string (e/const-name h))]
                                                                                  (subs s 0 (- (count s) 4)))
                                                                       iind-ci (env/lookup @ansatz-env (name/from-string iind-str))
                                                                       ictors (.ctors iind-ci) inp (.numParams irci)
                                                                       iparams (vec (take inp as))
                                                                       ilevels (e/const-levels h)
                                                                       n-aux (count aux-fvids)]
                                                                   (doseq [ci-idx (range (count ictors))]
                                                                     (try
                                                                       (let [icn (nth ictors ci-idx)
                                                                             ^ConstantInfo icci (env/lookup @ansatz-env icn)
                                                                             inf (.numFields icci) icnp (.numParams icci)
                                                              ;; Create fvars for ctor fields
                                                                             cf-base (+ fv-base 5000000 (* aux-n 10000) (* ci-idx 100))
                                                                             cf-fvids (mapv #(+ cf-base %) (range inf))
                                                                             cf-fvars (mapv e/fvar cf-fvids)
                                                              ;; Ctor field types
                                                                             ict-sub (zipmap (vec (.levelParams icci)) (vec (rest ilevels)))
                                                                             ict-inst (if (seq ict-sub) (e/instantiate-level-params (.type icci) ict-sub) (.type icci))
                                                                             cf-types (loop [t ict-inst sk icnp j 0 acc []]
                                                                                        (if (or (not (e/forall? t)) (>= j inf)) acc
                                                                                            (if (pos? sk)
                                                                                              (recur (e/instantiate1 (e/forall-body t)
                                                                                                                     (if (< (- icnp sk) (count iparams))
                                                                                                                       (nth iparams (- icnp sk)) (e/sort' lvl/zero)))
                                                                                                     (dec sk) j acc)
                                                                                              (recur (e/instantiate1 (e/forall-body t) (nth cf-fvars j))
                                                                                                     0 (inc j) (conj acc (e/forall-type t))))))
                                                              ;; Build ctor application
                                                                             ica (reduce e/app (e/const' icn (vec (rest ilevels)))
                                                                                         (concat iparams cf-fvars))
                                                              ;; LHS: aux(params..., ctor-app)
                                                                             aux-lhs (reduce e/app (e/const' aux-cname [])
                                                                                             (concat (mapv e/fvar all-fv-ids) [ica]))
                                                              ;; RHS: WHNF of aux applied to concrete ctor.
                                                              ;; Use CURRENT env (includes aux def) for TC state.
                                                                             st-cf (reduce (fn [s [fid nm tp]]
                                                                                             (update s :lctx red/lctx-add-local fid nm tp))
                                                                                           (assoc (tc/mk-tc-state @ansatz-env) :lctx (:lctx st'))
                                                                                           (map vector cf-fvids
                                                                                                (map #(str "cf" %) (range inf)) cf-types))
                                                                             aux-rhs-raw (#'tc/cached-whnf st-cf aux-lhs)
                                                              ;; Recursively replace stuck recursors in the aux RHS
                                                                             aux-rhs (create-aux aux-rhs-raw (inc depth))
                                                              ;; Build equation: ∀ params fields, aux(params, ctor) = rhs
                                                                             eq-body (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                                                                             ret-ansatz aux-lhs aux-rhs)
                                                                             abs-eq (e/abstract-many eq-body (vec (concat param-fvids field-fvids all-fv-ids cf-fvids)))
                                                              ;; Wait — this is getting complex. Let me simplify.
                                                              ;; Just register the equation with Eq.refl proof.
                                                                             all-eq-fvids (vec (distinct (concat all-fv-ids cf-fvids)))
                                                                             all-eq-types (vec (concat (mapv (fn [fid] (or (:type (get-in st-cf [:lctx fid])) (e/sort' lvl/zero))) all-fv-ids)
                                                                                                       cf-types))
                                                                             abs-eq2 (e/abstract-many eq-body all-eq-fvids)
                                                                             full-eq-type (loop [j (dec (count all-eq-fvids)) body abs-eq2]
                                                                                            (if (< j 0) body
                                                                                                (recur (dec j) (e/forall' (str "p" j) (nth all-eq-types j) body :default))))
                                                                             rfl-pf (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                                                            ret-ansatz aux-lhs)
                                                                             abs-pf (e/abstract-many rfl-pf all-eq-fvids)
                                                                             full-pf (loop [j (dec (count all-eq-fvids)) body abs-pf]
                                                                                       (if (< j 0) body
                                                                                           (recur (dec j) (e/lam (str "p" j) (nth all-eq-types j) body :default))))
                                                                             eqn-nm (name/from-string (str aux-name-str ".eq_" (inc ci-idx)))]
                                                          ;; Verify and register
                                                                         (let [tc-v (ansatz.kernel.TypeChecker. @ansatz-env)]
                                                                           (.setFuel tc-v (int config/*default-fuel*))
                                                                           (.inferType tc-v full-pf)
                                                                           (swap! ansatz-env env/check-constant-replace (env/mk-thm eqn-nm [] full-eq-type full-pf))
                                                                           (when *verbose* (println "  aux eq_" (inc ci-idx) "for" aux-name-str))))
                                                                       (catch Exception ex
                                                                         (when *verbose*
                                                                           (println "  aux eq_" (inc ci-idx) "for" aux-name-str "FAILED:" (.getMessage ex))
                                                                           (.printStackTrace ex *out*))))))
                                                                 (catch Exception ex
                                                                   (when *verbose*
                                                                     (println "  aux gen for" aux-name-str "FAILED:" (.getMessage ex)))))
                                                ;; Return call to the auxiliary instead of the stuck recursor
                                                               (reduce e/app (e/const' aux-cname []) (mapv e/fvar aux-fvids)))))
                                            ;; No stuck recursor at top — recurse into sub-expressions
                                                         (if (e/app? rhs)
                                                           (let [f (create-aux (e/app-fn rhs) depth)
                                                                 a (create-aux (e/app-arg rhs) depth)]
                                                             (if (and (identical? f (e/app-fn rhs)) (identical? a (e/app-arg rhs)))
                                                               rhs (e/app f a)))
                                                           rhs)))))]
                                (create-aux rhs-clean 0))
                              (catch Exception _ rhs-clean))
                            ;; Split inner stuck recursors (Lean 4: mkEqnTypes splitMatch?).
                            ;; KEEP the general equation (matches opaque args via star-key)
                            ;; AND add split variants (match concrete constructors).
                            split-equations
                            (try
                              (let [split-counter (atom 0)]
                                (letfn [(find-stuck [expr]
                                          (let [[h as] (e/get-app-fn-args expr)]
                                            (cond
                                              (and (e/const? h)
                                                   (.endsWith ^String (name/->string (e/const-name h)) ".rec")
                                                   (seq as) (e/fvar? (last as)))
                                              {:rec-head h :rec-args (vec as) :scrut-fvar (e/fvar-id (last as))}
                                              (e/app? expr)
                                              (or (find-stuck (e/app-fn expr)) (find-stuck (e/app-arg expr)))
                                              :else nil)))
                                        (split-rec [st rhs the-lhs xfvids xtypes sfx depth]
                                          (if (> depth 2) nil
                                              (when-let [{:keys [rec-head rec-args scrut-fvar]} (find-stuck rhs)]
                                                (let [irci (env/lookup env' (e/const-name rec-head))
                                                      iind-str (let [s (name/->string (e/const-name rec-head))]
                                                                 (subs s 0 (- (count s) 4)))
                                                      iind-ci (env/lookup env' (name/from-string iind-str))
                                                      ictors (.ctors iind-ci) inp (.numParams irci)
                                                      iparams (vec (take inp rec-args))
                                                      ilevels (e/const-levels rec-head)]
                                                  (vec (mapcat
                                                        (fn [ci-idx]
                                                          (try
                                                            (let [icn (nth ictors ci-idx)
                                                                  ^ConstantInfo icci (env/lookup env' icn)
                                                                  inf (.numFields icci) icnp (.numParams icci)
                                                                  base (+ fv-base n-non-discr nf (count xfvids)
                                                                          (* ci-idx 100) (* depth 1000))
                                                                  iffids (mapv #(+ base %) (range inf))
                                                                  iffvars (mapv e/fvar iffids)
                                                                  ict-sub (zipmap (vec (.levelParams icci)) (vec (rest ilevels)))
                                                                  ict-inst (let [raw (.type icci)]
                                                                             (if (seq ict-sub) (e/instantiate-level-params raw ict-sub) raw))
                                                                  iftypes (loop [t ict-inst sk icnp j 0 acc []]
                                                                            (if (or (not (e/forall? t)) (>= j inf)) acc
                                                                                (if (pos? sk)
                                                                                  (recur (e/instantiate1 (e/forall-body t)
                                                                                                         (if (< (- icnp sk) (count iparams))
                                                                                                           (nth iparams (- icnp sk)) (e/sort' lvl/zero)))
                                                                                         (dec sk) j acc)
                                                                                  (recur (e/instantiate1 (e/forall-body t) (nth iffvars j))
                                                                                         0 (inc j) (conj acc (e/forall-type t))))))
                                                                  ica (reduce e/app (e/const' icn (vec (rest ilevels)))
                                                                              (concat iparams iffvars))
                                                                  rhs' (e/instantiate1 (e/abstract1 rhs scrut-fvar) ica)
                                                                  lhs' (e/instantiate1 (e/abstract1 the-lhs scrut-fvar) ica)
                                                                  st' (reduce (fn [s [fid nm tp]]
                                                                                (update s :lctx red/lctx-add-local fid nm tp))
                                                                              st (map vector iffids
                                                                                      (map #(str "g" %) (range inf)) iftypes))
                                                                  rhs-r (#'tc/cached-whnf st' rhs')]
                                                           ;; Recurse for deeper splits
                                                              (or (split-rec st' rhs-r lhs' (vec (concat xfvids iffids))
                                                                             (vec (concat xtypes iftypes))
                                                                             (+ (* sfx 10) (inc ci-idx)) (inc depth))
                                                               ;; Leaf: use flat sequential numbering (Lean 4 style)
                                                                  (let [n (swap! split-counter inc)]
                                                                    [{:rhs rhs-r :lhs lhs' :extra-fvids (vec (concat xfvids iffids))
                                                                      :extra-types (vec (concat xtypes iftypes))
                                                                      :suffix (str "s" n)}])))
                                                            (catch Exception _ nil)))
                                                        (range (count ictors))))))))]
                                  (split-rec st' rhs-clean lhs [] [] 0 0)))
                              (catch Exception _ nil))
                            ;; Following Lean 4 (mkEqnTypes/splitMatch?): when leaf-level
                            ;; split equations exist, use ONLY them — each has a concrete
                            ;; constructor pattern. Falls back to general equation only
                            ;; when no splits exist (e.g., Bool inner match).
                            equations (if (seq split-equations)
                                        (vec split-equations)
                                        [{:rhs rhs-clean :condition nil :suffix nil}])]
                        ;; Build and register each equation using abstract-many
                        (doseq [[_ {:keys [rhs lhs extra-fvids extra-types condition suffix]
                                    :or {lhs lhs extra-fvids [] extra-types []}}]
                                (map-indexed vector equations)]
                          (let [;; Collect fvars actually used in LHS and RHS.
                                ;; Split equations may have "phantom" field fvars replaced
                                ;; by inner constructors. Exclude these (Lean 4 style).
                                used-fvars (let [acc (atom #{})]
                                             (letfn [(walk [e]
                                                       (when (e/has-fvar-flag e)
                                                         (case (e/tag e)
                                                           :fvar (swap! acc conj (e/fvar-id e))
                                                           :app (do (walk (e/app-fn e)) (walk (e/app-arg e)))
                                                           :lam (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                                                           :forall (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                                                           nil)))]
                                               (walk lhs) (walk rhs))
                                             @acc)
                                all-fv-pairs (filterv (fn [[fid _]] (contains? used-fvars fid))
                                                      (map vector
                                                           (concat field-fvids extra-fvids)
                                                           (concat field-types extra-types)))
                                all-fvids (mapv first all-fv-pairs)
                                all-ftypes (mapv second all-fv-pairs)
                                all-nf (count all-fvids)
                                ;; Eq ret_type lhs rhs (all with fvars)
                                eq-body (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                                ret-ansatz lhs rhs)
                                eq-body (if condition (e/arrow condition eq-body) eq-body)
                                abstracted-type
                                (e/abstract-many eq-body (vec (concat param-fvids all-fvids)))
                                ;; Wrap in foralls: all fields then params (right to left)
                                full-type (loop [j (dec all-nf) body abstracted-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (if (< j nf) (str "f" j) (str "g" (- j nf)))
                                                                  (nth all-ftypes j) body :default))))
                                full-type (loop [j (dec n-non-discr) body full-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (str (first (nth (vec pairs) (nth non-discr-indices j))))
                                                                  (nth param-types j) body :default))))
                                ;; Proof: rfl (with fvars), then abstract
                                rfl-proof (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                  ret-ansatz lhs)
                                proof-body (if condition (e/lam "h" condition rfl-proof :default) rfl-proof)
                                abstracted-proof (e/abstract-many proof-body
                                                                  (vec (concat param-fvids all-fvids)))
                                full-proof (loop [j (dec all-nf) body abstracted-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (if (< j nf) (str "f" j) (str "g" (- j nf)))
                                                               (nth all-ftypes j) body :default))))
                                full-proof (loop [j (dec n-non-discr) body full-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (str (first (nth (vec pairs) (nth non-discr-indices j))))
                                                               (nth param-types j) body :default))))
                                eqn-name (name/from-string (str fn-name ".eq_" (inc i) (or suffix "")))]
                            (try
                              (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) "type:" (e/->string full-type)))
                              (let [tc-v (ansatz.kernel.TypeChecker. @ansatz-env)]
                                (.setFuel tc-v (int config/*default-fuel*))
                                (.inferType tc-v full-proof)
                                (swap! ansatz-env env/check-constant-replace (env/mk-thm eqn-name [] full-type full-proof))
                                (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) ":" (e/->string full-type))))
                              (catch Exception e
                                (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) "skipped:" (.getMessage e))))))))
                      (catch Exception e
                        (when *verbose* (println "  eq" (inc i) "gen failed:" (.getMessage e)))))))))
            (catch Exception ex
              (when *verbose* (println "  eq-gen outer:" (.getMessage ex)))))
        ;; Optionally optimize the body (verified deforestation/fusion) before
        ;; lowering — the runtime computes the same thing in fewer passes, with a
        ;; kernel-checked proof it equals the verified body. Graceful fallback.
        opt-result (when *optimize*
                     (try ((requiring-resolve 'ansatz.optimize/optimize-body) @ansatz-env body-ansatz n)
                          (catch Throwable _ nil)))
        _ (when opt-result
            (swap! optimization-registry assoc (str fn-name)
                   (select-keys opt-result [:changed? :verified? :rewrites
                                            :stages-before :stages-after
                                            :passes-before :passes-after]))
            (when (and *verbose* (:changed? opt-result))
              (println "  optimized:" (:rewrites opt-result))))
        runtime-body (if (and opt-result (:changed? opt-result) (:verified? opt-result))
                       (:term opt-result) body-ansatz)
        ;; Compile to Clojure — uncurry multi-arg functions for flat calls. If the
        ;; body was optimized, guard the lowering: any construct the optimized term
        ;; produces that ansatz->clj can't yet compile falls back to the original
        ;; (proven-equal) body — optimization can never break compilation.
        clj-form0 (if (identical? runtime-body body-ansatz)
                    (ansatz->clj @ansatz-env body-ansatz [])
                    (try (ansatz->clj @ansatz-env runtime-body [])
                         (catch Throwable _ (ansatz->clj @ansatz-env body-ansatz []))))
        ;; boundary: coerce record-typed inputs (maps) to defrecords so `.field` reads unbox
        clj-form (inject-record-coercions clj-form0 (vec pairs))
        clj-fn (if (<= n 1)
                 (eval clj-form)
                 ;; Multi-arg: support both flat (f x y) and curried ((f x) y) calls
                 (let [param-syms (mapv (fn [[p _]] (gensym (str p "_"))) (vec pairs))
                       curried-call (reduce (fn [f s] (list f s))
                                            (list clj-form (first param-syms))
                                            (rest param-syms))]
                   (eval
                    `(fn
                       (~[(first param-syms)]
                        ~(if (= n 2)
                           `(fn [~(second param-syms)] ~curried-call)
                           (reduce (fn [body s] `(fn [~s] ~body))
                                   curried-call
                                   (reverse (rest param-syms)))))
                       (~param-syms ~curried-call)))))]
    (when *verbose* (println "✓" fn-name ":" (pr-str clj-form)))
    (tag-kernel-fn clj-fn fn-name)))


