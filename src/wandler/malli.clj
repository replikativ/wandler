;; The Ansatz ⟷ Malli boundary.
;;
;; This is the two-way bridge between Ansatz's verified (CIC) types and Malli
;; schemas:
;;
;;   EXPORT  (CIC type → Malli schema)  — a verified function's kernel type
;;           becomes a Malli function schema, for runtime contract checking and
;;           for GENERATIVE TESTING of the compiled runtime (`ansatz->clj`),
;;           which is the least formally-verified link in the pipeline — the
;;           runtime↔kernel bridge every optimization rests on.
;;
;;   IMPORT  (Malli schema → CIC type / record model) — a Malli `:map`/`:tuple`
;;           schema drives a kernel record model, so the verified reducer planner
;;           can reason about pipelines over native Clojure maps using the
;;           schema as its column/type information (à la a query planner).
;;
;; Malli is an OPTIONAL dependency (alias `:malli`). The schema-form mappings are
;; pure data and need no Malli on the classpath; only registration,
;; instrumentation, and generative testing load it lazily via `requiring-resolve`.
;; There is zero coupling into `ansatz.core` — bringing Malli in is an explicit
;; choice the user makes here.
;;
;; Credit: the EXPORT mapping (`type-expr->malli`, `fn-schema`) and the
;; registration/instrumentation helpers originate from Felix Barbalet's PR #2
;; (replikativ/ansatz "Malli function schema bridge"), carried forward and
;; extended here with the review's design (no core coupling, extensibility hook,
;; warn-don't-silently-:any) plus the import direction and generative testing.

(ns wandler.malli
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel ConstantInfo]))

(defn- resolve-malli! [sym]
  (or (requiring-resolve sym)
      (throw (ex-info (str "Cannot resolve " sym ". Add the :malli alias "
                           "(metosin/malli) to bring Malli in.") {:sym sym}))))

(defn- nm [s] (name/from-string s))

;; ============================================================
;; Extensibility + diagnostics
;; ============================================================

(def ^:dynamic *warn-unknown?*
  "When true, mapping an unknown type to :any emits a warning so the user knows
   the schema is approximate."
  true)

(def type-mappings
  "User-registered CIC-type-name → (fn [args opts] -> malli-schema) overrides for
   types the built-in table doesn't cover (e.g. Mathlib structures)."
  (atom {}))

(defn register-type-mapping!
  "Register a custom CIC-type-name → Malli-schema mapping. `f` receives the
   applied type arguments (Exprs) and opts, and returns a Malli schema form."
  [type-name f]
  (swap! type-mappings assoc type-name f))

(defn- unknown [type-name]
  (when *warn-unknown?*
    (binding [*out* *err*]
      (println "WARN wandler.malli: no schema for" type-name "— using :any")))
  :any)

;; ============================================================
;; EXPORT — CIC type → Malli schema  (from PR #2, refactored)
;; ============================================================

(defn type-expr->malli
  "Convert a CIC type Expr to a Malli schema form (plain data). Unknown types map
   to :any (with a warning unless `*warn-unknown?*` is false). `opts` may carry
   `:struct-registry` (atom) for structure types."
  ([expr] (type-expr->malli expr nil))
  ([expr opts]
   (cond
     (e/lit-nat? expr) :int

     (e/const? expr)
     (let [n (name/->string (e/const-name expr))]
       (case n
         "Nat"    [:and :int [:>= 0]]
         "Int"    :int
         "Bool"   :boolean
         "String" :string
         "Float"  :double
         "Real"   number?
         "UInt8"  [:and :int [:>= 0] [:<= 255]]
         "UInt16" [:and :int [:>= 0] [:<= 65535]]
         "UInt32" [:and :int [:>= 0]]
         "UInt64" [:and :int [:>= 0]]
         "Unit"   :nil
         "True"   :boolean
         "False"  :boolean
         "Prop"   :any
         (if-let [info (and (:struct-registry opts) (get @(:struct-registry opts) n))]
           (into [:map] (mapv (fn [f] [(keyword f) :any]) (:fields info)))
           (if-let [f (get @type-mappings n)] (f [] opts) (unknown n)))))

     (e/app? expr)
     (let [[head args] (e/get-app-fn-args expr)]
       (if (e/const? head)
         (let [n (name/->string (e/const-name head))]
           (case n
             "List"   [:sequential (type-expr->malli (first args) opts)]
             "Array"  [:sequential (type-expr->malli (first args) opts)]
             "Option" [:maybe (type-expr->malli (first args) opts)]
             "Prod"   [:tuple (type-expr->malli (first args) opts)
                       (type-expr->malli (second args) opts)]
             "Sum"    [:or (type-expr->malli (first args) opts)
                       (type-expr->malli (second args) opts)]
             (if-let [info (and (:struct-registry opts) (get @(:struct-registry opts) n))]
               (into [:map] (mapv (fn [f] [(keyword f) :any]) (:fields info)))
               (if-let [f (get @type-mappings n)] (f args opts) (unknown n)))))
         :any))

     (e/forall? expr) 'ifn?
     :else :any)))

(defn fn-schema
  "A Malli function schema `[:=> [:cat in…] out]` from a verified function's CIC
   type. Only `:default` (runtime) parameters are included — implicit and
   instance-implicit binders are erased, matching `ansatz.core/compute-arity`."
  ([fn-type] (fn-schema fn-type nil))
  ([fn-type opts]
   (loop [t fn-type inputs []]
     (if (e/forall? t)
       (if (= :default (e/forall-info t))
         (recur (e/forall-body t) (conj inputs (type-expr->malli (e/forall-type t) opts)))
         (recur (e/forall-body t) inputs))
       [:=> (into [:cat] inputs) (type-expr->malli t opts)]))))

;; ============================================================
;; IMPORT — Malli schema → CIC type / kernel record model
;; ============================================================

(def ^:private u1 (lvl/succ lvl/zero))

(defn- kconst [s] (e/const' (nm s) []))

(defn- bound-prop
  "A Nat predicate body over `(bvar 0)` for the given `ge`/`lt` bounds (a conjunction
   if both are present), or nil if neither. Carries the refinement; erased at runtime."
  [ge lt]
  (let [Nat (kconst "Nat")
        le (fn [a b] (e/app* (e/const' (nm "LE.le") [lvl/zero]) Nat (e/const' (nm "instLENat") []) a b))
        ltp (fn [a b] (e/app* (e/const' (nm "LT.lt") [lvl/zero]) Nat (e/const' (nm "instLTNat") []) a b))
        gp (when ge (le (e/lit-nat ge) (e/bvar 0)))     ; ge ≤ v
        lp (when lt (ltp (e/bvar 0) (e/lit-nat lt)))]   ; v < lt
    (cond (and gp lp) (e/app* (e/const' (nm "And") []) gp lp)
          gp gp
          lp lp
          :else nil)))

(defn- ksubtype-nat
  "`Subtype Nat (fun v => <ge/lt bounds>)`, or nil if no bound."
  [ge lt]
  (when-let [body (bound-prop ge lt)]
    (e/app* (e/const' (nm "Subtype") [u1]) (kconst "Nat") (e/lam "v" (kconst "Nat") body :default))))

(defn- string-length-prop
  "A Prop body `min ≤ s.length ∧ s.length ≤ max` over `(bvar 0 : String)` for the malli
   `[:string {:min .. :max ..}]` bounds (a conjunction if both), or nil if neither.
   The refinement is carried in the TYPE and erased at runtime (the value is a plain String)."
  [mn mx]
  (let [Nat (kconst "Nat")
        len-s (e/app (e/const' (nm "String.length") []) (e/bvar 0))   ; s.length : Nat
        le (fn [a b] (e/app* (e/const' (nm "LE.le") [lvl/zero]) Nat (e/const' (nm "instLENat") []) a b))
        lo (when mn (le (e/lit-nat mn) len-s))    ; min ≤ s.length
        hi (when mx (le len-s (e/lit-nat mx)))]   ; s.length ≤ max
    (cond (and lo hi) (e/app* (e/const' (nm "And") []) lo hi)
          lo lo
          hi hi
          :else nil)))

(defn- ksubtype-string
  "`Subtype String (fun s => min ≤ s.length ∧ s.length ≤ max)`, or nil if no length bound.
   `u1` is the SORT level of α = String : Type 0 = Sort 1 (as for `ksubtype-nat`)."
  [mn mx]
  (when-let [body (string-length-prop mn mx)]
    (e/app* (e/const' (nm "Subtype") [u1]) (kconst "String")
            (e/lam "s" (kconst "String") body :default))))

;; Prod.{u,v} : Type u → Type v → Type (max u v) — its level params are the TYPE
;; universes of the components. Record fields are at Type 0 (Nat, or `Subtype Nat _`),
;; so the level is 0, NOT u1 (=1). `Prod.{1,1} Nat Nat` asserts Nat : Type 1 and is
;; ill-typed (non-cumulative universes); lenient inferType accepted it, .check rejects.
;; (Contrast `Subtype.{u}` above, whose u is the SORT level of α = 1 for Nat — hence u1.)
(defn- kprod [a b] (e/app* (e/const' (nm "Prod") [lvl/zero lvl/zero]) a b))
(defn- kprods
  "RIGHT-nested Prod of `ts` — `(a, (b, c))`, the tuple convention the field-ops
   (`tail-type`/`rget` in wandler.reducers.record) navigate. A left fold
   `(reduce kprod ts)` would build `((a,b),c)` instead, which disagrees with the
   getters (Prod.snd then hits the wrong component) — masked by lenient inferType."
  [ts]
  (let [r (reverse ts)] (reduce (fn [acc t] (kprod t acc)) (first r) (rest r))))
(defn- klist [a] (e/app (e/const' (nm "List") [lvl/zero]) a))
(defn- koption [a] (e/app (e/const' (nm "Option") [lvl/zero]) a))

(defn- deref-registry
  "Resolve a malli schema REFERENCE — a registered keyword (`:order`, `:user/email`),
   `[:ref k]`, or `[:schema {:registry …} k]` — through the registry to its underlying
   FORM, so a user's registered domain types flow into the kernel type universe with zero
   per-type wiring. `m/deref` resolves the ref (registry context preserved by `m/schema`);
   nil when `schema` is not a resolvable reference (caller falls through to its error).
   The `not=` guard avoids treating a built-in as a self-ref and looping."
  [schema]
  (try
    (let [m-schema (resolve-malli! 'malli.core/schema)
          m-deref  (resolve-malli! 'malli.core/deref)
          m-form   (resolve-malli! 'malli.core/form)
          f (m-form (m-deref (m-schema schema)))]
      (when (not= f schema) f))
    (catch Throwable _ nil)))

(defn malli->type-expr
  "Convert a Malli schema form to a CIC type Expr (the inverse of
   `type-expr->malli` over the supported subset). `:map` schemas become a
   right-nested `Prod` record type; `:tuple` likewise."
  [schema]
  (cond
    (keyword? schema)
    (case schema
      :int (kconst "Int")
      :boolean (kconst "Bool")
      :string (kconst "String")
      :double (kconst "Float")
      :nil (kconst "Unit")
      ;; not a built-in scalar — try the registry: a registered domain type resolves
      ;; to its form and we recurse. The user registers types once in malli; pipelines
      ;; over them just work.
      (if-let [f (deref-registry schema)]
        (malli->type-expr f)
        (throw (ex-info "Unsupported scalar Malli schema" {:schema schema}))))

    (vector? schema)
    (let [[tag & more] schema]
      (case tag
        ;; Scalar refinements over :int:
        ;;   [:>= 0]  → Nat                         (definitional; Tier-1 filters)
        ;;   [:>= k]  → {v : Nat // k ≤ v}  (k>0)    (refinement; Tier-3 filters)
        ;;   otherwise → the underlying type (refinement dropped)
        :and (let [ge (some (fn [s] (when (and (vector? s) (= :>= (first s))) (second s))) more)
                   lt (some (fn [s] (when (and (vector? s) (= :< (first s))) (second s))) more)
                   ge* (when (and ge (pos? ge)) ge)]    ; [:>= 0] is free for Nat
               (cond
                 (and (= :int (first more)) (or ge* lt)) (ksubtype-nat ge* lt)
                 (and (= :int (first more)) (some #(= % [:>= 0]) more)) (kconst "Nat")
                 :else (malli->type-expr (first more))))
        ;; [:string {:min n :max m}] → {s : String // n ≤ s.length ∧ s.length ≤ m}
        ;; (length refinement; a regex/format refinement [:re p] is future work). Bare
        ;; [:string] or unbounded props → plain String.
        :string (let [props (when (map? (first more)) (first more))]
                  (or (ksubtype-string (:min props) (:max props)) (kconst "String")))
        :sequential (klist (malli->type-expr (first more)))
        :maybe (koption (malli->type-expr (first more)))
        :tuple (kprods (map malli->type-expr more))
        :map (kprods (map (fn [entry]
                            (malli->type-expr (if (= 3 (count entry)) (nth entry 2) (nth entry 1))))
                          more))
        ;; `[:int {:min n :max m}]` — malli's native bounded int (the props-map form, as
        ;; opposed to `[:and :int [:>= n]]`). min→ lower bound, max m → v ≤ m (= v < m+1).
        ;; `[:int {:min 0}]` is just Nat; bare `[:int]` is Int.
        :int (let [props (when (map? (first more)) (first more))
                   mn (:min props), mx (:max props)
                   ge* (when (and mn (pos? mn)) mn)
                   lt* (when mx (inc mx))]
               (cond (or ge* lt*)       (ksubtype-nat ge* lt*)
                     (and mn (>= mn 0)) (kconst "Nat")
                     :else              (kconst "Int")))
        :double (kconst "Float")
        ;; `[:ref k]`, `[:schema {:registry …} k]`, or any registered composite — resolve
        ;; via the registry and recurse, so referenced types flow in like inline ones.
        (if-let [f (deref-registry schema)]
          (malli->type-expr f)
          (throw (ex-info "Unsupported Malli schema form" {:schema schema})))))

    :else (throw (ex-info "Unsupported Malli schema" {:schema schema}))))

(defn malli-record
  "Compile a Malli `:map` schema into a kernel RECORD MODEL for the planner:

     {:keys        [k0 k1 …]                ; field keys, in order
      :index       {k0 0, k1 1, …}          ; key → field position
      :field-types [<Expr> …]               ; kernel type of each field
      :rec-type    <Expr>}                  ; right-nested Prod of the fields

   This is what lets the verified reducer planner reason about pipelines over
   native Clojure maps using the Malli schema as its schema/column info."
  [schema]
  (when-not (and (vector? schema) (= :map (first schema)))
    (throw (ex-info "malli-record expects a [:map …] schema" {:schema schema})))
  (let [entries (rest schema)
        entries (remove map? entries)               ; drop a leading props map if present
        ks (mapv first entries)
        field-types (mapv (fn [entry]
                            (let [[_ a b] entry]
                              (malli->type-expr (if (= 3 (count entry)) b a))))
                          entries)]
    {:keys ks
     :index (into {} (map-indexed (fn [i k] [k i]) ks))
     :field-types field-types
     :rec-type (kprods field-types)}))

;; ============================================================
;; Registration + instrumentation  (from PR #2)
;; ============================================================

(defn register!
  "Register a Malli function schema for a verified function."
  [ns-sym fn-sym schema-form]
  ((resolve-malli! 'malli.core/-register-function-schema!) ns-sym fn-sym schema-form {}))

(defn- struct-registry []
  @(requiring-resolve 'ansatz.core/structure-registry))

(defn- ansatz-env []
  (deref @(requiring-resolve 'ansatz.core/ansatz-env)))

(defn register-from-defn!
  "Register a verified function with Malli by looking up its CIC type in the
   Ansatz environment. Opting into Malli is explicit — call this (or
   `register-all!`) for the functions you want instrumented; `ansatz.core` has
   no Malli coupling."
  [ns-sym fn-name-sym]
  (let [env (ansatz-env)
        ^ConstantInfo ci (env/lookup env (nm (str fn-name-sym)))]
    (when ci
      (register! ns-sym fn-name-sym
                 (fn-schema (.type ci) {:env env :struct-registry (struct-registry)})))))

(defn instrument!
  "Instrument all registered verified functions with Malli runtime validation."
  ([] (instrument! nil))
  ([opts] ((resolve-malli! 'malli.instrument/instrument!) opts)))

(defn unstrument!
  "Remove Malli instrumentation."
  ([] (unstrument! nil))
  ([opts] ((resolve-malli! 'malli.instrument/unstrument!) opts)))

(defn fn-schema-for
  "Return the Malli function schema for a verified function by name (inspection)."
  [fn-name]
  (let [env (ansatz-env)
        ^ConstantInfo ci (env/lookup env (nm (str fn-name)))]
    (when ci (fn-schema (.type ci) {:env env :struct-registry (struct-registry)}))))

;; ============================================================
;; Generative testing — property-test the compiled runtime bridge
;; ============================================================

(defn check-verified
  "Property-test a verified function's COMPILED runtime against its CIC type,
   using Malli generators. This exercises `ansatz->clj` — the runtime↔kernel
   bridge that every verified optimization trusts. Returns nil on success, or a
   failure map (`:input`/`:output`/…). Requires Malli.

   `f` must be an `ansatz.core/defn`-defined function (it carries its kernel
   constant name in `:ansatz.core/kernel-name` metadata)."
  ([f] (check-verified f nil))
  ([f opts]
   (let [kname (:ansatz.core/kernel-name (meta f))
         _ (when-not kname
             (throw (ex-info "check-verified needs an a/defn function (kernel-name metadata)"
                             {:fn f})))
         env (ansatz-env)
         ^ConstantInfo ci (env/lookup env (nm (str kname)))
         schema (fn-schema (.type ci) {:env env :struct-registry (struct-registry)})
         function-checker (resolve-malli! 'malli.generator/function-checker)]
     ((function-checker schema (or opts {})) f))))
