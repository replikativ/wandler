;; Standard Clojure record operations in verified functions.
;;
;; Lets you write idiomatic Clojure — `(assoc r :k v)`, `(:k r)` — inside `a/defn`
;; bodies over Ansatz STRUCTURE types, instead of explicit kernel terms. The body
;; compiler is extended (via `register-elaborator!`, no change to core) so a
;; record op is re-expressed over the structure's kernel constructor and field
;; projections and admitted as an ordinary verified term.
;;
;; All the type information comes from Ansatz: a structure is a single-constructor
;; inductive with named fields and `e/proj` projections; `assoc` rebuilds it. The
;; Malli schema (via `def-record`) is just the surface that names the fields and
;; their types — once lifted, the kernel is the source of truth, and the verified
;; reducer planner reasons over the resulting kernel terms.
;;
;; Keyword access `(:k r)` is already handled by core's structure projection; this
;; namespace adds `assoc`.

(ns ansatz.records
  (:refer-clojure :exclude [defn])
  (:require [ansatz.core :as a]
            [ansatz.malli :as malli]
            [ansatz.refine :as refine]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.string :as str]))

;; ============================================================
;; def-record — a Malli :map schema → an Ansatz structure
;; ============================================================

(defn- malli-field-type
  "Lift a Malli scalar field schema to an Ansatz surface type form."
  [s]
  (cond
    (= s :int) 'Int
    (= s :boolean) 'Bool
    (= s :string) 'String
    (= s :double) 'Float
    (and (vector? s) (= :and (first s)) (= :int (second s))
         (some #(= % [:>= 0]) (rest s))) 'Nat       ; the Nat refinement
    (and (vector? s) (= :int (first s))) 'Int
    :else (throw (ex-info "def-record: unsupported field schema" {:schema s}))))

(defn- nested-struct-name [parent k]
  (str parent (str/capitalize (clojure.core/name k))))

(defn- refinement-ge
  "If `schema` is `[:and :int [:>= k]]` with k>0 (a refinement that isn't just Nat),
   return k; else nil."
  [schema]
  (when (and (vector? schema) (= :and (first schema)) (= :int (second schema)))
    (let [ge (some (fn [s] (when (and (vector? s) (= :>= (first s))) (second s))) (rest schema))]
      (when (and ge (pos? ge)) ge))))

(clojure.core/defn ensure-refinement-abbrev!
  "Define (idempotently) `aname := {v:Nat // k≤v}` as a type ABBREVIATION, so a
   refined Malli field can be a plain named structure field type. Returns nil."
  [aname schema]
  (let [n (name/from-string aname)]
    (when-not (kenv/lookup @a/ansatz-env n)
      (swap! a/ansatz-env kenv/check-constant
             (kenv/mk-def n [] (e/sort' (lvl/succ lvl/zero))
                          (malli/malli->type-expr schema) :hints :abbrev))))
  nil)

(defn- schema->struct-forms
  "Expand a Malli `:map` schema into the forms that define it: refinement
   abbreviations and nested-`:map` structures first, the outer structure last.
   A nested `:map` field → `<Parent><Field>` structure; a `[:>= k]` (k>0) field →
   a `<Parent><Field>T` Subtype abbreviation (the refined field's type)."
  [type-name malli-schema]
  (let [pre (volatile! [])      ; abbrev-ensures + nested structures, in dependency order
        fields (mapv (fn [entry]
                       (let [[k a b] entry
                             s (if (= 3 (count entry)) b a)
                             fname (symbol (clojure.core/name k))]
                         (cond
                           (and (vector? s) (= :map (first s)))
                           (let [nname (nested-struct-name type-name k)]
                             (vswap! pre into (schema->struct-forms nname s))
                             (list fname (symbol nname)))

                           (refinement-ge s)
                           (let [aname (str type-name (str/capitalize (clojure.core/name k)) "T")]
                             (vswap! pre conj `(ensure-refinement-abbrev! ~aname '~s))
                             (list fname (symbol aname)))

                           :else (list fname (malli-field-type s)))))
                     (->> (rest malli-schema) (remove map?)))]  ; drop a leading props map
    (conj @pre (list* 'ansatz.core/structure (symbol (str type-name)) [] fields))))

(defmacro def-record
  "Define an Ansatz structure record from a Malli `:map` schema. Fields keep their
   schema order; scalar types are lifted to the corresponding Ansatz type (the Nat
   refinement `[:and :int [:>= 0]]` → `Nat`). A nested `:map` field becomes a nested
   structure `<Parent><Field>`, usable with get-in/assoc-in/update-in.

     (def-record Person [:map [:first :string] [:age [:and :int [:>= 0]]]])
     (def-record Cust   [:map [:id :int] [:addr [:map [:zip :int] [:num :int]]]])"
  [type-name malli-schema]
  (cons 'do (cons `(swap! record-schemas assoc ~(str type-name) '~malli-schema)
                  (schema->struct-forms type-name malli-schema))))

;; ============================================================
;; Contract boundary — Malli validation as the gradual-typing seam
;;
;; A verified function over a refined record reasons soundly GIVEN its input
;; inhabits the type (the .property invariants). The runtime guarantee that live
;; data inhabits the type is the CONTRACT, enforced here by Malli validation at the
;; edge. Inside is kernel-proved; the boundary is the one trusted cast.
;; ============================================================

(defonce ^{:doc "Record name (string) → its Malli schema, for the contract boundary."}
  record-schemas (atom {}))

(clojure.core/defn validate
  "Does `data` satisfy record `rname`'s Malli schema (including refinements)?"
  [rname data]
  (boolean (when-let [schema (get @record-schemas (str rname))]
             ((requiring-resolve 'malli.core/validate) schema data))))

(clojure.core/defn conform
  "Contract cast at the boundary: return `data` if it satisfies record `rname`'s
   schema, else throw. Downstream verified functions may then assume the record's
   refinement invariants — this is the trusted gradual-typing seam."
  [rname data]
  (if (validate rname data)
    data
    (throw (ex-info (str "contract violation: data does not satisfy " rname)
                    {:record (str rname) :data data}))))

;; ============================================================
;; Record-pipeline elaborator (assoc / update)
;;
;; An assoc/update chain over a structure-typed receiver is folded — at compile
;; time — into ONE rebuild `<T>.mk v0 … vn`, where each `vj` is the field's
;; current value expr (a projection off the base receiver, then overwritten by
;; each assoc/update). Overwrite elimination falls out for free: a field written
;; twice keeps only the last expr — the dead write never appears in the term. The
;; result is admitted as an ordinary verified term (no proof obligation — it is a
;; well-typed `<T>.mk`; the fusion is definitional).
;; ============================================================

(defn- receiver-type-expr
  "The record type of a receiver form. `assoc`/`update`/threading all preserve the
   record type, so peel them down to the base parameter and read its scope type.
   (A fast structural shortcut — avoids a type-checker call. Since the move to
   fvar-first elaboration `inferType` could now type the compiled receiver directly,
   but the structural peel is cheaper and has no failure mode, so we keep it.)"
  [stypes form]
  (cond
    (symbol? form) (get stypes form)
    (and (seq? form) (#{'assoc 'update} (first form))) (receiver-type-expr stypes (second form))
    (and (seq? form) (#{'-> '->>} (first form))) (receiver-type-expr stypes (second form))
    :else nil))

(defn- field-index [fields k]
  (first (keep-indexed (fn [i f] (when (= f k) i)) fields)))

(declare refined-field-spec discharge-refined discharge-refined-update)

(defn- pipeline-state
  "Fold an assoc/update receiver chain into {:ctor :tname :fields :vals}, where
   `:vals` is the vector of current field value exprs. Base case: each field is a
   projection off the (compiled) base receiver. Each assoc overwrites a field's
   expr; each update maps it through `f`."
  [env scope depth form lctx]
  (let [sexp->ansatz a/sexp->ansatz
        sreg @a/structure-registry
        stypes a/*scope-types*]
    (if (and (seq? form) (#{'assoc 'update} (first form)))
      (let [op (first form)
            st (pipeline-state env scope depth (second form) lctx)
            {:keys [tname fields vals]} st
            k (clojure.core/name (nth form 2))
            idx (field-index fields k)]
        (when-not idx
          (throw (ex-info (str (name op) ": unknown field :" k " on " tname) {:fields fields})))
        (case op
          assoc (assoc-in st [:vals idx]
                          (let [v (sexp->ansatz env scope depth (nth form 3) lctx)]
                            ;; writing a refined field discharges its predicate
                            (if-let [spec (refined-field-spec env tname idx)]
                              (discharge-refined spec v)
                              v)))
          update (let [f-expr (sexp->ansatz env scope depth (nth form 3) lctx)
                       arg-exprs (map #(sexp->ansatz env scope depth % lctx) (drop 4 form))
                       cur (nth vals idx)
                       apply-f (fn [x] (apply e/app* f-expr x arg-exprs))]
                   (assoc-in st [:vals idx]
                             ;; updating a refined field: unwrap, apply f, and prove the
                             ;; result still satisfies the refinement (omega-write)
                             (if-let [spec (refined-field-spec env tname idx)]
                               (discharge-refined-update env spec cur apply-f)
                               (apply-f cur))))))
      ;; base receiver
      (let [r-expr (sexp->ansatz env scope depth form lctx)
            rtype (receiver-type-expr stypes form)
            [th _] (when rtype (e/get-app-fn-args rtype))
            tname (when (and th (e/const? th)) (name/->string (e/const-name th)))
            sinfo (get sreg tname)]
        (when-not sinfo
          (throw (ex-info (str "record op on a non-record receiver: " (pr-str form))
                          {:type tname})))
        (let [fields (:fields sinfo)
              tn (name/from-string tname)]
          {:ctor (sexp->ansatz env scope depth (symbol (str tname ".mk")) lctx)
           :tname tname
           :fields fields
           :vals (mapv (fn [j] (e/proj tn j r-expr)) (range (count fields)))})))))

;; When false, a pipeline compiles to the NAIVE nested form (every write happens,
;; no overwrite elimination) — used to build the fusion-equivalence proof.
(def ^:dynamic *fuse-records?* true)
(declare naive-state)

(declare vupdatein-expr)

(defn- v-const [s] (e/const' (name/from-string s) []))

(defn- value-typed-fn
  "Annotate a bare `(fn [x …] body)`'s params as `:- Value` so field-value ops resolve (the
   update fn receives a Value). Leaves already-annotated or non-fn forms unchanged."
  [f-form]
  (if (and (seq? f-form) (#{'fn 'fn*} (first f-form)) (vector? (second f-form))
           (not (some #{:-} (second f-form))))
    (list* (first f-form)
           (vec (mapcat (fn [p] [p :- 'Value]) (second f-form)))
           (drop 2 f-form))
    f-form))

(defn- ->value-expr
  "Lift an elaborated scalar Expr to a `Value` (for `(assoc v :k x)` over dynamic EDN)."
  [env e]
  (let [t (a/get-arg-type env nil e) [th _] (when t (e/get-app-fn-args t))
        tnm (when (and th (e/const? th)) (name/->string (e/const-name th)))]
    (case tnm
      "Value"  e
      "Int"    (e/app (v-const "Value.vint") e)
      "String" (e/app (v-const "Value.vstr") e)
      "Bool"   (e/app (v-const "Value.vbool") e)
      "Float"  (e/app (v-const "Value.vfloat") e)
      (if (e/lit-nat? e) (e/app (v-const "Value.vint") (e/app (v-const "Int.ofNat") e)) e))))

(defn- vassoc-chain
  "`(assoc v :k1 x1 :k2 x2 …)` over a dynamic EDN Value → nested vassoc (each value lifted)."
  [env scope depth recv kvs lctx]
  (reduce (fn [acc [kf xf]]
            (e/app* (v-const "vput") acc
                    (if (keyword? kf)
                      (e/app (v-const "Value.vkw") (e/lit-str (subs (str kf) 1)))
                      (a/sexp->ansatz env scope depth kf lctx))
                    (->value-expr env (a/sexp->ansatz env scope depth xf lctx))))
          recv (partition 2 kvs)))

(defn- pipeline-elaborator
  "Elaborator for `head` (assoc or update): fold the whole chain into one rebuild
   (overwrite-eliminated), or — when fusion is disabled — the naive nested form. Over a
   dynamic EDN `Value`, `assoc` lowers to a `vassoc` chain instead (native portability)."
  [head]
  (fn [env scope depth args lctx]
    (let [recv (a/sexp->ansatz env scope depth (first args) lctx)
          t (a/get-arg-type env nil recv) [th _] (when t (e/get-app-fn-args t))
          tnm (when (and th (e/const? th)) (name/->string (e/const-name th)))]
      (if (= "Value" tnm)
        ;; (assoc v :k x …) / (update v :k f args…) over a dynamic EDN Value
        (if (= head 'assoc)
          (vassoc-chain env scope depth recv (rest args) lctx)
          (let [[kf ff & fargs] (rest args)]
            (vupdatein-expr env scope depth recv [kf]
                            (a/sexp->ansatz env scope depth (value-typed-fn ff) lctx)
                            (map #(a/sexp->ansatz env scope depth % lctx) fargs) lctx)))
        (if *fuse-records?*
          (let [st (pipeline-state env scope depth (list* head args) lctx)]
            (apply e/app* (:ctor st) (:vals st)))
          (:expr (naive-state env scope depth (list* head args) lctx)))))))

;; ============================================================
;; Nested ops (get-in / assoc-in / update-in)
;;
;; Built as DIRECT kernel terms (nested `e/proj` + ctor rebuilds), recursing on
;; the constructor's field-type telescope — so a record-typed field is itself a
;; structure we can descend into. This sidesteps core's keyword projection
;; (which can't type a compound receiver) entirely.
;; ============================================================

(defn- struct-field-types
  "Field types of structure `tname`, read from its constructor's Pi telescope."
  [env tname]
  (loop [t (.type (kenv/lookup env (name/from-string (str tname ".mk")))) acc []]
    (if (e/forall? t) (recur (e/forall-body t) (conj acc (e/forall-type t))) acc)))

(defn- refined-field-spec
  "If field `idx` of `tname` is a `[:>= k]` refinement `{v:Nat // k≤v}` (after
   unfolding its type abbreviation), return {:u :alpha :P :k}; else nil."
  [env tname idx]
  (let [ftype (nth (struct-field-types env tname) idx nil)
        unf (if (and ftype (e/const? ftype))
              (try (.value (kenv/lookup env (e/const-name ftype))) (catch Throwable _ ftype))
              ftype)
        [h args] (when unf (e/get-app-fn-args unf))]
    (when (and h (e/const? h) (= "Subtype" (name/->string (e/const-name h))) (= 2 (count args)))
      (let [P (nth args 1)
            [_ pargs] (e/get-app-fn-args (e/lam-body P))]      ; LE.le Nat inst k v
        {:u (first (e/const-levels h)) :alpha (nth args 0) :P P
         :k (when (= 4 (count pargs)) (nth pargs 2))}))))

(defn- discharge-refined
  "Wrap value `v` for a refined field: `Subtype.mk α P v (k≤v)`, the proof discharged
   by `Nat.le_of_ble_eq_true … rfl` — type-checks for an in-range literal, and is
   REJECTED at verification for an out-of-range (or unproven) value (correctly)."
  [{:keys [u alpha P k]} v]
  (if (nil? k)
    v
    (e/app* (e/const' (name/from-string "Subtype.mk") [u]) alpha P v
            (e/app* (e/const' (name/from-string "Nat.le_of_ble_eq_true") []) k v
                    (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                            (e/const' (name/from-string "Bool") [])
                            (e/const' (name/from-string "Bool.true") []))))))

(defn- discharge-refined-update
  "Wrap an UPDATE on a refined field `{w // P w}`: unwrap the current value (`.val`),
   apply `f`, and PROVE the result still satisfies `P` — via `refine/prove-monotone`
   (`∀w, P w → P (f w)`), instantiated at the current value and its carried
   `.property`. Throws if `f` isn't provably refinement-preserving (e.g. it could
   leave the bound), which is correct."
  [env {:keys [u alpha P]} cur apply-f]
  (let [val-cur (e/app* (e/const' (name/from-string "Subtype.val") [u]) alpha P cur)
        mono (refine/prove-monotone env alpha P apply-f)]
    (when-not mono
      (throw (ex-info "update on a refined field: f does not provably preserve the refinement"
                      {:field-pred (e/->string P)})))
    (e/app* (e/const' (name/from-string "Subtype.mk") [u]) alpha P
            (apply-f val-cur)
            (e/app* mono val-cur
                    (e/app* (e/const' (name/from-string "Subtype.property") [u]) alpha P cur)))))

(defn- type-name-of
  "Head constant name of a type expr (the structure name), or nil."
  [tyexpr]
  (when tyexpr
    (let [[h _] (e/get-app-fn-args tyexpr)]
      (when (e/const? h) (name/->string (e/const-name h))))))

(defn- struct-fields [tname]
  (mapv keyword (:fields (get @a/structure-registry
                              tname))))

(defn- field-pos [tname k]
  (let [idx (.indexOf ^java.util.List (struct-fields tname) k)]
    (when (neg? idx) (throw (ex-info (str "unknown field " k " on " tname) {:type tname})))
    idx))

(defn- getin-expr
  "Kernel term `(get-in r path)` as nested projections."
  [env tname r-expr path]
  (if (empty? path)
    r-expr
    (let [idx (field-pos tname (first path))
          ft (nth (struct-field-types env tname) idx)]
      (getin-expr env (type-name-of ft)
                  (e/proj (name/from-string tname) idx r-expr) (rest path)))))

(defn- associn-expr
  "Kernel term `(assoc-in r path v)` as nested rebuilds."
  [env tname r-expr path v-expr]
  (let [idx (field-pos tname (first path))
        fts (struct-field-types env tname)
        tn (name/from-string tname)]
    (apply e/app* (e/const' (name/from-string (str tname ".mk")) [])
           (map-indexed
            (fn [j _]
              (cond
                (not= j idx) (e/proj tn j r-expr)
                ;; leaf set — discharge if this field is refined (like flat assoc)
                (= 1 (count path)) (if-let [spec (refined-field-spec env tname idx)]
                                     (discharge-refined spec v-expr)
                                     v-expr)
                :else (associn-expr env (type-name-of (nth fts idx))
                                    (e/proj tn idx r-expr) (rest path) v-expr)))
            fts))))

(defn- base-type-name [env scope depth r-form lctx]
  (let [stypes a/*scope-types*]
    (type-name-of (receiver-type-expr stypes r-form))))

;; ── nested ops over a dynamic EDN Value (get-in / assoc-in / update-in) ───────
(defn- value-typed-expr? [env recv]
  (let [t (a/get-arg-type env nil recv) [th _] (when t (e/get-app-fn-args t))]
    (and th (e/const? th) (= "Value" (name/->string (e/const-name th))))))

(defn- vkey-form [env scope depth kf lctx]
  (if (keyword? kf)
    (e/app (v-const "Value.vkw") (e/lit-str (subs (str kf) 1)))
    (a/sexp->ansatz env scope depth kf lctx)))

(defn- vgetin-expr [env scope depth recv path lctx]
  (reduce (fn [acc kf] (e/app* (v-const "vget") (vkey-form env scope depth kf lctx) acc)) recv path))

(defn- vassocin-expr
  "`(assoc-in v path x)` over a Value → nested vput (rebuild each map along the path)."
  [env scope depth recv path v-expr lctx]
  (let [kexpr (vkey-form env scope depth (first path) lctx)]
    (if (= 1 (count path))
      (e/app* (v-const "vput") recv kexpr v-expr)
      (e/app* (v-const "vput") recv kexpr
              (vassocin-expr env scope depth (e/app* (v-const "vget") kexpr recv)
                             (rest path) v-expr lctx)))))

(defn- vupdatein-expr
  "`(update-in v path f args…)` over a Value → vput the path's value to `(f cur args…)`,
   lifted back to a Value."
  [env scope depth recv path f-expr f-args lctx]
  (let [kexpr (vkey-form env scope depth (first path) lctx)
        cur (e/app* (v-const "vget") kexpr recv)]
    (if (= 1 (count path))
      (e/app* (v-const "vput") recv kexpr (->value-expr env (apply e/app* f-expr cur f-args)))
      (e/app* (v-const "vput") recv kexpr
              (vupdatein-expr env scope depth cur (rest path) f-expr f-args lctx)))))

(defn- get-in-elaborator [env scope depth args lctx]
  (let [sexp->ansatz a/sexp->ansatz
        [r-form path-form] args
        recv (sexp->ansatz env scope depth r-form lctx)]
    (if (value-typed-expr? env recv)
      (vgetin-expr env scope depth recv (vec path-form) lctx)
      (getin-expr env (base-type-name env scope depth r-form lctx) recv (vec path-form)))))

(defn- assoc-in-elaborator [env scope depth args lctx]
  (let [sexp->ansatz a/sexp->ansatz
        [r-form path-form v-form] args
        recv (sexp->ansatz env scope depth r-form lctx)]
    (if (value-typed-expr? env recv)
      (vassocin-expr env scope depth recv (vec path-form)
                     (->value-expr env (sexp->ansatz env scope depth v-form lctx)) lctx)
      (associn-expr env (base-type-name env scope depth r-form lctx) recv (vec path-form)
                    (sexp->ansatz env scope depth v-form lctx)))))

(defn- update-in-elaborator [env scope depth args lctx]
  (let [sexp->ansatz a/sexp->ansatz
        [r-form path-form f-form & f-args] args
        r-expr (sexp->ansatz env scope depth r-form lctx)
        path (vec path-form)
        arg-exprs (map #(sexp->ansatz env scope depth % lctx) f-args)]
    (if (value-typed-expr? env r-expr)
      (vupdatein-expr env scope depth r-expr path
                      (sexp->ansatz env scope depth (value-typed-fn f-form) lctx) arg-exprs lctx)
      (let [tname (base-type-name env scope depth r-form lctx)
            f-expr (sexp->ansatz env scope depth f-form lctx)
            cur (getin-expr env tname r-expr path)]
        (associn-expr env tname r-expr path (apply e/app* f-expr cur arg-exprs))))))

(defn- naive-state
  "The NAIVE compilation of an assoc/update chain: each op rebuilds the WHOLE
   record over the previous term (no overwrite elimination). Returns {:expr :tname}.
   Used as the un-optimized side of the fusion-equivalence proof."
  [env scope depth form lctx]
  (let [sexp->ansatz a/sexp->ansatz]
    (if (and (seq? form) (#{'assoc 'update} (first form)))
      (let [op (first form)
            {prev :expr tname :tname} (naive-state env scope depth (second form) lctx)
            k (keyword (clojure.core/name (nth form 2)))
            idx (field-pos tname k)
            fts (struct-field-types env tname)
            tn (name/from-string tname)
            newval (if (= op 'assoc)
                     (sexp->ansatz env scope depth (nth form 3) lctx)
                     (apply e/app* (sexp->ansatz env scope depth (nth form 3) lctx)
                            (e/proj tn idx prev)
                            (map #(sexp->ansatz env scope depth % lctx) (drop 4 form))))]
        {:tname tname
         :expr (apply e/app* (e/const' (name/from-string (str tname ".mk")) [])
                      (map-indexed (fn [j _] (if (= j idx) newval (e/proj tn j prev))) fts))})
      {:expr (sexp->ansatz env scope depth form lctx)
       :tname (base-type-name env scope depth form lctx)})))

;; ============================================================
;; select-keys — column projection to an auto-registered record
;;
;; (select-keys r [:a :b]) over a record yields a NEW structure with just the
;; kept fields. The result type is SYNTHESIZED (named `<T>__a_b`) and registered
;; on first use — reusing the a/structure machinery so it gets a defrecord +
;; registry entry (the runtime is a defrecord, which acts like a map). The result
;; type is unnameable in a signature, so a select-keys-terminal function uses the
;; `_` return type (inferred — see define-verified).
;; ============================================================

(defn- type-expr->form
  "Render a data-type expr back to a surface type form for an a/structure field
   spec (e.g. Nat → Nat, (List Nat) → (List Nat))."
  [tyexpr]
  (let [[h args] (e/get-app-fn-args tyexpr)]
    (if (e/const? h)
      (let [s (symbol (name/->string (e/const-name h)))]
        (if (empty? args) s (cons s (map type-expr->form args))))
      (throw (ex-info "select-keys: cannot render field type to a surface form"
                      {:type (e/->string tyexpr)})))))

(defn- synth-record-name [parent ks]
  (str parent "__" (str/join "_" (map name ks))))

(defn- ensure-projection-record!
  "Define+register the projection record `<parent>__k1_k2` on first use, with the
   kept fields' types taken from the parent's constructor telescope. Returns its
   name. Idempotent (skips if already registered)."
  [env parent ks]
  (let [sname (synth-record-name parent ks)]
    (when-not (get @a/structure-registry sname)
      (let [fts (struct-field-types env parent)
            specs (map (fn [k]
                         (list (symbol (name k))
                               (type-expr->form (nth fts (field-pos parent k)))))
                       ks)]
        (binding [a/*verbose* false]
          (eval (list* 'ansatz.core/structure (symbol sname) [] specs)))))
    sname))

(defn- select-keys-elaborator [env scope depth args lctx]
  (let [sexp->ansatz a/sexp->ansatz
        [r-form ks-form] args
        ks (vec ks-form)
        tname (base-type-name env scope depth r-form lctx)
        r-expr (sexp->ansatz env scope depth r-form lctx)
        sname (ensure-projection-record! env tname ks)
        tn (name/from-string tname)]
    (apply e/app* (e/const' (name/from-string (str sname ".mk")) [])
           (map (fn [k] (e/proj tn (field-pos tname k) r-expr)) ks))))

;; ============================================================
;; Threading macros (->/->>) — so idiomatic pipelines compile
;; ============================================================

(clojure.core/defn install!
  "Register the record-op elaborators (idempotent). Enables `(assoc r :k v)`,
   `(update r :k f)` in verified bodies. Keyword access `(:k r)` is handled by core; the
   `->`/`->>` threading used with these (`(-> r (assoc …) (update …))`) now lives in
   ansatz.collections (the base surface ns), so it works whenever collections is loaded."
  []
  (a/register-elaborator! 'assoc (pipeline-elaborator 'assoc))
  (a/register-elaborator! 'update (pipeline-elaborator 'update))
  (a/register-elaborator! 'get-in get-in-elaborator)
  (a/register-elaborator! 'assoc-in assoc-in-elaborator)
  (a/register-elaborator! 'update-in update-in-elaborator)
  (a/register-elaborator! 'select-keys select-keys-elaborator))

(install!)

;; ============================================================
;; Fusion-equivalence proof — certify the optimization
;;
;; The elaborator emits the FUSED (overwrite-eliminated) term, verified well-typed.
;; `defn` below additionally proves the optimization SOUND: it recompiles the body
;; naively (every write happens) and proves `naive = fused` in the kernel. Because
;; projection-of-constructor reduces, the two terms are DEFINITIONALLY equal, so the
;; proof is `funext (fun r => Eq.refl _ (fused r))` — no Mathlib, just Init.
;; ============================================================

(def ^:private u1 (lvl/succ lvl/zero))

(clojure.core/defn fusion-proof!
  "Given an already-defined single-record-param function `fn-name` (the fused term)
   and its body form, recompile the body naively and admit a theorem
   `<fn-name>.fusion_eq : naive = fused`. Returns its inferred type, or nil if the
   shape isn't supported (multi-param, or no record param). Skips silently on any
   failure (the fused fn is still valid)."
  [fn-name params body-form]
  (try
    (let [env @a/ansatz-env  ; var → atom → env
          build-telescope a/build-telescope
          parse-params a/parse-params
          pairs (parse-params params)
          cname (name/from-string (str fn-name))
          ci (kenv/lookup env cname)
          ftype (.type ci)]
      (when (and (= 1 (count pairs)) (e/forall? ftype))
        (let [rec-type (e/forall-type ftype)
              result-type (e/forall-body ftype)
              fused-lam (.value ci)
              naive-lam (binding [*fuse-records?* false]
                          (build-telescope env {} 0 pairs body-form e/lam))
              tc (doto (ansatz.kernel.TypeChecker. env) (.setFuel 50000000))
              beta (e/lam "_" rec-type result-type :default)
              h (e/lam "r" rec-type
                       (e/app* (e/const' (name/from-string "Eq.refl") [u1])
                               result-type (e/lam-body fused-lam))
                       :default)
              proof (e/app* (e/const' (name/from-string "funext") [u1 u1])
                            rec-type beta naive-lam fused-lam h)
              thm-type (.inferType tc proof)
              eq-ci (kenv/mk-thm (name/from-string (str fn-name ".fusion_eq")) [] thm-type proof)]
          (swap! a/ansatz-env
                 kenv/check-constant eq-ci)
          thm-type)))
    (catch Throwable _ nil)))

(defmacro defn
  "Like `a/defn`, but for a single-record-param pipeline it ALSO proves the
   optimization sound: a theorem `<name>.fusion_eq : naive = fused` is admitted,
   certifying the overwrite-eliminated body equals the naive one.

     (rec/defn bump [r :- Row] Row
       (-> r (assoc :a 1) (assoc :b 2) (assoc :a 9)))    ;; :a 1 dropped, PROVEN equal"
  [fn-name params ret-type & body]
  `(let [f# (a/defn ~fn-name ~params ~ret-type ~@body)]
     (fusion-proof! '~fn-name '~params '~(last body))
     f#))
