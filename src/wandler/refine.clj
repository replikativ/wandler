;; Refinement types — reasoning about `Subtype`-refined values.
;;
;; The home for refinement-type logic, consumed by both `wandler.records` (refined
;; record fields) and the optimizer (`wandler.reducers.plan` filter elimination).
;;
;; The central engine, `prove-const`, decides whether a predicate `p : T → Bool` is
;; CONSTANT over `T` — `∀x:T, p x = true` (a filter that always passes — drop it) or
;; `∀x:T, p x = false` (always fails — the pipeline is empty) — with a kernel proof,
;; consumed ONCE at optimization time to delete per-element work.
;;
;; TIERED proof candidates, cheapest first (a non-constant predicate is rejected
;; because the candidate is type-checked against `∀x:T,(p x)=b`):
;;   1. DEFINITIONAL — `fun x => Eq.refl Bool b`, valid when `p x` reduces to `b`
;;      (e.g. `(>= x 0)` over `Nat`).
;;   2. REFINEMENT (direct) — a `Subtype.val` in the predicate carries `.property`
;;      that discharges it directly via `Nat.ble_eq_true_of_le` (`(>= field k)` over
;;      a `[:>= k]` field).
;;   3. OMEGA (general) — materialize the refinement(s) as hypotheses, bridge the
;;      Bool comparison to its Prop (`simp`), and discharge with the `omega` decision
;;      procedure. The systematic path (the way F*/Liquid Haskell discharge
;;      refinements); subsumes 2 and reaches further (always-false, …) as omega's
;;      non-ground proof builder improves.

(ns wandler.refine
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.extract :as extract])
  (:import [ansatz.kernel Env TypeChecker]))

(def ^:private u1 (lvl/succ lvl/zero))
(defn- nm [s] (name/from-string s))
(def ^:private Bool (e/const' (nm "Bool") []))

(defn- bool-const [b] (e/const' (nm (if b "Bool.true" "Bool.false")) []))

(defn- const-prop
  "`∀x:T, (p x) = b` — the proposition that `p` is constantly `b`."
  [p-term elem-type b]
  (e/forall' "x" elem-type
             (e/app* (e/const' (nm "Eq") [u1]) Bool (e/app p-term (e/bvar 0)) (bool-const b))
             :default))

;; ---- proof candidates (tiers) ----

(defn- rfl-proof
  "Tier 1 (definitional): `fun x => Eq.refl Bool b`. Type-checks against
   `∀x:T, (p x) = b` exactly when `(p x)` reduces to `b`."
  [_env _p-term elem-type b]
  (e/lam "x" elem-type
         (e/app* (e/const' (nm "Eq.refl") [u1]) Bool (bool-const b))
         :default))

(defn- subtype-val-parts
  "If `m` is `Subtype.val.{u} α P s`, return {:u :alpha :P :s}; else nil."
  [m]
  (let [[h args] (e/get-app-fn-args m)]
    (when (and (e/const? h) (= "Subtype.val" (name/->string (e/const-name h))) (= 3 (count args)))
      {:u (first (e/const-levels h)) :alpha (nth args 0) :P (nth args 1) :s (nth args 2)})))

(defn- find-subtype-val
  "The first `Subtype.val.{u} α P s` subterm ANYWHERE in `e`, or nil. The refinement may be
   read through a transparent wrapper — e.g. the string-length check `Nat.ble k (String.length
   (val x))` nests the val under `String.length` — so search recursively, not just direct args."
  [e]
  (cond
    (subtype-val-parts e) e
    (e/app? e) (or (find-subtype-val (e/app-fn e)) (find-subtype-val (e/app-arg e)))
    (e/lam? e) (find-subtype-val (e/lam-body e))
    (e/forall? e) (or (find-subtype-val (e/forall-type e)) (find-subtype-val (e/forall-body e)))
    :else nil))

(defn- subtype-property-proof
  "Tier 3 (refinement subtyping). PREDICATE-DRIVEN: if the predicate is
   `Nat.ble k m` and `m` reads a refinement (`m = Subtype.val α P s`), the carried
   `.property = Subtype.property α P s : P (val …)` discharges it via
   `Nat.ble_eq_true_of_le`. Handles both a refined ELEMENT (`s` = the param) and a
   refined record FIELD (`s` = a projection off the param) — the always-true case
   Tier 1 can't prove (`k ≤ v` is not definitional)."
  [_env p-term elem-type b]
  (when b
    (let [[h args] (e/get-app-fn-args (e/lam-body p-term))]    ; predicate body over x=bvar0
      (when (and (e/const? h) (= "Nat.ble" (name/->string (e/const-name h))) (= 2 (count args)))
        ;; `m` (the 2nd arg) reads a refinement: either the val directly (refined Nat
        ;; element/field, `k ≤ val s`) OR through a transparent wrapper — `String.length
        ;; (val s)` for a malli string-length refinement `{s // k ≤ s.length}`, where the
        ;; property IS `k ≤ s.length = k ≤ m`. find-subtype-val reaches the val while `m`
        ;; stays opaque, so the proof is a cheap SYNTACTIC discharge (no omega/reduction).
        (when-let [sv (find-subtype-val (nth args 1))]
          (let [{:keys [u alpha P s]} (subtype-val-parts sv)]
            (e/lam "x" elem-type
                   (e/app* (e/const' (nm "Nat.ble_eq_true_of_le") [])
                           (nth args 0)                                      ; k
                           (nth args 1)                                      ; m (= val s, or length (val s))
                           (e/app* (e/const' (nm "Subtype.property") [u]) alpha P s))
                   :default)))))))

(defn- subtype-negation-proof
  "Always-FALSE via refinement: predicate `Nat.blt (val s) k` where `s` carries a
   lower-bound refinement `k ≤ val s` — the filter `val s < k` CONTRADICTS the type,
   so it is always false. Proof chain: `.property → ¬(v<k) (Nat.not_lt) → ¬(blt=true)
   (Nat.blt_eq) → blt=false (Bool.not_eq_true)`. Nat-specific."
  [_env p-term elem-type b]
  (when (not b)
    (let [[h args] (e/get-app-fn-args (e/lam-body p-term))]
      (when (and (e/const? h) (= "Nat.blt" (name/->string (e/const-name h))) (= 2 (count args)))
        (when-let [{:keys [u alpha P s]} (subtype-val-parts (nth args 0))]
          (let [v0 (nth args 0) k0 (nth args 1)
                v1 (e/lift v0 1 0) s1 (e/lift s 1 0) k1 (e/lift k0 1 0)
                u0 lvl/zero
                C (fn [n ls] (e/const' (nm n) (or ls [])))
                lt (fn [vv kk] (e/app* (C "LT.lt" [u0]) alpha (C "instLTNat" nil) vv kk))
                le (fn [vv kk] (e/app* (C "LE.le" [u0]) alpha (C "instLENat" nil) kk vv))
                blt (fn [vv kk] (e/app* (C "Nat.blt" nil) vv kk))
                NOT (fn [p] (e/app (C "Not" nil) p))
                blt-true (fn [vv kk] (e/app* (C "Eq" [u1]) Bool (blt vv kk) (C "Bool.true" nil)))
                prop (fn [src] (e/app* (C "Subtype.property" [u]) alpha P src))
                not-lt (fn [vv kk src] (e/app* (C "Iff.mpr" nil) (NOT (lt vv kk)) (le vv kk)
                                               (e/app* (C "Nat.not_lt" nil) vv kk) (prop src)))
                not-blt (e/lam "hb" (blt-true v0 k0)
                               (e/app (not-lt v1 k1 s1)
                                      (e/app* (C "Eq.mp" [u0]) (blt-true v1 k1) (lt v1 k1)
                                              (e/app* (C "Nat.blt_eq" nil) v1 k1) (e/bvar 0)))
                               :default)]
            (e/lam "x" elem-type
                   (e/app* (C "Eq.mp" [u0]) (NOT (blt-true v0 k0))
                           (e/app* (C "Eq" [u1]) Bool (blt v0 k0) (C "Bool.false" nil))
                           (e/app* (C "Bool.not_eq_true" nil) (blt v0 k0)) not-blt)
                   :default)))))))

(defn- omega-proof
  "Tier 3 (general): discharge via the omega decision procedure. Builds the goal
   `∀x:T, p x = b`, intros x, MATERIALIZES the predicate's refinement (`s.property`)
   as a hypothesis, bridges the Bool comparison to its Prop (`simp [Nat.ble_eq …]`),
   and closes with `omega` (which uses the materialized refinement). Returns the
   extracted proof term, or nil. This is the systematic refinement-discharge path —
   it reaches cases the direct bridge can't as omega's proof builder grows."
  [^Env env p-term elem-type b]
  (try
    (let [goal (const-prop p-term elem-type b)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["x"])
          g (proof/current-goal ps)
          xf (e/fvar (some (fn [[id d]] (when (= "x" (:name d)) id)) (:lctx g)))
          body (e/instantiate1 (e/lam-body p-term) xf)   ; predicate body with x := xf
          [_ pargs] (e/get-app-fn-args body)
          sv-arg (some #(when (subtype-val-parts %) %) pargs)  ; the Subtype.val operand
          sv (when sv-arg (subtype-val-parts sv-arg))
          ps (if sv
               ;; have h := s.property  (the refinement, e.g. k ≤ val s)
               (-> ps
                   (basic/have-tac "h" (e/app (:P sv) sv-arg))
                   (basic/apply-tac (e/app* (e/const' (nm "Subtype.property") [(:u sv)])
                                            (:alpha sv) (:P sv) (:s sv))))
               ps)
          ps (try (simp/simp ps ['Nat.ble_eq 'Nat.blt_eq]) (catch Throwable _ ps))
          ps (omega/omega ps)]
      (when (proof/solved? ps) (extract/extract ps)))
    (catch Throwable _ nil)))

(def ^:private proof-candidates
  "Ordered proof builders `(env p-term elem-type b) → proof | nil`, cheapest first:
   definitional `rfl`, the direct Subtype `.property` bridge, then the general
   `omega` discharge."
  [rfl-proof subtype-property-proof subtype-negation-proof omega-proof])

(defn- try-value [^Env env p-term elem-type b]
  (let [prop (const-prop p-term elem-type b)
        tc (doto (TypeChecker. env) (.setFuel 50000000))]
    (some (fn [mk]
            (when-let [proof (mk env p-term elem-type b)]
              ;; STRICT .check (not lenient inferType): only ACCEPT a candidate whose
              ;; proof genuinely type-checks — so refine picks a real proof, and a later
              ;; a/defn admission (check-constant) never rejects a candidate we "verified".
              (try (when (.isDefEq tc (.check tc proof) prop)
                     {:value b :proof proof :theorem-type prop})
                   (catch Throwable _ nil))))
          proof-candidates)))

(defn prove-const
  "If predicate `p-term` (a kernel `T → Bool`) is provably constant over `elem-type`,
   return {:value bool :proof term :theorem-type (∀x:T,(p x)=value)}; else nil."
  [^Env env p-term elem-type]
  (or (try-value env p-term elem-type true)
      (try-value env p-term elem-type false)))

(defn prove-monotone
  "Prove the CLOSED obligation `∀w:base, (P w) → (P (apply-f w))` — that applying the
   update function preserves the refinement `P`. `apply-f` builds the kernel
   application of the update fn to a value term. Returns the proof term, or nil if
   not provable (a non-monotone update fn is correctly rejected). Discharged by
   omega, so it covers `inc`/`+k`-style writes (`18 <= succ age` from `18 <= age`).
   The returned proof is instantiated at the write site with the field value and its
   carried `.property`."
  [^Env env base P apply-f]
  (try
    (let [pbody (e/lam-body P)                                  ; P = fun v => <pbody[v]>
          goal (e/forall' "w" base
                          (e/forall' "hw" (e/instantiate1 pbody (e/bvar 0))      ; hyp: P w (β-reduced)
                                     (e/instantiate1 pbody (apply-f (e/bvar 1)))  ; goal: P (f w)
                                     :default)
                          :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["w" "hw"])
          ps (omega/omega ps)]
      (when (proof/solved? ps) (extract/extract ps)))
    (catch Throwable _ nil)))
