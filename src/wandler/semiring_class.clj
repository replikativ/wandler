(ns wandler.semiring-class
  "Bundled-axiom algebra typeclasses over ansatz's `a/structure :extends` (the Lean-4 subobject
   model — see ansatz/docs/EXTENDS_DESIGN.md), plus verified instances auto-derived from the
   carrier registry (`wandler.laws.semiring`).

   This is the L4 typeclass front door: instead of threading the 6 algebra axioms
   (hAA/hZA/hAZ/hMA/hMZ/hZM) as bare hypotheses, a generic law can take ONE `[s : WSemiring S]`
   instance argument and project what it needs; instance synthesis resolves a carrier's
   `WAddMonoid S` from its `WSemiring S` via the `WSemiring.toWAddMonoid` subobject coercion.

   The class hierarchy mirrors the two carriers the frame-family laws use:
     WAddMonoid S = { add, zero, add_assoc, zero_add, add_zero }          -- the aggregation monoid
     WSemiring  S extends WAddMonoid + { mul, mul_add, mul_zero, zero_mul } -- + left-distributive product

   Note the fragment is non-unital, non-commutative, left-distributive (exactly what the laws need —
   no `one`, no mul-assoc, no add-comm), leaner than Mathlib's `Semiring`.

   An instance is built straight from a registry row: the row's {:add :mul :zero + axiom-proof names}
   ARE the constructor arguments, so there is no duplication — the same Init/Mathlib lemmas that the
   `_generic` law emitter instantiates also construct the instance, and the kernel checks the proofs
   line up (e.g. `mul_add`'s `add` reduces through the subobject projection to the carrier's `add`)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [wandler.laws.semiring :as sreg]))

(defn- kconst [s] (e/const' (nm/from-string s) []))
(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn classes-installed? []
  (and (has? "WAddMonoid") (has? "WSemiring")))

(defn install-classes!
  "Define WAddMonoid ⊂ WSemiring (idempotent). Requires an initialised ansatz env (a/init!/load-init!)."
  []
  (when-not (classes-installed?)
    (eval '(ansatz.core/structure WAddMonoid [S Type]
             (add (=> S S S)) (zero S)
             (add_assoc (forall [a S b S c S] (= S (add (add a b) c) (add a (add b c)))))
             (zero_add (forall [a S] (= S (add zero a) a)))
             (add_zero (forall [a S] (= S (add a zero) a)))))
    (eval '(ansatz.core/structure WSemiring [S Type] :extends (WAddMonoid S)
             (mul (=> S S S))
             (mul_add (forall [a S b S c S] (= S (mul a (add b c)) (add (mul a b) (mul a c)))))
             (mul_zero (forall [a S] (= S (mul a zero) zero)))
             (zero_mul (forall [a S] (= S (mul zero a) zero))))))
  :installed)

(defn instance-names
  "The canonical instance const names for a carrier (e.g. \"Nat\")."
  [carrier]
  {:addmonoid (str "instWAddMonoid_" carrier)
   :semiring  (str "instWSemiring_" carrier)})

(defn build-instance!
  "Build and KERNEL-VERIFY the WAddMonoid and WSemiring instances for `carrier` (a kernel const
   name) from registry `row` {:add :mul :zero :hAA :hZA :hAZ :hMA :hMZ :hZM}. Adds both defs to the
   env (so the child can reference the parent instance). Returns a status map; on any missing lemma
   or proof mismatch the kernel rejects it and we report :failed without mutating further."
  [carrier row]
  (let [{am-name :addmonoid ws-name :semiring} (instance-names carrier)
        S (kconst carrier)]
    (try
      (when-not (classes-installed?)
        (throw (ex-info "classes not installed; call install-classes! first" {})))
      ;; parent: WAddMonoid.mk S add zero add_assoc zero_add add_zero
      (let [am-ty   (e/app (kconst "WAddMonoid") S)
            am-inst (e/app* (kconst "WAddMonoid.mk") S
                            (kconst (:add row)) (kconst (:zero row))
                            (kconst (:hAA row)) (kconst (:hZA row)) (kconst (:hAZ row)))]
        (reset! a/ansatz-env
                (env/check-constant (a/env) (env/mk-def (nm/from-string am-name) [] am-ty am-inst))))
      ;; child: WSemiring.mk S <parent-inst> mul mul_add mul_zero zero_mul
      (let [ws-ty   (e/app (kconst "WSemiring") S)
            ws-inst (e/app* (kconst "WSemiring.mk") S (kconst am-name)
                            (kconst (:mul row)) (kconst (:hMA row)) (kconst (:hMZ row)) (kconst (:hZM row)))]
        (reset! a/ansatz-env
                (env/check-constant (a/env) (env/mk-def (nm/from-string ws-name) [] ws-ty ws-inst))))
      {:carrier carrier :status :verified :addmonoid am-name :semiring ws-name}
      (catch Exception ex
        {:carrier carrier :status :failed :error (.getMessage ex)}))))

(defn install-from-registry!
  "Install the classes, then build+verify a WSemiring instance for every carrier currently in the
   `wandler.laws.semiring` registry. Returns {carrier → status-map}. Carriers whose axiom lemmas
   are absent from the loaded store simply report :failed (graceful — the kernel gate can't be
   fooled). Populate the registry first by requiring wandler.laws.relational / .tropical."
  []
  (install-classes!)
  (into {} (for [c (sreg/registered)]
             [c (build-instance! c (sreg/entry (kconst c)))])))

(defn instance-term
  "The kernel const term for a carrier's installed WSemiring instance, or nil if not installed."
  [carrier]
  (let [n (:semiring (instance-names carrier))]
    (when (has? n) (kconst n))))

;; ── Inline instance TERMS (built straight from a registry row, no env mutation) ──────────────
;; These are what the migrated laws' application sites pass instead of 6 bare consts. The kernel
;; checks the term when it checks the law application, so a bad row simply fails to typecheck.

(defn mk-addmonoid-instance
  "WAddMonoid.mk S add zero add_assoc zero_add add_zero — a `WAddMonoid S` term from a registry row.
   `S` is a kernel const term (e.g. (kconst \"Nat\"))."
  [S row]
  (e/app* (kconst "WAddMonoid.mk") S
          (kconst (:add row)) (kconst (:zero row))
          (kconst (:hAA row)) (kconst (:hZA row)) (kconst (:hAZ row))))

(defn mk-semiring-instance
  "WSemiring.mk S <WAddMonoid inst> mul mul_add mul_zero zero_mul — a `WSemiring S` term from a row.
   The parent WAddMonoid instance is built inline (compositional, like Lean's subobject ctor)."
  [S row]
  (e/app* (kconst "WSemiring.mk") S
          (mk-addmonoid-instance S row)
          (kconst (:mul row)) (kconst (:hMA row)) (kconst (:hMZ row)) (kconst (:hZM row))))
