(ns wandler.causality
  "EXTRINSIC causality, proven in plain CIC — the worked example behind docs/TYPE_THEORY.md.

   The point of the type-theory design note: a property like *causality* of a stream operator (output at
   time t depends only on inputs at times ≤ t) does NOT need a guarded `▷` kernel extension — it is an
   ordinary CIC proposition you can state and prove. We demonstrate on the DBSP delay (z⁻¹):

     Stream.delay_causal : ∀ (s s' : Nat→Int) (t : Nat),
                             (∀ i, i ≤ t → s i = s' i) → Stream.delay s t = Stream.delay s' t

   Proven by `Nat.casesOn t`: at 0 both sides reduce to 0 (rfl); at t'+1 both reduce to `s t'` / `s' t'`,
   and the hypothesis at i = t' (with t' ≤ t'+1) closes it. No modality required.

   This is the lever in the design note: CIC expresses & verifies causality EXTRINSICALLY (as a proved
   side-theorem per operator); guarded type theory would only make it INTRINSIC (true by typing). For
   certifying *generated* operators — which is what Ansatz does — extrinsic dominates, and we keep the
   Lean-4 kernel untouched. See [[programming-model-4-structures]]."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [wandler.dbsp-stream :as ds]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(def ^:private intT (e/const' (nm "Int") [])) (def ^:private natT (e/const' (nm "Nat") []))
(def ^:private strmT (e/forall' "_" natT intT :default))
(def ^:private iZero (e/app* (e/const' (nm "OfNat.ofNat") [z]) intT (e/lit-nat 0)
                             (e/app* (e/const' (nm "instOfNat") []) (e/lit-nat 0))))
(defn- nsucc [t] (e/app (e/const' (nm "Nat.succ") []) t))
(defn- dly [s t] (e/app* (e/const' (nm "Stream.delay") []) s t))
(defn- eqI [x y] (e/app* (e/const' (nm "Eq") [L1]) intT x y))
(defn- natle [i t] (e/app* (e/const' (nm "Nat.le") []) i t))
(defn- reflI [x] (e/app* (e/const' (nm "Eq.refl") [L1]) intT x))

(defn- hyp
  "∀ i, Nat.le i T → Eq Int (s i) (s' i)  — the 'agree up to T' premise (built with i = fvar 5)."
  [s s' T]
  (e/forall' "i" natT
    (e/abstract1 (e/forall' "_" (natle (e/fvar 5) T) (eqI (e/app s (e/fvar 5)) (e/app s' (e/fvar 5))) :default) 5)
    :default))

(defn- prove-delay-causal []
  (let [s (e/fvar 1) s' (e/fvar 2) t (e/fvar 3) t' (e/fvar 4) h (e/fvar 6)
        ;; motive μ = λ T. hyp(s,s',T) → Eq Int (delay s T) (delay s' T)
        mu (e/lam "T" natT (e/abstract1 (e/forall' "h" (hyp s s' t') (eqI (dly s t') (dly s' t')) :default) 4) :default)
        zero-case (e/lam "h" (hyp s s' (e/const' (nm "Nat.zero") [])) (reflI iZero) :default)
        le-proof  (e/app* (e/const' (nm "Nat.le.step") []) t' t' (e/app* (e/const' (nm "Nat.le.refl") []) t'))
        succ-body (e/lam "h" (hyp s s' (nsucc t')) (e/abstract1 (e/app* h t' le-proof) 6) :default)
        succ-case (e/lam "t'" natT (e/abstract1 succ-body 4) :default)
        body (e/app* (e/const' (nm "Nat.casesOn") [z]) mu t zero-case succ-case)
        concl (e/forall' "h" (hyp s s' t) (eqI (dly s t) (dly s' t)) :default)]
    [(-> concl (#(e/forall' "t" natT (e/abstract1 % 3) :default)) (#(e/forall' "s'" strmT (e/abstract1 % 2) :default)) (#(e/forall' "s" strmT (e/abstract1 % 1) :default)))
     (-> body  (#(e/lam "t" natT (e/abstract1 % 3) :default))    (#(e/lam "s'" strmT (e/abstract1 % 2) :default))    (#(e/lam "s" strmT (e/abstract1 % 1) :default)))]))

(defn install!
  "Install the DBSP stream operators (delay/D/I) and prove `Stream.delay_causal` — extrinsic causality of
   z⁻¹ as a kernel theorem. Idempotent."
  []
  (ds/install!)
  (when-not (kenv/lookup (a/env) (nm "Stream.delay_causal"))
    (let [[g p] (prove-delay-causal)]
      (swap! a/ansatz-env kenv/check-constant (kenv/mk-thm (nm "Stream.delay_causal") [] g p))))
  (a/env))
