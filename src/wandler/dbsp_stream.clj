(ns wandler.dbsp-stream
  "The DBSP STREAM-OPERATOR algebra (rung 3) — the layer beneath the value-level incremental relational
   algebra (wandler.dbsp). A stream is `Nat → Int` (an abelian group over time). The three fundamental
   operators (DBSP §3.5, operators.lean / linear.lean):

     delay (z⁻¹) : (z⁻¹ s) t = if t=0 then 0 else s(t-1)           — shift by one
     D (differentiate) : (D s) t = s t − s(t−1)                    — stream of changes
     I (integrate)     : (I s) t = Σ_{i≤t} s i  (running sum)      — cumulative

   and `incremental Q := D ∘ Q ∘ I` (the incremental version of a stream operator, `Q^Δ`).

   The load-bearing facts (the fundamental theorem of the discrete calculus, both check-constant'd):
     Stream.D_I : D (I s) = s     (D∘I = id)
     Stream.I_D : I (D s) = s     (I∘D = id, by telescoping)
   from which the CHAIN RULE follows — the general composition theorem (DBSP Prop 5.2):
     Stream.incremental_comp : (Q1∘Q2)^Δ = Q1^Δ ∘ Q2^Δ
   This is what makes incrementalization MODULAR/syntactic (incrementalize any pipeline by
   incrementalizing its parts) and is the infrastructure under which non-linear operators like
   `distinct` get their increment `Q^Δ = D∘Q∘I`. Grounded in ../dbsp-theory (the paper's Lean proofs).

   Streams here are `Nat → Int` over a fixed Int; the general abelian-group version (and the codegen of
   the operators) is future work — this establishes the algebra."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(def ^:private intT (e/const' (nm "Int") []))
(def ^:private natT (e/const' (nm "Nat") []))
(def ^:private streamT (e/forall' "_" natT intT :default))      ; a stream = Nat → Int
(def ^:private streamArrow (e/forall' "_" streamT streamT :default))
(def ^:private iZero (e/app* (e/const' (nm "OfNat.ofNat") [z]) intT (e/lit-nat 0) (e/app* (e/const' (nm "instOfNat") []) (e/lit-nat 0))))
(defn- iAdd [a b] (e/app* (e/const' (nm "Int.add") []) a b))
(defn- iSub [a b] (e/app* (e/const' (nm "Int.sub") []) a b))
(defn- nzero [] (e/const' (nm "Nat.zero") []))
(defn- nsucc [t] (e/app (e/const' (nm "Nat.succ") []) t))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- eqI [x y] (e/app* (e/const' (nm "Eq") [L1]) intT x y))
(defn- trI [x y w h1 h2] (e/app* (e/const' (nm "Eq.trans") [L1]) intT x y w h1 h2))
(defn- cgI [a1 a2 f h] (e/app* (e/const' (nm "congrArg") [L1 L1]) intT intT a1 a2 f h))
(defn- dD  [s t] (e/app* (e/const' (nm "Stream.D") []) s t))
(defn- iI  [s t] (e/app* (e/const' (nm "Stream.I") []) s t))
(defn- dly [s t] (e/app* (e/const' (nm "Stream.delay") []) s t))

(defn- op-defs
  "The ConstantInfos for Stream.delay (z⁻¹), Stream.D, Stream.I."
  []
  (let [s (e/fvar 1) t (e/fvar 2)
        mkdef (fn [name body] (kenv/mk-def (nm name) []
                (-> intT (#(e/forall' "t" natT % :default)) (#(e/forall' "s" streamT % :default)))
                (-> body (#(e/lam "t" natT (e/abstract1 % 2) :default)) (#(e/lam "s" streamT (e/abstract1 % 1) :default)))))
        delay-body (e/app* (e/const' (nm "Nat.casesOn") [L1]) (e/lam "_" natT intT :default) t iZero
                           (e/lam "t'" natT (e/app s (e/bvar 0)) :default))
        I-body (e/app* (e/const' (nm "Nat.rec") [L1]) (e/lam "_" natT intT :default)
                       (e/app s (nzero))
                       (e/lam "t'" natT (e/lam "acc" intT (iAdd (e/bvar 0) (e/app s (nsucc (e/bvar 1)))) :default) :default)
                       t)
        D-body (iSub (e/app s t) (dly s t))]
    [(mkdef "Stream.delay" delay-body) (mkdef "Stream.I" I-body) (mkdef "Stream.D" D-body)]))

(defn- incr-def []
  (let [Q (e/fvar 1) s (e/fvar 2) t (e/fvar 3)
        body (e/app* (e/const' (nm "Stream.D") []) (e/app Q (e/app* (e/const' (nm "Stream.I") []) s)) t)]
    (kenv/mk-def (nm "Stream.incremental") []
      (-> intT (#(e/forall' "t" natT % :default)) (#(e/forall' "s" streamT % :default)) (#(e/forall' "Q" streamArrow % :default)))
      (-> body (#(e/lam "t" natT (e/abstract1 % 3) :default)) (#(e/lam "s" streamT (e/abstract1 % 2) :default))
               (#(e/lam "Q" streamArrow (e/abstract1 % 1) :default))))))

;; Stream.D_I : D (I s) t = s t  (D∘I = id). Nat.casesOn t: 0 → s 0 − 0 = s 0; succ t' → (a+b)−a = b.
(defn prove-D-I []
  (let [s (e/fvar 1) t (e/fvar 2)
        mu (e/lam "t" natT (eqI (dD (e/app* (e/const' (nm "Stream.I") []) s) (e/bvar 0)) (e/app s (e/bvar 0))) :default)
        Is (e/app* (e/const' (nm "Stream.I") []) s)
        zeroPf (e/app* (e/const' (nm "Int.sub_zero") []) (e/app s (nzero)))
        succLam (let [t' (e/fvar 3) a (iI s t') b (e/app s (nsucc t'))
                      body (trI (iSub (iAdd a b) a) (iSub (iAdd b a) a) b
                                (cgI (iAdd a b) (iAdd b a) (e/lam "w" intT (iSub (e/bvar 0) a) :default)
                                     (e/app* (e/const' (nm "Int.add_comm") []) a b))
                                (e/app* (e/const' (nm "Int.add_sub_cancel") []) b a))]
                  (e/lam "t'" natT (e/abstract1 body 3) :default))
        body (e/app* (e/const' (nm "Nat.casesOn") [z]) mu t zeroPf succLam)
        proof (-> body (#(e/lam "t" natT (e/abstract1 % 2) :default)) (#(e/lam "s" streamT (e/abstract1 % 1) :default)))
        goal (-> (eqI (dD Is t) (e/app s t))
                 (#(e/forall' "t" natT (e/abstract1 % 2) :default)) (#(e/forall' "s" streamT (e/abstract1 % 1) :default)))]
    [goal proof]))

;; Stream.I_D : I (D s) t = s t  (I∘D = id, telescoping). Induction on t.
(defn prove-I-D []
  (let [s (e/fvar 1) t (e/fvar 2)
        goal (-> (eqI (iI (e/app* (e/const' (nm "Stream.D") []) s) t) (e/app s t))
                 (#(e/forall' "t" natT (e/abstract1 % 2) :default)) (#(e/forall' "s" streamT (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["s" "t"])
        ps (basic/induction ps (fvid ps "t"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid) cg (proof/current-goal psg)
                    ihnm (some (fn [[_ d]] (when (clojure.string/starts-with? (str (:name d)) "ih") (:name d))) (:lctx cg))]
                (if ihnm
                  (let [s (gf psg "s") ih (gf psg ihnm)
                        tp (some (fn [[id d]] (when (and (not= (:name d) ihnm) (= "Nat" (e/->string (:type d)))) id)) (:lctx cg))
                        t' (e/fvar tp) Ds (e/app* (e/const' (nm "Stream.D") []) s)
                        a (e/app s t') b (e/app s (nsucc t')) ihLHS (iI Ds t')
                        step1 (cgI ihLHS a (e/lam "w" intT (iAdd (e/bvar 0) (iSub b a)) :default) ih)
                        step2 (trI (iAdd a (iSub b a)) (iAdd (iSub b a) a) b
                                   (e/app* (e/const' (nm "Int.add_comm") []) a (iSub b a))
                                   (e/app* (e/const' (nm "Int.sub_add_cancel") []) b a))
                        result (trI (iAdd ihLHS (iSub b a)) (iAdd a (iSub b a)) b step1 step2)]
                    (basic/exact psg result))
                  (basic/exact psg (e/app* (e/const' (nm "Int.sub_zero") []) (e/app (gf psg "s") (nzero)))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Stream.incremental_comp : (Q1∘Q2)^Δ = Q1^Δ ∘ Q2^Δ  (chain rule, Prop 5.2). Rests on I∘D=id + funext.
(defn prove-incr-comp []
  (let [Q1 (e/fvar 1) Q2 (e/fvar 2) s (e/fvar 3) t (e/fvar 4)
        compQ (e/lam "x" streamT (e/app Q1 (e/app Q2 (e/bvar 0))) :default)
        Is (e/app* (e/const' (nm "Stream.I") []) s)
        u  (e/app Q2 Is)
        Du (e/app* (e/const' (nm "Stream.D") []) u)
        IDu (e/app* (e/const' (nm "Stream.I") []) Du)
        funextEq (e/app* (e/const' (nm "funext") [L1 L1]) natT (e/lam "_" natT intT :default)
                         IDu u (e/app* (e/const' (nm "Stream.I_D") []) u))
        congrFn (e/lam "w" streamT (e/app* (e/const' (nm "Stream.D") []) (e/app Q1 (e/bvar 0)) t) :default)
        cg (e/app* (e/const' (nm "congrArg") [L1 L1]) streamT intT IDu u congrFn funextEq)
        incrA (fn [Q ss tt] (e/app* (e/const' (nm "Stream.incremental") []) Q ss tt))
        incrL (incrA compQ s t)
        incrR (incrA Q1 (e/app* (e/const' (nm "Stream.incremental") []) Q2 s) t)
        proof (e/app* (e/const' (nm "Eq.symm") [L1]) intT incrR incrL cg)
        goal (-> (eqI incrL incrR)
                 (#(e/forall' "t" natT (e/abstract1 % 4) :default))
                 (#(e/forall' "s" streamT (e/abstract1 % 3) :default))
                 (#(e/forall' "Q2" streamArrow (e/abstract1 % 2) :default))
                 (#(e/forall' "Q1" streamArrow (e/abstract1 % 1) :default)))
        pf (-> proof
               (#(e/lam "t" natT (e/abstract1 % 4) :default))
               (#(e/lam "s" streamT (e/abstract1 % 3) :default))
               (#(e/lam "Q2" streamArrow (e/abstract1 % 2) :default))
               (#(e/lam "Q1" streamArrow (e/abstract1 % 1) :default)))]
    [goal pf]))

;; Stream.incremental_linear (DBSP Theorem 5.4): a LINEAR (over −) + TIME-INVARIANT operator is its own
;; incremental version — Q^Δ = Q. This is THE bridge to the value-level relational algebra: it is *why*
;; the increment of a linear operator (filter/map/projection) is just the operator applied to the delta.
;;   Proof (the paper's): Q^Δ s = D(Q(I s)) = Q(D(I s)) [D commutes with Q] = Q s [D∘I=id]. D commutes
;;   with Q because  D(Q u) = Q u − z⁻¹(Q u) = Q u − Q(z⁻¹ u) [TI] = Q(u − z⁻¹ u) [linear] = Q(D u).
(defn- ssub [a b] (e/lam "t" natT (iSub (e/app a (e/bvar 0)) (e/app b (e/bvar 0))) :default))
(defn- dlyS [s] (e/app* (e/const' (nm "Stream.delay") []) s))
(defn- DS [s] (e/app* (e/const' (nm "Stream.D") []) s))
(defn- IS [s] (e/app* (e/const' (nm "Stream.I") []) s))
(defn- incrAt [Q s t] (e/app* (e/const' (nm "Stream.incremental") []) Q s t))
(defn- eqS [x y] (e/app* (e/const' (nm "Eq") [L1]) streamT x y))
(defn- symS [x y h] (e/app* (e/const' (nm "Eq.symm") [L1]) streamT x y h))
(defn- symI [x y h] (e/app* (e/const' (nm "Eq.symm") [L1]) intT x y h))
(defn- atT [t h fA gA] (e/app* (e/const' (nm "congrArg") [L1 L1]) streamT intT fA gA
                               (e/lam "f" streamT (e/app (e/bvar 0) t) :default) h))
(defn- congrQ [Q a b h] (e/app* (e/const' (nm "congrArg") [L1 L1]) streamT streamT a b Q h))
(defn- funextS [f g h] (e/app* (e/const' (nm "funext") [L1 L1]) natT (e/lam "_" natT intT :default) f g h))

(defn prove-incr-linear []
  (let [Q (e/fvar 1) a (e/fvar 10) b (e/fvar 11) sp (e/fvar 12)
        hlinType (-> (eqS (e/app Q (ssub a b)) (ssub (e/app Q a) (e/app Q b)))
                     (#(e/forall' "b" streamT (e/abstract1 % 11) :default))
                     (#(e/forall' "a" streamT (e/abstract1 % 10) :default)))
        htiType (-> (eqS (e/app Q (dlyS sp)) (dlyS (e/app Q sp)))
                    (#(e/forall' "s" streamT (e/abstract1 % 12) :default)))
        s (e/fvar 4) t (e/fvar 5)
        goal (-> (eqI (incrAt Q s t) (e/app (e/app Q s) t))
                 (#(e/forall' "t" natT (e/abstract1 % 5) :default))
                 (#(e/forall' "s" streamT (e/abstract1 % 4) :default))
                 (#(e/forall' "hti" htiType % :default))
                 (#(e/forall' "hlin" hlinType % :default))
                 (#(e/forall' "Q" streamArrow (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["Q" "hlin" "hti" "s" "t"])
        Q (gf ps "Q") hlin (gf ps "hlin") hti (gf ps "hti") s (gf ps "s") t (gf ps "t")
        u (IS s) Qu (e/app Q u) QuT (e/app Qu t)
        eT (atT t (symS (e/app Q (dlyS u)) (dlyS Qu) (e/app hti u)) (dlyS Qu) (e/app Q (dlyS u)))
        eL (atT t (e/app* hlin u (dlyS u)) (e/app Q (ssub u (dlyS u))) (ssub Qu (e/app Q (dlyS u))))
        m0 (e/app (DS Qu) t) m1 (iSub QuT (e/app (e/app Q (dlyS u)) t)) m2 (e/app (e/app Q (DS u)) t)
        stepA (e/app* (e/const' (nm "congrArg") [L1 L1]) intT intT
                      (e/app (dlyS Qu) t) (e/app (e/app Q (dlyS u)) t)
                      (e/lam "w" intT (iSub QuT (e/bvar 0)) :default) eT)
        eLlhs (e/app (e/app Q (ssub u (dlyS u))) t) eLrhs (e/app (ssub Qu (e/app Q (dlyS u))) t)
        Dcomm (trI m0 m1 m2 stepA (symI eLlhs eLrhs eL))
        DIeq (funextS (DS u) s (e/app* (e/const' (nm "Stream.D_I") []) s))
        ee2 (atT t (congrQ Q (DS u) s DIeq) (e/app Q (DS u)) (e/app Q s))
        ps (basic/exact ps (trI (incrAt Q s t) m2 (e/app (e/app Q s) t) Dcomm ee2))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defonce ^:private cache (atom nil))

(defn install!
  "Admit the stream-operator algebra (delay/D/I/incremental + D_I/I_D/incremental_comp) into the
   global env (idempotent). The chain rule then certifies modular incrementalization."
  []
  (when-not (kenv/lookup (a/env) (nm "Stream.incremental_linear"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      ;; register defs FIRST (the proofs typecheck against them), then build+register each proof.
      (let [reg! (fn [ci] (swap! a/ansatz-env kenv/check-constant ci) ci)
            thm! (fn [n pf] (reg! (let [[g p] (pf)] (kenv/mk-thm (nm n) [] g p))))
            defs (mapv reg! (op-defs))
            incd (reg! (incr-def))
            d-i  (thm! "Stream.D_I" prove-D-I)
            i-d  (thm! "Stream.I_D" prove-I-D)
            ic   (thm! "Stream.incremental_comp" prove-incr-comp)
            il   (thm! "Stream.incremental_linear" prove-incr-linear)]
        (reset! cache (vec (concat defs [incd d-i i-d ic il]))))))
  (a/env))
