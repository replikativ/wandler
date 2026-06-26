(ns wandler.exec.dbsp-group
  "The DBSP differential calculus, generalized OFF `Int` to an ABSTRACT ABELIAN GROUP — step 2 of the
   comonad/∂ debt (PROGRAMMING_MODEL.md §13, the audit's \"S2 ∂ uses only the abelian-group axioms\").

   `wandler.exec.dbsp-stream` proves `D∘I = id` / `I∘D = id` for streams `Nat → Int`, using exactly four `Int`
   lemmas: `sub_zero`, `add_comm`, `add_sub_cancel`, `sub_add_cancel` — the abelian-group axioms. Here we
   make that genericity a KERNEL THEOREM: generic `Stream.Igen`/`Stream.Dgen` over any carrier `G` + ops,
   and `Stream.D_I_gen`/`Stream.I_D_gen` taking the four group laws as HYPOTHESES. `Int` is then recovered
   as a CERTIFIED INSTANCE (`Stream.D_I_int`/`Stream.I_D_int`, check-constant'd) — proving the differential
   calculus depends on nothing Int-specific, only the group structure. Init-only (no Mathlib AddCommGroup).

   This closes the ∂-generalization; the deeper guarded/comonadic `Strm` (a non-global clock) remains the
   open part of the debt. See dbsp-stream-operator-algebra, programming-model-4-structures."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(def ^:private TypeT (e/sort' L1))                  ; Type 0 = Sort 1
(def ^:private natT (e/const' (nm "Nat") []))
(def ^:private intT (e/const' (nm "Int") []))
(def ^:private iZero (e/app* (e/const' (nm "OfNat.ofNat") [z]) intT (e/lit-nat 0)
                             (e/app* (e/const' (nm "instOfNat") []) (e/lit-nat 0))))
(defn- nzero [] (e/const' (nm "Nat.zero") []))
(defn- nsucc [t] (e/app (e/const' (nm "Nat.succ") []) t))
(defn- eqG [G x y] (e/app* (e/const' (nm "Eq") [L1]) G x y))
(defn- trG [G x y w h1 h2] (e/app* (e/const' (nm "Eq.trans") [L1]) G x y w h1 h2))
(defn- cgG [G a1 a2 f h] (e/app* (e/const' (nm "congrArg") [L1 L1]) G G a1 a2 f h))

;; ── generic Igen (running sum) / Dgen (difference) over an abstract carrier G ─────────────────────
(defn- mk-Igen []
  ;; Stream.Igen : ∀ (G:Type)(add:G→G→G)(s:Nat→G)(t:Nat), G  := Nat.rec (s 0) (λt' acc. add acc (s (succ t'))) t
  (let [G (e/fvar 1) add (e/fvar 2) s (e/fvar 3) t (e/fvar 4)
        GG (e/forall' "_" G G :default) addT (e/forall' "_" G GG :default) sT (e/forall' "_" natT G :default)
        motive (e/lam "_" natT G :default)
        step (e/lam "n" natT (e/lam "acc" G (e/app* add (e/bvar 0) (e/app s (nsucc (e/bvar 1)))) :default) :default)
        body (e/app* (e/const' (nm "Nat.rec") [L1]) motive (e/app s (nzero)) step t)
        ty (-> G (#(e/forall' "t" natT (e/abstract1 % 4) :default)) (#(e/forall' "s" sT (e/abstract1 % 3) :default))
                 (#(e/forall' "add" addT (e/abstract1 % 2) :default)) (#(e/forall' "G" TypeT (e/abstract1 % 1) :default)))
        pf (-> body (#(e/lam "t" natT (e/abstract1 % 4) :default)) (#(e/lam "s" sT (e/abstract1 % 3) :default))
                    (#(e/lam "add" addT (e/abstract1 % 2) :default)) (#(e/lam "G" TypeT (e/abstract1 % 1) :default)))]
    (kenv/mk-def (nm "Stream.Igen") [] ty pf)))

(defn- mk-Dgen []
  ;; Stream.Dgen : ∀ (G:Type)(zero:G)(sub:G→G→G)(s:Nat→G)(t:Nat), G  := sub (s t) (casesOn t zero (λt'. s t'))
  (let [G (e/fvar 1) zr (e/fvar 2) sub (e/fvar 3) s (e/fvar 4) t (e/fvar 5)
        GG (e/forall' "_" G G :default) subT (e/forall' "_" G GG :default) sT (e/forall' "_" natT G :default)
        delay (e/app* (e/const' (nm "Nat.casesOn") [L1]) (e/lam "_" natT G :default) t zr (e/lam "t'" natT (e/app s (e/bvar 0)) :default))
        body (e/app* sub (e/app s t) delay)
        ty (-> G (#(e/forall' "t" natT (e/abstract1 % 5) :default)) (#(e/forall' "s" sT (e/abstract1 % 4) :default))
                 (#(e/forall' "sub" subT (e/abstract1 % 3) :default)) (#(e/forall' "zero" G (e/abstract1 % 2) :default))
                 (#(e/forall' "G" TypeT (e/abstract1 % 1) :default)))
        pf (-> body (#(e/lam "t" natT (e/abstract1 % 5) :default)) (#(e/lam "s" sT (e/abstract1 % 4) :default))
                    (#(e/lam "sub" subT (e/abstract1 % 3) :default)) (#(e/lam "zero" G (e/abstract1 % 2) :default))
                    (#(e/lam "G" TypeT (e/abstract1 % 1) :default)))]
    (kenv/mk-def (nm "Stream.Dgen") [] ty pf)))

;; ── Stream.D_I_gen : D∘I = id over any abelian group (sub_zero + add_comm + add_sub_cancel) ────────
(defn- prove-D-I-gen []
  (let [G (e/fvar 1) zr (e/fvar 2) add (e/fvar 3) sub (e/fvar 4) sz (e/fvar 5) ac (e/fvar 6) asc (e/fvar 7) s (e/fvar 8) t (e/fvar 9) t' (e/fvar 10)
        GG (e/forall' "_" G G :default) addT (e/forall' "_" G GG :default) subT (e/forall' "_" G GG :default) sT (e/forall' "_" natT G :default)
        a (e/fvar 21) b (e/fvar 22)
        szT  (e/forall' "a" G (e/abstract1 (eqG G (e/app* sub a zr) a) 21) :default)
        acT  (e/forall' "a" G (e/abstract1 (e/forall' "b" G (e/abstract1 (eqG G (e/app* add a b) (e/app* add b a)) 22) :default) 21) :default)
        ascT (e/forall' "a" G (e/abstract1 (e/forall' "b" G (e/abstract1 (eqG G (e/app* sub (e/app* add a b) b) a) 22) :default) 21) :default)
        igenP (e/app* (e/const' (nm "Stream.Igen") []) G add s)
        dterm (fn [tt] (e/app* (e/const' (nm "Stream.Dgen") []) G zr sub igenP tt))
        mu (e/lam "t" natT (eqG G (dterm (e/bvar 0)) (e/app s (e/bvar 0))) :default)
        zeroPf (e/app* sz (e/app s (nzero)))
        av (e/app* (e/const' (nm "Stream.Igen") []) G add s t') bv (e/app s (nsucc t'))
        succPf (trG G (e/app* sub (e/app* add av bv) av) (e/app* sub (e/app* add bv av) av) bv
                    (cgG G (e/app* add av bv) (e/app* add bv av) (e/lam "w" G (e/app* sub (e/bvar 0) av) :default) (e/app* ac av bv))
                    (e/app* asc bv av))
        succLam (e/lam "t'" natT (e/abstract1 succPf 10) :default)
        body (e/app* (e/const' (nm "Nat.casesOn") [z]) mu t zeroPf succLam)
        wrap (fn [x lamf] (-> x (#(lamf "t" natT (e/abstract1 % 9))) (#(lamf "s" sT (e/abstract1 % 8)))
                               (#(lamf "asc" ascT (e/abstract1 % 7))) (#(lamf "ac" acT (e/abstract1 % 6)))
                               (#(lamf "sz" szT (e/abstract1 % 5))) (#(lamf "sub" subT (e/abstract1 % 4)))
                               (#(lamf "add" addT (e/abstract1 % 3))) (#(lamf "zero" G (e/abstract1 % 2)))
                               (#(lamf "G" TypeT (e/abstract1 % 1)))))]
    [(wrap (eqG G (dterm t) (e/app s t)) (fn [n ty b] (e/forall' n ty b :default)))
     (wrap body (fn [n ty b] (e/lam n ty b :default)))]))

;; ── Stream.I_D_gen : I∘D = id over any abelian group (telescoping; sub_zero + add_comm + sub_add_cancel) ─
(defn- prove-I-D-gen []
  (let [G (e/fvar 1) zr (e/fvar 2) add (e/fvar 3) sub (e/fvar 4) sz (e/fvar 5) ac (e/fvar 6) sac (e/fvar 7) s (e/fvar 8) t (e/fvar 9) n (e/fvar 10) ih (e/fvar 11)
        GG (e/forall' "_" G G :default) addT (e/forall' "_" G GG :default) subT (e/forall' "_" G GG :default) sT (e/forall' "_" natT G :default)
        a (e/fvar 21) b (e/fvar 22)
        szT  (e/forall' "a" G (e/abstract1 (eqG G (e/app* sub a zr) a) 21) :default)
        acT  (e/forall' "a" G (e/abstract1 (e/forall' "b" G (e/abstract1 (eqG G (e/app* add a b) (e/app* add b a)) 22) :default) 21) :default)
        sacT (e/forall' "a" G (e/abstract1 (e/forall' "b" G (e/abstract1 (eqG G (e/app* add (e/app* sub a b) b) a) 22) :default) 21) :default)
        ds (e/app* (e/const' (nm "Stream.Dgen") []) G zr sub s)
        igen (fn [tt] (e/app* (e/const' (nm "Stream.Igen") []) G add ds tt))
        mu (e/lam "t" natT (eqG G (igen (e/bvar 0)) (e/app s (e/bvar 0))) :default)
        base (e/app* sz (e/app s (nzero)))
        av (e/app s n) bv (e/app s (nsucc n)) subba (e/app* sub bv av)
        ihLHS (igen n) ihT (eqG G ihLHS (e/app s n))
        step1 (cgG G ihLHS av (e/lam "w" G (e/app* add (e/bvar 0) subba) :default) ih)
        step2 (trG G (e/app* add av subba) (e/app* add subba av) bv (e/app* ac av subba) (e/app* sac bv av))
        result (trG G (e/app* add ihLHS subba) (e/app* add av subba) bv step1 step2)
        step (e/lam "n" natT (e/abstract1 (e/lam "ih" ihT (e/abstract1 result 11) :default) 10) :default)
        body (e/app* (e/const' (nm "Nat.rec") [z]) mu base step t)
        wrap (fn [x lamf] (-> x (#(lamf "t" natT (e/abstract1 % 9))) (#(lamf "s" sT (e/abstract1 % 8)))
                               (#(lamf "sac" sacT (e/abstract1 % 7))) (#(lamf "ac" acT (e/abstract1 % 6)))
                               (#(lamf "sz" szT (e/abstract1 % 5))) (#(lamf "sub" subT (e/abstract1 % 4)))
                               (#(lamf "add" addT (e/abstract1 % 3))) (#(lamf "zero" G (e/abstract1 % 2)))
                               (#(lamf "G" TypeT (e/abstract1 % 1)))))]
    [(wrap (eqG G (igen t) (e/app s t)) (fn [n2 ty b] (e/forall' n2 ty b :default)))
     (wrap body (fn [n2 ty b] (e/lam n2 ty b :default)))]))

;; ── Int as a CERTIFIED instance: instantiate the generic laws with Int's four group lemmas ─────────
(defn- int-instance [gen-name asc-or-sac-lemma]
  ;; the partial application `<gen> Int 0 Int.add Int.sub Int.sub_zero Int.add_comm <lemma>` : ∀ s t, …
  (e/app* (e/const' (nm gen-name) []) intT iZero (e/const' (nm "Int.add") []) (e/const' (nm "Int.sub") [])
          (e/const' (nm "Int.sub_zero") []) (e/const' (nm "Int.add_comm") []) (e/const' (nm asc-or-sac-lemma) [])))

(defn- int-instance-type [igen-or-dgen-fn]
  ;; ∀ (s:Nat→Int)(t:Nat), Eq Int (<I/D composition over Int> s t) (s t)
  (let [s (e/fvar 1) t (e/fvar 2) sT (e/forall' "_" natT intT :default)]
    (-> (eqG intT (igen-or-dgen-fn s t) (e/app s t))
        (#(e/forall' "t" natT (e/abstract1 % 2) :default))
        (#(e/forall' "s" sT (e/abstract1 % 1) :default)))))

(defn- di-int-comp [s t]   ; Dgen Int 0 Int.sub (Igen Int Int.add s) t
  (e/app* (e/const' (nm "Stream.Dgen") []) intT iZero (e/const' (nm "Int.sub") [])
          (e/app* (e/const' (nm "Stream.Igen") []) intT (e/const' (nm "Int.add") []) s) t))
(defn- id-int-comp [s t]   ; Igen Int Int.add (Dgen Int 0 Int.sub s) t
  (e/app* (e/const' (nm "Stream.Igen") []) intT (e/const' (nm "Int.add") [])
          (e/app* (e/const' (nm "Stream.Dgen") []) intT iZero (e/const' (nm "Int.sub") []) s) t))

(defn install!
  "Install the group-generic DBSP differential calculus (idempotent): generic `Stream.Igen`/`Stream.Dgen`,
   the group-generic mutual-inverse theorems `Stream.D_I_gen`/`Stream.I_D_gen`, and `Int` recovered as a
   certified instance `Stream.D_I_int`/`Stream.I_D_int`. Every constant is check-constant'd."
  []
  (when-not (kenv/lookup (a/env) (nm "Stream.I_D_int"))
    (let [reg!  (fn [ci] (swap! a/ansatz-env kenv/check-constant ci) ci)
          thm!  (fn [n pf] (reg! (let [[g p] (pf)] (kenv/mk-thm (nm n) [] g p))))
          inst! (fn [n ty pf] (reg! (kenv/mk-thm (nm n) [] ty pf)))]
      (reg! (mk-Igen)) (reg! (mk-Dgen))
      (thm! "Stream.D_I_gen" prove-D-I-gen)
      (thm! "Stream.I_D_gen" prove-I-D-gen)
      (inst! "Stream.D_I_int" (int-instance-type di-int-comp) (int-instance "Stream.D_I_gen" "Int.add_sub_cancel"))
      (inst! "Stream.I_D_int" (int-instance-type id-int-comp) (int-instance "Stream.I_D_gen" "Int.sub_add_cancel"))))
  (a/env))
