(ns wandler.laws.tropical
  "The TROPICAL (min,+) semiring as a CERTIFIED carrier for the frame family — ℕ∞ = `ENat` (a fresh
   2-constructor inductive: `ENat.inf` = +∞, `ENat.fin n`). ⊕ = `ENat.min` (min, identity +∞), ⊗ =
   `ENat.plus` (addition, +∞ annihilates). This is the third registered carrier after Nat (counting/SUM)
   and Bool (provenance): it makes the certified frame index do MIN-PLUS pre-aggregation — shortest-path /
   Viterbi-style DP through a join, each bucket pre-min-summed (O(distinct-keys)).

   Unlike Nat/Bool, tropical needs a TOP element (the additive identity for min = the annihilator for +),
   absent from Init — so we build ℕ∞ ourselves and PROVE the six semiring laws the generic frame family
   requires, Init-only. The one genuinely missing Nat fact, `x + min y z = min (x+y) (x+z)`
   (`Nat.add_min_distrib`), is proven here by `Nat.le_total` case analysis. The ENat laws are raw
   `ENat.casesOn` terms (the match-defined ops iota-reduce on constructors, so each leaf closes by
   reflexivity or `congrArg ENat.fin` of the Nat fact). All admitted via check-constant. See
   [[faq-variable-elimination]]; consumed by the `ENat` row in wandler.optimize.physical/semiring-registry."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [wandler.laws.semiring :as sreg]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ z))
(defn- c [s] (e/const' (nm s) []))
(defn- cl [s lvls] (e/const' (nm s) lvls))
(defn- admit! [nme g p]
  (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm nme) [] g p))))
(defn- has? [n] (some? (kenv/lookup (a/env) (nm n))))

;; ── Nat.add_min_distrib : x + min y z = min (x+y) (x+z)  (the missing Init lemma) ──────────────────
;; By Nat.le_total y z: in each branch min_eq_left/right collapses both mins (add_le_add_left ports the
;; ≤ across +), so both sides reduce to the same +.
(defn- build-add-min-distrib []
  (let [Nat (c "Nat")
        addN (fn [a b] (e/app* (c "Nat.add") a b)) minN (fn [a b] (e/app* (c "Nat.min") a b))
        le (fn [a b] (e/app* (cl "LE.le" [z]) Nat (c "instLENat") a b))
        eqN (fn [a b] (e/app* (cl "Eq" [L1]) Nat a b))
        x (e/fvar 1) y (e/fvar 2) zz (e/fvar 3) addx (e/lam "w" Nat (addN x (e/bvar 0)) :default)
        mkb (fn [el pk sa sb h]
              (let [myz (e/app* (c el) y zz h) side (e/app* (c "Nat.add_le_add_left") sa sb h x)
                    madd (e/app* (c el) (addN x y) (addN x zz) side)
                    cg (e/app* (cl "congrArg" [L1 L1]) Nat Nat (minN y zz) pk addx myz)
                    gR (minN (addN x y) (addN x zz)) ms (e/app* (cl "Eq.symm" [L1]) Nat gR (addN x pk) madd)]
                (e/app* (cl "Eq.trans" [L1]) Nat (addN x (minN y zz)) (addN x pk) gR cg ms)))
        Lb (e/lam "h" (le y zz) (mkb "Nat.min_eq_left" y y zz (e/bvar 0)) :default)
        Rb (e/lam "h" (le zz y) (mkb "Nat.min_eq_right" zz zz y (e/bvar 0)) :default)
        gC (eqN (addN x (minN y zz)) (minN (addN x y) (addN x zz)))
        body (e/app* (c "Or.elim") (le y zz) (le zz y) gC (e/app* (c "Nat.le_total") y zz) Lb Rb)
        wr (fn [t f] (-> t (#(f "z" Nat (e/abstract1 % 3))) (#(f "y" Nat (e/abstract1 % 2))) (#(f "x" Nat (e/abstract1 % 1)))))]
    [(wr gC (fn [n T b] (e/forall' n T b :default))) (wr body (fn [n T b] (e/lam n T b :default)))]))

;; ── Nat.min_assoc_bare : bare-spelled min-assoc (Init's is typeclass `Min.min`; we want `Nat.min`) ──
(defn- build-min-assoc-bare []
  (let [Nat (c "Nat") minN (fn [a b] (e/app* (c "Nat.min") a b)) eqN (fn [a b] (e/app* (cl "Eq" [L1]) Nat a b))
        x (e/fvar 1) y (e/fvar 2) zz (e/fvar 3)
        wr (fn [t f] (-> t (#(f "z" Nat (e/abstract1 % 3))) (#(f "y" Nat (e/abstract1 % 2))) (#(f "x" Nat (e/abstract1 % 1)))))]
    [(wr (eqN (minN (minN x y) zz) (minN x (minN y zz))) (fn [n T b] (e/forall' n T b :default)))
     (wr (e/app* (c "Nat.min_assoc") x y zz) (fn [n T b] (e/lam n T b :default)))]))

;; ── the six ENat semiring laws (raw ENat.casesOn; leaves reduce on constructors) ───────────────────
(defn- build-enat-lemmas []
  (let [EN (c "ENat") infE (c "ENat.inf") finE (fn [n] (e/app* (c "ENat.fin") n))
        minE (fn [a b] (e/app* (c "ENat.min") a b)) plusE (fn [a b] (e/app* (c "ENat.plus") a b))
        eqE (fn [a b] (e/app* (cl "Eq" [L1]) EN a b)) reflE (fn [x] (e/app* (cl "Eq.refl" [L1]) EN x))
        Nat (c "Nat") natMin (fn [a b] (e/app* (c "Nat.min") a b)) natAdd (fn [a b] (e/app* (c "Nat.add") a b))
        caE (fn [mot t infc finc] (e/app* (cl "ENat.casesOn" [z]) mot t infc finc))
        liftFin (fn [a1 a2 h] (e/app* (cl "congrArg" [L1 L1]) Nat EN a1 a2 (e/lam "w" Nat (finE (e/bvar 0)) :default) h))
        motlam (fn [v body] (e/lam "k" EN (e/abstract1 body v) :default))
        finlam (fn [v body] (e/lam "n" Nat (e/abstract1 body v) :default))
        a (e/fvar 1) b (e/fvar 2) cc (e/fvar 3) av (e/fvar 10) bv (e/fvar 14) cv (e/fvar 15)
        xf (e/fvar 11) yf (e/fvar 12) zf (e/fvar 13)
        wr1 (fn [t f] (f "a" EN (e/abstract1 t 1)))
        wr3 (fn [t f] (-> t (#(f "c" EN (e/abstract1 % 3))) (#(f "b" EN (e/abstract1 % 2))) (#(f "a" EN (e/abstract1 % 1)))))
        FA (fn [n T bd] (e/forall' n T bd :default)) LA (fn [n T bd] (e/lam n T bd :default))]
    {;; inf_min : min inf a = a   (definitional)
     "ENat.inf_min"
     [(wr1 (eqE (minE infE a) a) FA) (e/lam "a" EN (reflE (e/bvar 0)) :default)]
     ;; inf_plus : plus inf a = inf   (definitional)
     "ENat.inf_plus"
     [(wr1 (eqE (plusE infE a) infE) FA) (e/lam "a" EN infE :default)]
     ;; min_inf : min a inf = a   (cases on a)
     "ENat.min_inf"
     [(wr1 (eqE (minE a infE) a) FA)
      (caE (motlam 10 (eqE (minE av infE) av)) a (reflE infE) (finlam 11 (reflE (finE xf))))]
     ;; plus_inf : plus a inf = inf   (cases on a)
     "ENat.plus_inf"
     [(wr1 (eqE (plusE a infE) infE) FA)
      (caE (motlam 10 (eqE (plusE av infE) infE)) a (reflE infE) (finlam 11 (reflE infE)))]
     ;; min_assoc : min (min a b) c = min a (min b c)   (3-deep; fin/fin/fin via Nat.min_assoc_bare)
     "ENat.min_assoc"
     (let [motA (motlam 10 (eqE (minE (minE av b) cc) (minE av (minE b cc))))
           motB (motlam 14 (eqE (minE (minE (finE xf) bv) cc) (minE (finE xf) (minE bv cc))))
           motC (motlam 15 (eqE (minE (minE (finE xf) (finE yf)) cv) (minE (finE xf) (minE (finE yf) cv))))
           finC (finlam 13 (liftFin (natMin (natMin xf yf) zf) (natMin xf (natMin yf zf))
                                    (e/app* (c "Nat.min_assoc_bare") xf yf zf)))
           finB (finlam 12 (caE motC cc (reflE (minE (finE xf) (finE yf))) finC))
           finA (finlam 11 (caE motB b (reflE (minE (finE xf) cc)) finB))
           body (caE motA a (reflE (minE b cc)) finA)]
       [(wr3 (eqE (minE (minE a b) cc) (minE a (minE b cc))) FA) (wr3 body LA)])
     ;; plus_min_distrib : plus a (min b c) = min (plus a b) (plus a c)   (3-deep; via Nat.add_min_distrib)
     "ENat.plus_min_distrib"
     (let [motA (motlam 10 (eqE (plusE av (minE b cc)) (minE (plusE av b) (plusE av cc))))
           motB (motlam 14 (eqE (plusE (finE xf) (minE bv cc)) (minE (plusE (finE xf) bv) (plusE (finE xf) cc))))
           motC (motlam 15 (eqE (plusE (finE xf) (minE (finE yf) cv)) (minE (plusE (finE xf) (finE yf)) (plusE (finE xf) cv))))
           finC (finlam 13 (liftFin (natAdd xf (natMin yf zf)) (natMin (natAdd xf yf) (natAdd xf zf))
                                     (e/app* (c "Nat.add_min_distrib") xf yf zf)))
           finB (finlam 12 (caE motC cc (reflE (plusE (finE xf) (finE yf))) finC))
           finA (finlam 11 (caE motB b (reflE (plusE (finE xf) cc)) finB))
           body (caE motA a (reflE infE) finA)]
       [(wr3 (eqE (plusE a (minE b cc)) (minE (plusE a b) (plusE a cc))) FA) (wr3 body LA)])}))

(defn install!
  "Admit the ℕ∞ (ENat) tropical carrier + its six certified semiring laws (idempotent). Requires the base
   env (Nat.min/Nat.add/Or.elim/… from Init). Defines `ENat` + `ENat.min`/`ENat.plus`, then admits every
   law via check-constant. After this, the `ENat` row in the optimizer's semiring-registry fires."
  []
  (when-not (has? "ENat.plus_min_distrib")
    ;; 1. the two Nat-level helpers (one a genuine Init gap, one a bare respelling)
    (let [[g p] (build-add-min-distrib)] (admit! "Nat.add_min_distrib" g p))
    (let [[g p] (build-min-assoc-bare)]  (admit! "Nat.min_assoc_bare" g p))
    ;; 2. the carrier + ops (match-defined ⇒ iota-reduce on constructors)
    (binding [a/*verbose* false]
      (when-not (has? "ENat")
        (eval '(ansatz.core/inductive ENat [] (inf) (fin [n Nat])))
        (eval '(ansatz.core/defn ENat.min [a :- ENat, b :- ENat] ENat
                 (match a ENat ENat (inf b)
                        (fin [x] (match b ENat ENat (inf (ENat.fin x))
                                        (fin [y] (ENat.fin (Nat.min x y))))))))
        (eval '(ansatz.core/defn ENat.plus [a :- ENat, b :- ENat] ENat
                 (match a ENat ENat (inf (ENat.inf))
                        (fin [x] (match b ENat ENat (inf (ENat.inf))
                                        (fin [y] (ENat.fin (Nat.add x y))))))))))
    ;; 3. the six semiring laws
    (doseq [[lbl [g p]] (build-enat-lemmas)]
      (admit! lbl g p)))
  ;; 4. register the ℕ∞ row so the optimizer's frame index instantiates the generic laws at (ENat,min,plus,∞)
  (sreg/register! "ENat" {:add "ENat.min" :mul "ENat.plus" :zero "ENat.inf"
                          :hAA "ENat.min_assoc" :hZA "ENat.inf_min" :hAZ "ENat.min_inf"
                          :hMA "ENat.plus_min_distrib" :hMZ "ENat.plus_inf" :hZM "ENat.inf_plus"})
  (a/env))

(defn carrier-installed? [] (has? "ENat.plus_min_distrib"))
