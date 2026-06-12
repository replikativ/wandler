(ns wandler.dist-laws
  "L0 KEYSTONE for the FinSet/FinDist monad (wandler.dist): the monad LEFT-UNIT law `bind (return a) f = f a`
   proven in the kernel for the weighted-list representation `List (A × S)`, GENERIC over `(S, mul, one)`
   with `one_mul : ∀ w, mul one w = w` as a hypothesis (the dbsp-group style — laws-as-hypotheses).

     return a  = [ (a, 1̄) ]
     bind m f  = flatMap (λp. map (λq. (q.1, p.2 ⊗ q.2)) (f p.1)) m
     left-unit : bind (return a) f = f a          -- needs ONLY the ⊗-unit law (one_mul) + Prod.eta + List.map_id''

   PROVEN (both unit laws, generic over the ⊗-monoid):
     WList.left_unit  : bind (return a) f = f a   — needs only `one_mul : ∀ w, mul one w = w`
     WList.right_unit : bind m return = m         — needs only `mul_one : ∀ w, mul w one = w`
   Each is proven via the same shape: a singleton flatMap/map reduces definitionally, then `List.append_nil`
   / `List.map_eq_flatMap` + `List.map_id''` over a per-element `ψ q = q` (`mul`-unit + `Prod.eta`). They
   instantiate at `Bool` (FinSet), `Nat` (counting), etc.

   ASSOCIATIVITY `bind (bind m f) g = bind m (λa. bind (f a) g)` is the remaining law — DOCUMENTED, deferred
   to a focused pass. It additionally needs `mul_assoc` (the ⊗-monoid associativity) and a deeper congruence
   chain: `List.flatMap_assoc` to merge the outer flatMaps; `List.flatMap_map`/`List.map_flatMap` to push the
   scaling-maps through; the inner `Gg(Mf p r) = map (Mf p) (Gg r)` via `List.map_map` + `congrArg mul_assoc`;
   lifted by `funext`+`congrArg` over the two flatMap levels (this kernel lacks `List.flatMap_congr`). The two
   unit laws are the binding-identity laws (they pin `return`); associativity is the mechanical sum-product
   re-association. See [[finset-findist-monad]]."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(def ^:private type0 (e/sort' L1))
(defn- c' [s & ls] (e/const' (nm s) (vec ls)))
(defn- prodOf [x y] (e/app* (c' "Prod" z z) x y))
(defn- listOf [x] (e/app (c' "List" z) x))
(defn- mk [X Y u v] (e/app* (c' "Prod.mk" z z) X Y u v))
(defn- fst [X Y p] (e/app* (c' "Prod.fst" z z) X Y p))
(defn- snd [X Y p] (e/app* (c' "Prod.snd" z z) X Y p))
(defn- eqL [T x y] (e/app* (c' "Eq" L1) T x y))
(defn- trL [T x y w h1 h2] (e/app* (c' "Eq.trans" L1) T x y w h1 h2))

(defn- prove-wlist-left-unit []
  (let [A (e/fvar 1) B (e/fvar 2) S (e/fvar 3) mul (e/fvar 4) one (e/fvar 5) onemul (e/fvar 6) av (e/fvar 7) f (e/fvar 8) q (e/fvar 11)
        SS (e/forall' "_" S S :default) mulT (e/forall' "_" S SS :default)
        pAS (prodOf A S) pBS (prodOf B S) listBS (listOf pBS) fT (e/forall' "_" A listBS :default)
        onemulT (e/forall' "w" S (e/abstract1 (eqL S (e/app* mul one (e/fvar 20)) (e/fvar 20)) 20) :default)
        mulp (fn [x y] (e/app* mul x y))
        ret (e/app* (c' "List.cons" z) pAS (mk A S av one) (e/app (c' "List.nil" z) pAS))
        gfn (e/lam "p" pAS
              (e/app* (c' "List.map" z z) pBS pBS
                (e/lam "q" pBS (mk B S (fst B S (e/bvar 0)) (mulp (snd A S (e/bvar 1)) (snd B S (e/bvar 0)))) :default)
                (e/app f (fst A S (e/bvar 0)))) :default)
        bindterm (e/app* (c' "List.flatMap" z z) pAS pBS gfn ret)
        fa (e/app f av)
        psi (e/lam "q" pBS (mk B S (fst B S (e/bvar 0)) (mulp one (snd B S (e/bvar 0)))) :default)
        mappsifa (e/app* (c' "List.map" z z) pBS pBS psi fa)
        hbody (trL pBS (mk B S (fst B S q) (mulp one (snd B S q))) (mk B S (fst B S q) (snd B S q)) q
                (e/app* (c' "congrArg" L1 L1) S pBS (mulp one (snd B S q)) (snd B S q)
                        (e/lam "wv" S (mk B S (fst B S q) (e/bvar 0)) :default) (e/app onemul (snd B S q)))
                (e/app* (c' "Prod.eta" z z) B S q))
        hpf (e/lam "q" pBS (e/abstract1 hbody 11) :default)
        step1 (e/app* (c' "List.append_nil" z) pBS mappsifa)
        step2 (e/app* (c' "List.map_id''" z) pBS psi hpf fa)
        pf-inner (trL listBS bindterm mappsifa fa step1 step2)
        wrap (fn [x lamf] (-> x (#(lamf "f" fT (e/abstract1 % 8))) (#(lamf "a" A (e/abstract1 % 7)))
                               (#(lamf "one_mul" onemulT (e/abstract1 % 6))) (#(lamf "one" S (e/abstract1 % 5)))
                               (#(lamf "mul" mulT (e/abstract1 % 4))) (#(lamf "S" type0 (e/abstract1 % 3)))
                               (#(lamf "B" type0 (e/abstract1 % 2))) (#(lamf "A" type0 (e/abstract1 % 1)))))]
    [(wrap (eqL listBS bindterm fa) (fn [n t b] (e/forall' n t b :default)))
     (wrap pf-inner (fn [n t b] (e/lam n t b :default)))]))

(defn- prove-wlist-right-unit []
  ;; bind m return = m  — needs only the RIGHT ⊗-unit (mul_one : ∀ w, mul w one = w) + Prod.eta.
  (let [A (e/fvar 1) S (e/fvar 3) mul (e/fvar 4) one (e/fvar 5) mulone (e/fvar 6) m (e/fvar 9) p (e/fvar 11)
        SS (e/forall' "_" S S :default) mulT (e/forall' "_" S SS :default)
        pAS (prodOf A S) listAS (listOf pAS)
        muloneT (e/forall' "w" S (e/abstract1 (eqL S (e/app* mul (e/fvar 20) one) (e/fvar 20)) 20) :default)
        mulp (fn [x y] (e/app* mul x y))
        gfn (e/lam "p" pAS
              (e/app* (c' "List.map" z z) pAS pAS
                (e/lam "q" pAS (mk A S (fst A S (e/bvar 0)) (mulp (snd A S (e/bvar 1)) (snd A S (e/bvar 0)))) :default)
                (e/app* (c' "List.cons" z) pAS (mk A S (fst A S (e/bvar 0)) one) (e/app (c' "List.nil" z) pAS))) :default)
        bindterm (e/app* (c' "List.flatMap" z z) pAS pAS gfn m)
        phi (e/lam "p" pAS (mk A S (fst A S (e/bvar 0)) (mulp (snd A S (e/bvar 0)) one)) :default)
        mapphi (e/app* (c' "List.map" z z) pAS pAS phi m)
        flatphi (e/app* (c' "List.flatMap" z z) pAS pAS (e/lam "a" pAS (e/app* (c' "List.cons" z) pAS (e/app phi (e/bvar 0)) (e/app (c' "List.nil" z) pAS)) :default) m)
        meflat (e/app* (c' "List.map_eq_flatMap" z z) pAS pAS phi m)
        symmmef (e/app* (c' "Eq.symm" L1) listAS mapphi flatphi meflat)
        hbody (trL pAS (mk A S (fst A S p) (mulp (snd A S p) one)) (mk A S (fst A S p) (snd A S p)) p
                (e/app* (c' "congrArg" L1 L1) S pAS (mulp (snd A S p) one) (snd A S p)
                        (e/lam "wv" S (mk A S (fst A S p) (e/bvar 0)) :default) (e/app mulone (snd A S p)))
                (e/app* (c' "Prod.eta" z z) A S p))
        hpf (e/lam "p" pAS (e/abstract1 hbody 11) :default)
        mapid (e/app* (c' "List.map_id''" z) pAS phi hpf m)
        pf-inner (trL listAS bindterm mapphi m symmmef mapid)
        wrap (fn [x lamf] (-> x (#(lamf "m" listAS (e/abstract1 % 9))) (#(lamf "mul_one" muloneT (e/abstract1 % 6)))
                               (#(lamf "one" S (e/abstract1 % 5))) (#(lamf "mul" mulT (e/abstract1 % 4)))
                               (#(lamf "S" type0 (e/abstract1 % 3))) (#(lamf "A" type0 (e/abstract1 % 1)))))]
    [(wrap (eqL listAS bindterm m) (fn [n t b] (e/forall' n t b :default)))
     (wrap pf-inner (fn [n t b] (e/lam n t b :default)))]))

(defn install!
  "Install the FinSet/FinDist monad LAWS (idempotent): `WList.left_unit` + `WList.right_unit` (the two unit
   laws), each proven generic over the ⊗-monoid (one_mul / mul_one) of any semiring."
  []
  (when-not (kenv/lookup (a/env) (nm "WList.right_unit"))
    (let [thm! (fn [n pf] (let [[g p] (pf)] (swap! a/ansatz-env kenv/check-constant (kenv/mk-thm (nm n) [] g p))))]
      (thm! "WList.left_unit"  prove-wlist-left-unit)
      (thm! "WList.right_unit" prove-wlist-right-unit)))
  (a/env))
