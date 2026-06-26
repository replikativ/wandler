(ns wandler.exec.mode-laws
  "Kernel-proof layer for the mode lattice (extracted from wandler.exec.mode): the batch modality `Box`,
   the additive-identity Z-set `Zzero`, and the ONE admitted law `Mode.diff_async_dist` (the diff×async
   distributive law, PROVEN by induction on n via Strm.scan_step + linearity). `install!` admits all three
   (idempotent, cached), after ensuring the Z-set + Strm laws the ∂ pass cites are present. The routing /
   execute / ∂-pass code stays in wandler.exec.mode and re-exports this `install!`. Mirrors how zset/dbsp
   keep their proofs in their own files."
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- zsetOf [A] (e/app (e/const' (nm "Zset") []) A))
(defn- strmOf [A] (e/app (e/const' (nm "Strm") []) A))
(defn- eqZ [T x y] (e/app* (e/const' (nm "Eq") [L1]) T x y))
(defn- zaddE [A m1 m2] (e/app* (e/const' (nm "Zadd") []) A m1 m2))
(defn- zzeroOf [A] (e/app (e/const' (nm "Zzero") []) A))

(defn- box-def []
  ;; Box.{u} : Type u → Type u := fun A => A   — the □ STABLE/BATCH modality (can run any time).
  (kenv/mk-def (nm "Box") [] (e/forall' "A" type0 type0 :default)
               (e/lam "A" type0 (e/bvar 0) :default) :hints :opaque))

(defn- zzero-def []
  ;; Zzero : ∀ A, Zset A := fun A a => Int.ofNat 0   — the additive identity Z-set (empty relation).
  (let [zeroInt (e/app (e/const' (nm "Int.ofNat") []) (e/const' (nm "Nat.zero") []))]
    (kenv/mk-def (nm "Zzero") [] (e/forall' "A" type0 (zsetOf (e/bvar 0)) :default)
                 (e/lam "A" type0 (e/lam "a" (e/bvar 0) zeroInt :default) :default))))

(def ^:private natT (e/const' (nm "Nat") []))
(def ^:private n0 (e/const' (nm "Nat.zero") []))
(defn- nsucc [n] (e/app (e/const' (nm "Nat.succ") []) n))
(defn- zaddPart [A] (e/app (e/const' (nm "Zadd") []) A))
(defn- etrans [T x y w h1 h2] (e/app* (e/const' (nm "Eq.trans") [L1]) T x y w h1 h2))
(defn- esymm [T x y h] (e/app* (e/const' (nm "Eq.symm") [L1]) T x y h))
(defn- cong-q [A B q a1 a2 h] (e/app* (e/const' (nm "congrArg") [L1 L1]) (zsetOf A) (zsetOf B) a1 a2 q h))

(defn- prove-diff-async-dist []
  ;; Mode.diff_async_dist : the diff×async DISTRIBUTIVE LAW — PROVEN (induction on n via Strm.scan_step).
  ;; A LINEAR Z-set operator q (commutes with ⊞ AND preserves 0 — an LTI operator) commutes with stream
  ;; integration (Strm.scan over Zadd): integrating the stream of q-applied deltas equals q of the
  ;; integrated stream. The DBSP fact that linear operators commute with I.
  ;;   ∀ (A B : Type) (q : Zset A → Zset B),
  ;;     (hlin : ∀ a b, q (a ⊞ b) = q a ⊞ q b)          -- q additive
  ;;     (hz   : q 0 = 0)                                -- q preserves the empty relation
  ;;     ∀ (s : Strm (Zset A)) (n : Nat),
  ;;       scan ⊞ 0 (smap q s) n  =  q (scan ⊞ 0 s n)
  ;; Base n=0:  Zadd_B 0 (q s0) =[symm congr hz] Zadd_B (q 0)(q s0) =[symm hlin 0 s0] q(Zadd_A 0 s0).
  ;; Step:      scanB(n+1) =[scan_step] Zadd_B (scanB n)(q sₙ₊₁) =[ih] … =[symm hlin] q(Zadd_A (scanA n) sₙ₊₁)
  ;;            =[congr (symm scan_step)] q(scanA(n+1)).
  (let [A (e/fvar 1) B (e/fvar 2) q (e/fvar 3) hlin (e/fvar 4) hz (e/fvar 5) s (e/fvar 6)
        qA   (fn [x] (e/app q x))
        smap (e/app* (e/const' (nm "Strm.smap") []) (zsetOf A) (zsetOf B) q s)
        scanB-strm (e/app* (e/const' (nm "Strm.scan") []) (zsetOf B) (zsetOf B) (zaddPart B) (zzeroOf B) smap)
        scanA-strm (e/app* (e/const' (nm "Strm.scan") []) (zsetOf A) (zsetOf A) (zaddPart A) (zzeroOf A) s)
        scanB (fn [k] (e/app scanB-strm k))
        scanA (fn [k] (e/app scanA-strm k))
        sAt   (fn [k] (e/app s k))
        hlinAt (fn [aa bb] (e/app* hlin aa bb))
        M    (e/lam "n" natT (eqZ (zsetOf B) (scanB (e/bvar 0)) (qA (scanA (e/bvar 0)))) :default)
        ;; base
        s0 (sAt n0) zB0 (zzeroOf B) zA0 (zzeroOf A)
        congHz (cong-q B B (e/lam "w" (zsetOf B) (zaddE B (e/bvar 0) (qA s0)) :default) (qA zA0) zB0 hz)
        base (etrans (zsetOf B) (zaddE B zB0 (qA s0)) (zaddE B (qA zA0) (qA s0)) (qA (zaddE A zA0 s0))
                     (esymm (zsetOf B) (zaddE B (qA zA0) (qA s0)) (zaddE B zB0 (qA s0)) congHz)
                     (esymm (zsetOf B) (qA (zaddE A zA0 s0)) (zaddE B (qA zA0) (qA s0)) (hlinAt zA0 s0)))
        ;; step
        ssA (fn [n] (e/app* (e/const' (nm "Strm.scan_step") []) (zsetOf A) (zsetOf A) (zaddPart A) (zzeroOf A) s n))
        ssB (fn [n] (e/app* (e/const' (nm "Strm.scan_step") []) (zsetOf B) (zsetOf B) (zaddPart B) (zzeroOf B) smap n))
        nn (e/fvar 7) ih (e/fvar 8)
        sSn (sAt (nsucc nn)) IRn (scanB nn) ILn (scanA nn)
        stepbody
        (etrans (zsetOf B) (scanB (nsucc nn)) (zaddE B IRn (qA sSn)) (qA (scanA (nsucc nn)))
          (ssB nn)
          (etrans (zsetOf B) (zaddE B IRn (qA sSn)) (zaddE B (qA ILn) (qA sSn)) (qA (scanA (nsucc nn)))
            (cong-q B B (e/lam "w" (zsetOf B) (zaddE B (e/bvar 0) (qA sSn)) :default) IRn (qA ILn) ih)
            (etrans (zsetOf B) (zaddE B (qA ILn) (qA sSn)) (qA (zaddE A ILn sSn)) (qA (scanA (nsucc nn)))
              (esymm (zsetOf B) (qA (zaddE A ILn sSn)) (zaddE B (qA ILn) (qA sSn)) (hlinAt ILn sSn))
              (cong-q A B q (zaddE A ILn sSn) (scanA (nsucc nn))
                      (esymm (zsetOf A) (scanA (nsucc nn)) (zaddE A ILn sSn) (ssA nn))))))
        Mn   (eqZ (zsetOf B) (scanB nn) (qA (scanA nn)))
        step (e/lam "n" natT (e/abstract1 (e/lam "ih" Mn (e/abstract1 stepbody 8) :default) 7) :default)
        natrec (e/app* (e/const' (nm "Nat.rec") [z]) M base step)
        ;; the statement
        body-ty (e/forall' "n" natT (eqZ (zsetOf B) (scanB (e/bvar 0)) (qA (scanA (e/bvar 0)))) :default)
        hlin-ty (e/forall' "a" (zsetOf A)
                  (e/abstract1 (e/forall' "b" (zsetOf A)
                    (e/abstract1 (eqZ (zsetOf B) (qA (zaddE A (e/fvar 20) (e/fvar 21)))
                                   (zaddE B (qA (e/fvar 20)) (qA (e/fvar 21)))) 21) :default) 20) :default)
        hz-ty (eqZ (zsetOf B) (qA zA0) zB0)
        wrap (fn [t mk] (-> t (#(mk "s" (strmOf (zsetOf A)) 6 %)) (#(mk "hz" hz-ty 5 %)) (#(mk "hlin" hlin-ty 4 %))
                            (#(mk "q" (e/forall' "_" (zsetOf A) (zsetOf B) :default) 3 %))
                            (#(mk "B" type0 2 %)) (#(mk "A" type0 1 %))))]
    [(wrap body-ty (fn [nme t i b] (e/forall' nme t (e/abstract1 b i) :default)))
     (wrap natrec  (fn [nme t i b] (e/lam nme t (e/abstract1 b i) :default)))]))

(defonce ^:private cache (atom nil))

(defn install!
  "Install the mode-layer kernel constants (idempotent), after ensuring the Z-set + Strm laws the ∂ pass
   cites are present:
     Box                  — the □ stable/batch modality (def, opaque)
     Zzero                — the additive-identity Z-set (def)
     Mode.diff_async_dist — the diff×async distributive law, PROVEN by induction on n (Strm.scan_step +
                            linearity); a linear (additive, 0-preserving) Z-set op commutes with ∫."
  []
  ((requiring-resolve 'wandler.exec.zset/install!))
  ((requiring-resolve 'wandler.surface.streams/install!))
  ((requiring-resolve 'wandler.surface.streams/install-join!))
  (when-not (kenv/lookup (a/env) (nm "Mode.diff_async_dist"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [box  (box-def)
            zz   (zzero-def)
            _    (doseq [d [box zz]] (swap! a/ansatz-env kenv/check-constant d))
            [ty pf] (prove-diff-async-dist)
            thm  (kenv/mk-thm (nm "Mode.diff_async_dist") [] ty pf)
            _    (swap! a/ansatz-env kenv/check-constant thm)]
        (reset! cache [box zz thm]))))
  (a/env))
