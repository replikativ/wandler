(ns ansatz.stream-comonad
  "`Stream A := Nat → A` IS a lawful COMONAD — proven in the kernel. This closes the literal \"not a comonad\"
   part of the comonad/∂ debt (PROGRAMMING_MODEL.md §13; the audit's MISMATCH on `dbsp_stream`'s carrier).

   The exponent/stream comonad `(W, ε, δ)`:
     ε  `Stream.extract`   : W A → A           ε s        = s 0           (the head)
     δ  `Stream.duplicate` : W A → W (W A)      δ s n m    = s (n + m)     (all tails)
        `Stream.map`       : (A→B) → W A → W B  (functor action)
   with the three comonad laws (all by `funext` + `Nat.add_zero`/`zero_add`/`add_assoc`):
     `Stream.comonad_counit_l` : map ε ∘ δ = id      (right counit)
     `Stream.comonad_counit_r` : ε ∘ δ = id          (left counit)
     `Stream.comonad_coassoc`  : δ ∘ δ = map δ ∘ δ    (coassociativity)

   This is the COMONAD STRUCTURE on the same carrier that `ansatz.dbsp-group` gives the differential/group
   structure (D/I) — two structures, one stream type. What this does NOT do (and CANNOT, in plain CIC): the
   GUARDED/CAUSAL refinement — a ▷ (\"later\") modality enforcing productivity so a stream operator can only
   read the past. `Nat → A` lets an operator peek at the whole future (the \"leaky global clock\"); ruling that
   out needs guarded type theory (Nakano/Clouston/Birkedal), a different formal system, not an Init-only proof.
   So: the comonad is DONE; the causal/guarded modality is a foundations question, flagged honestly.
   See [[dbsp-stream-operator-algebra]], [[programming-model-4-structures]], [[modal-mode-lattice]]."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(def ^:private TypeT (e/sort' L1))
(def ^:private natT (e/const' (nm "Nat") []))
(def ^:private nZero (e/const' (nm "Nat.zero") []))
(defn- arrNat [X] (e/forall' "_" natT X :default))
(defn- nadd [a b] (e/app* (e/const' (nm "Nat.add") []) a b))
(defn- eqX [X x y] (e/app* (e/const' (nm "Eq") [L1]) X x y))
(defn- cgX [al be a1 a2 f h] (e/app* (e/const' (nm "congrArg") [L1 L1]) al be a1 a2 f h))
(defn- funX [be f g h] (e/app* (e/const' (nm "funext") [L1 L1]) natT be f g h))

;; ── the comonad operations ───────────────────────────────────────────────────────────────────────
(defn- mk-extract []                ; Stream.extract A s = s 0
  (let [A (e/fvar 1) s (e/fvar 2) sT (arrNat A) body (e/app s nZero)]
    (kenv/mk-def (nm "Stream.extract") []
      (-> A (#(e/forall' "s" sT (e/abstract1 % 2) :default)) (#(e/forall' "A" TypeT (e/abstract1 % 1) :default)))
      (-> body (#(e/lam "s" sT (e/abstract1 % 2) :default)) (#(e/lam "A" TypeT (e/abstract1 % 1) :default))))))

(defn- mk-dup []                     ; Stream.duplicate A s n m = s (n + m)
  (let [A (e/fvar 1) s (e/fvar 2) n (e/fvar 3) m (e/fvar 4) sT (arrNat A) body (e/app s (nadd n m))]
    (kenv/mk-def (nm "Stream.duplicate") []
      (-> A (#(e/forall' "m" natT (e/abstract1 % 4) :default)) (#(e/forall' "n" natT (e/abstract1 % 3) :default))
            (#(e/forall' "s" sT (e/abstract1 % 2) :default)) (#(e/forall' "A" TypeT (e/abstract1 % 1) :default)))
      (-> body (#(e/lam "m" natT (e/abstract1 % 4) :default)) (#(e/lam "n" natT (e/abstract1 % 3) :default))
               (#(e/lam "s" sT (e/abstract1 % 2) :default)) (#(e/lam "A" TypeT (e/abstract1 % 1) :default))))))

(defn- mk-map []                     ; Stream.map A B f s n = f (s n)
  (let [A (e/fvar 1) B (e/fvar 2) f (e/fvar 3) s (e/fvar 4) n (e/fvar 5) fT (e/forall' "_" A B :default) sT (arrNat A) body (e/app f (e/app s n))]
    (kenv/mk-def (nm "Stream.map") []
      (-> B (#(e/forall' "n" natT (e/abstract1 % 5) :default)) (#(e/forall' "s" sT (e/abstract1 % 4) :default))
            (#(e/forall' "f" fT (e/abstract1 % 3) :default)) (#(e/forall' "B" TypeT (e/abstract1 % 2) :default)) (#(e/forall' "A" TypeT (e/abstract1 % 1) :default)))
      (-> body (#(e/lam "n" natT (e/abstract1 % 5) :default)) (#(e/lam "s" sT (e/abstract1 % 4) :default))
               (#(e/lam "f" fT (e/abstract1 % 3) :default)) (#(e/lam "B" TypeT (e/abstract1 % 2) :default)) (#(e/lam "A" TypeT (e/abstract1 % 1) :default))))))

(def ^:private EXT (delay (e/const' (nm "Stream.extract") [])))
(def ^:private DUP (delay (e/const' (nm "Stream.duplicate") [])))
(def ^:private MAP (delay (e/const' (nm "Stream.map") [])))

;; ── the three comonad laws ───────────────────────────────────────────────────────────────────────
(defn- wrap2 [x lamf sT]  ; abstract the two leading binders (A : Type, s : Nat→A)
  (-> x (#(lamf "s" sT (e/abstract1 % 2))) (#(lamf "A" TypeT (e/abstract1 % 1)))))

(defn- prove-counit-l []   ; map (extract A) (duplicate A s) = s   (right counit)
  (let [A (e/fvar 1) s (e/fvar 2) n (e/fvar 3) sT (arrNat A)
        dupAs (e/app* @DUP A s)
        lhs (e/app* @MAP sT A (e/app @EXT A) dupAs)
        hpf (e/lam "n" natT (e/abstract1 (cgX natT A (nadd n nZero) n s (e/app* (e/const' (nm "Nat.add_zero") []) n)) 3) :default)
        pf (funX (e/lam "_" natT A :default) lhs s hpf)]
    [(wrap2 (eqX sT lhs s) (fn [a b c] (e/forall' a b c :default)) sT)
     (wrap2 pf (fn [a b c] (e/lam a b c :default)) sT)]))

(defn- prove-counit-r []   ; extract (Nat→A) (duplicate A s) = s   (left counit)
  (let [A (e/fvar 1) s (e/fvar 2) m (e/fvar 3) sT (arrNat A)
        dupAs (e/app* @DUP A s)
        lhs (e/app* @EXT sT dupAs)
        hpf (e/lam "m" natT (e/abstract1 (cgX natT A (nadd nZero m) m s (e/app* (e/const' (nm "Nat.zero_add") []) m)) 3) :default)
        pf (funX (e/lam "_" natT A :default) lhs s hpf)]
    [(wrap2 (eqX sT lhs s) (fn [a b c] (e/forall' a b c :default)) sT)
     (wrap2 pf (fn [a b c] (e/lam a b c :default)) sT)]))

(defn- prove-coassoc []    ; duplicate (duplicate s) = map duplicate (duplicate s)   (coassociativity)
  (let [A (e/fvar 1) s (e/fvar 2) n (e/fvar 3) m (e/fvar 4) p (e/fvar 5) sT (arrNat A)
        dupAs (e/app* @DUP A s)
        LHS (e/app* @DUP sT dupAs)
        RHS (e/app* @MAP sT (arrNat (arrNat A)) (e/app @DUP A) dupAs)
        congr (cgX natT A (nadd (nadd n m) p) (nadd n (nadd m p)) s (e/app* (e/const' (nm "Nat.add_assoc") []) n m p))
        hp (e/lam "p" natT (e/abstract1 congr 5) :default)
        fp (funX (e/lam "_" natT A :default) (e/app* LHS n m) (e/app* RHS n m) hp)
        hm (e/lam "m" natT (e/abstract1 fp 4) :default)
        fm (funX (e/lam "_" natT (arrNat A) :default) (e/app LHS n) (e/app RHS n) hm)
        hn (e/lam "n" natT (e/abstract1 fm 3) :default)
        fnn (funX (e/lam "_" natT (arrNat (arrNat A)) :default) LHS RHS hn)]
    [(wrap2 (eqX (arrNat (arrNat sT)) LHS RHS) (fn [a b c] (e/forall' a b c :default)) sT)
     (wrap2 fnn (fn [a b c] (e/lam a b c :default)) sT)]))

(defn install!
  "Install the stream comonad (idempotent): `Stream.extract`/`Stream.duplicate`/`Stream.map` and the three
   comonad laws `Stream.comonad_counit_l`/`_counit_r`/`_coassoc`. Every constant is check-constant'd."
  []
  (when-not (kenv/lookup (a/env) (nm "Stream.comonad_coassoc"))
    (let [reg! (fn [ci] (swap! a/ansatz-env kenv/check-constant ci) ci)
          thm! (fn [n pf] (reg! (let [[g p] (pf)] (kenv/mk-thm (nm n) [] g p))))]
      (reg! (mk-extract)) (reg! (mk-dup)) (reg! (mk-map))
      (thm! "Stream.comonad_counit_l" prove-counit-l)
      (thm! "Stream.comonad_counit_r" prove-counit-r)
      (thm! "Stream.comonad_coassoc"  prove-coassoc)))
  (a/env))
