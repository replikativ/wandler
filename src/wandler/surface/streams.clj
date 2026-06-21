(ns wandler.surface.streams
  "SYSTEMATIC tracing of infinite (coinductive) sources through the TYPE. `Strm A := Nat → A` is a
   type DISTINCT from `List A` — so a value's type traces whether it is an infinite stream or a finite
   list, and the surface verbs route on it (no runtime 'is it infinite?' check; it's static).

     (range)                         → `Strm.range : Strm Nat`   (the naturals — an infinite source)
     (map f  <Strm>)                 → `Strm.smap f`             (PRODUCTIVE: one in → one out — allowed)
     (take n <Strm>)                 → `Strm.take n`  : List A    (the WINDOW: Strm → List)
     (reduce / filter <Strm>)        → ERROR 'window an infinite stream with (take n …) first'

   That last gate is the *productivity* discipline made concrete: `map` rides a raw stream (it's a
   guarded corecursion), but `filter`/`reduce`/`join` cannot (they'd consume forever / need the end),
   so the type system forces a `take` (→ List) or incrementalization first. `Strm.take_smap` certifies
   the window commutes: `take n (smap f s) = List.map f (take n s)` — so a windowed stream pipeline
   equals the finite List pipeline, and runs over the infinite source forcing only the window.

   Runtime: a `Strm A` is a Clojure function `Nat → A` (range = identity); `take` materializes n
   (a real lazy seq is adapted by index). See wandler.exec.stream (the coalgebra / `unfold-take` flavour for
   possibly-finite lazy seqs) and wandler.exec.dbsp-stream (the Nat→Int operator algebra)."
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [wandler.clean.surface.common :refer [nm]]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(def ^:private prop (e/sort' z))
(def ^:private natT (e/const' (nm "Nat") []))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- optOf [a] (e/app (e/const' (nm "Option") [z]) a))
(defn- strmOf [a] (e/app (e/const' (nm "Strm") []) a))
(defn- lseqOf [a] (e/app (e/const' (nm "LSeq") []) a))
(defn- mapL [A B f l] (e/app* (e/const' (nm "List.map") [z z]) A B f l))
(defn- eqA [A x y] (e/app* (e/const' (nm "Eq") [L1]) A x y))
(defn- nsucc [t] (e/app (e/const' (nm "Nat.succ") []) t))
(defn- foldlE [A B op i l] (e/app* (e/const' (nm "List.foldl") [z z]) B A op i l))  ; foldl β α op init l
(defn- consE [A x t] (e/app* (e/const' (nm "List.cons") [z]) A x t))
(defn- nilE [A] (e/app (e/const' (nm "List.nil") [z]) A))
(defn- takeE [A n s] (e/app* (e/const' (nm "Strm.take") []) A n s))
(defn- scanE [A B op init s k] (e/app* (e/const' (nm "Strm.scan") []) A B op init s k))
(defn- appE [A xs ys]
  (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) (listOf A) (listOf A) (listOf A)
          (e/app* (e/const' (nm "instHAppendOfAppend") [z]) (listOf A) (e/app (e/const' (nm "List.instAppend") [z]) A))
          xs ys))
;; relational-join helpers (for the bilinear streaming join — reuse Map.join + the DBSP product rule)
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- lengthL [A l] (e/app* (e/const' (nm "List.length") [z]) A l))
(defn- joinL [K X Y dec kf lf xs ys] (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys))
(defn- hadd [a b] (e/app* (e/const' (nm "HAdd.hAdd") [z z z]) natT natT natT
                          (e/app* (e/const' (nm "instHAdd") [z]) natT (e/const' (nm "instAddNat") [])) a b))
(defn- single [A x] (consE A x (nilE A)))

;; <P>.bisim A s t := ∀ n, (s n) = (t n) — pointwise / bisimulation (a Prop). `elem` is the observation
;; type at each index: A for Strm (total), Option A for LSeq (possibly-finite).
(defn- mk-bisim-def [nm-str cOf elem]
  (let [A (e/fvar 1) s (e/fvar 2) t (e/fvar 3)]
    (kenv/mk-def (nm nm-str) []
      (-> prop (#(e/forall' "t" (cOf A) % :default)) (#(e/forall' "s" (cOf A) % :default))
          (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
      (-> (eqA (elem A) (e/app s (e/bvar 0)) (e/app t (e/bvar 0)))
          (#(e/forall' "n" natT % :default))
          (#(e/lam "t" (cOf A) (e/abstract1 % 3) :default))
          (#(e/lam "s" (cOf A) (e/abstract1 % 2) :default))
          (#(e/lam "A" type0 (e/abstract1 % 1) :default))))))

(defn- op-defs []
  (let [A (e/fvar 1)]
    [;; Strm A := Nat → A
     (kenv/mk-def (nm "Strm") [] (e/forall' "A" type0 type0 :default)
       (e/lam "A" type0 (e/forall' "_" natT (e/bvar 1) :default) :default))
     ;; Strm.range : Strm Nat = λn. n
     (kenv/mk-def (nm "Strm.range") [] (strmOf natT) (e/lam "n" natT (e/bvar 0) :default))
     ;; Strm.smap : ∀ A B, (A→B) → Strm A → Strm B = λA B g s n. g (s n)
     (kenv/mk-def (nm "Strm.smap") []
       (-> (e/forall' "_" (strmOf A) (strmOf (e/fvar 2)) :default)
           (#(e/forall' "g" (e/forall' "_" A (e/fvar 2) :default) % :default))
           (#(e/forall' "B" type0 (e/abstract1 % 2) :default))
           (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
       (-> (e/lam "n" natT (e/app (e/fvar 3) (e/app (e/fvar 4) (e/bvar 0))) :default)
           (#(e/lam "s" (strmOf A) (e/abstract1 % 4) :default))
           (#(e/lam "g" (e/forall' "_" A (e/fvar 2) :default) (e/abstract1 % 3) :default))
           (#(e/lam "B" type0 (e/abstract1 % 2) :default))
           (#(e/lam "A" type0 (e/abstract1 % 1) :default))))
     ;; Strm.take : ∀ A, Nat → Strm A → List A = λA n s. List.map s (List.range n)   (the WINDOW)
     (kenv/mk-def (nm "Strm.take") []
       (-> (listOf A) (#(e/forall' "s" (strmOf A) % :default)) (#(e/forall' "n" natT % :default))
           (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
       (-> (mapL natT A (e/fvar 3) (e/app (e/const' (nm "List.range") []) (e/fvar 2)))
           (#(e/lam "s" (strmOf A) (e/abstract1 % 3) :default))
           (#(e/lam "n" natT (e/abstract1 % 2) :default))
           (#(e/lam "A" type0 (e/abstract1 % 1) :default))))
     ;; LSeq A := Nat → Option A — a POSSIBLY-FINITE stream (a real lazy seq / channel / data feed).
     ;; Distinct from both Strm A (total) and List A (finite). `none` marks the end.
     (kenv/mk-def (nm "LSeq") [] (e/forall' "A" type0 type0 :default)
       (e/lam "A" type0 (e/forall' "_" natT (optOf (e/bvar 1)) :default) :default))
     ;; LSeq.smap : ∀ A B, (A→B) → LSeq A → LSeq B = λA B g s n. Option.map g (s n)
     (kenv/mk-def (nm "LSeq.smap") []
       (-> (e/forall' "_" (lseqOf A) (lseqOf (e/fvar 2)) :default)
           (#(e/forall' "g" (e/forall' "_" A (e/fvar 2) :default) % :default))
           (#(e/forall' "B" type0 (e/abstract1 % 2) :default))
           (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
       (-> (e/lam "n" natT (e/app* (e/const' (nm "Option.map") [z z]) A (e/fvar 2) (e/fvar 3) (e/app (e/fvar 4) (e/bvar 0))) :default)
           (#(e/lam "s" (lseqOf A) (e/abstract1 % 4) :default))
           (#(e/lam "g" (e/forall' "_" A (e/fvar 2) :default) (e/abstract1 % 3) :default))
           (#(e/lam "B" type0 (e/abstract1 % 2) :default))
           (#(e/lam "A" type0 (e/abstract1 % 1) :default))))
     ;; LSeq.take : ∀ A, Nat → LSeq A → List A = λA n s. List.filterMap s (List.range n)  (the WINDOW)
     (kenv/mk-def (nm "LSeq.take") []
       (-> (listOf A) (#(e/forall' "s" (lseqOf A) % :default)) (#(e/forall' "n" natT % :default))
           (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
       (-> (e/app* (e/const' (nm "List.filterMap") [z z]) natT A (e/fvar 3) (e/app (e/const' (nm "List.range") []) (e/fvar 2)))
           (#(e/lam "s" (lseqOf A) (e/abstract1 % 3) :default))
           (#(e/lam "n" natT (e/abstract1 % 2) :default))
           (#(e/lam "A" type0 (e/abstract1 % 1) :default))))
     (mk-bisim-def "Strm.bisim" strmOf identity)        ; observe A at each index (total stream)
     (mk-bisim-def "LSeq.bisim" lseqOf optOf)            ; observe Option A (possibly-finite)
     ;; Strm.scan op init s : Strm B = λn. foldl op init (take (n+1) s) — the RUNNING-aggregate stream
     ;; (DBSP's integrate `I` over a monoid step). Each prefix's fold, maintained over time.
     (let [op (e/fvar 3) init (e/fvar 4) s (e/fvar 5)
           opTy (e/forall' "_" (e/fvar 2) (e/forall' "_" A (e/fvar 2) :default) :default)]
       (kenv/mk-def (nm "Strm.scan") []
         (-> (strmOf (e/fvar 2))
             (#(e/forall' "s" (strmOf A) % :default)) (#(e/forall' "init" (e/fvar 2) % :default))
             (#(e/forall' "op" opTy % :default))
             (#(e/forall' "B" type0 (e/abstract1 % 2) :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
         (-> (foldlE A (e/fvar 2) op init (takeE A (nsucc (e/bvar 0)) s))
             (#(e/lam "n" natT % :default))
             (#(e/lam "s" (strmOf A) (e/abstract1 % 5) :default)) (#(e/lam "init" (e/fvar 2) (e/abstract1 % 4) :default))
             (#(e/lam "op" opTy (e/abstract1 % 3) :default))
             (#(e/lam "B" type0 (e/abstract1 % 2) :default)) (#(e/lam "A" type0 (e/abstract1 % 1) :default)))))]))

;; take (succ m) s = take m s ++ [s m]   (via List.range_succ + List.map_append)
(defn- take-succ [A s m]
  (let [rangeM (e/app (e/const' (nm "List.range") []) m)
        rangeSm (e/app (e/const' (nm "List.range") []) (nsucc m))
        appRn (appE natT rangeM (consE natT m (nilE natT)))
        cg (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf natT) (listOf A) rangeSm appRn
                   (e/lam "l" (listOf natT) (mapL natT A s (e/bvar 0)) :default)
                   (e/app (e/const' (nm "List.range_succ") []) m))
        ma (e/app* (e/const' (nm "List.map_append") [z z]) natT A s rangeM (consE natT m (nilE natT)))]
    (e/app* (e/const' (nm "Eq.trans") [L1]) (listOf A)
            (mapL natT A s rangeSm) (mapL natT A s appRn)
            (appE A (mapL natT A s rangeM) (mapL natT A s (consE natT m (nilE natT))))
            cg ma)))

;; Strm.scan_step : scan(succ n) = op (scan n) (s (succ n)) — the O(1) INCREMENTAL recurrence (only the
;; NEW element folded in each step). The DBSP-integrate correctness: incremental update ≡ batch fold.
(defn- prove-scan-step []
  (let [A (e/fvar 1) B (e/fvar 2) op (e/fvar 3) init (e/fvar 4) s (e/fvar 5) n (e/fvar 6)
        opTy (e/forall' "_" B (e/forall' "_" A B :default) :default)
        sSn (e/app s (nsucc n)) takeSn (takeE A (nsucc n) s)
        a1 (takeE A (nsucc (nsucc n)) s) a2 (appE A takeSn (consE A sSn (nilE A)))
        cg (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf A) B a1 a2
                   (e/lam "l" (listOf A) (foldlE A B op init (e/bvar 0)) :default) (take-succ A s (nsucc n)))
        fa (e/app* (e/const' (nm "List.foldl_append") [z z]) A B op init takeSn (consE A sSn (nilE A)))
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) B (foldlE A B op init a1) (foldlE A B op init a2)
                      (foldlE A B op (foldlE A B op init takeSn) (consE A sSn (nilE A))) cg fa)
        ty (-> (eqA B (scanE A B op init s (nsucc n)) (e/app* op (scanE A B op init s n) sSn))
               (#(e/forall' "n" natT (e/abstract1 % 6) :default))
               (#(e/forall' "s" (strmOf A) (e/abstract1 % 5) :default)) (#(e/forall' "init" B (e/abstract1 % 4) :default))
               (#(e/forall' "op" opTy (e/abstract1 % 3) :default))
               (#(e/forall' "B" type0 (e/abstract1 % 2) :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        pf (-> proof
               (#(e/lam "n" natT (e/abstract1 % 6) :default))
               (#(e/lam "s" (strmOf A) (e/abstract1 % 5) :default)) (#(e/lam "init" B (e/abstract1 % 4) :default))
               (#(e/lam "op" opTy (e/abstract1 % 3) :default))
               (#(e/lam "B" type0 (e/abstract1 % 2) :default)) (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    [ty pf]))

(defn prove-take-smap []
  (let [A (e/fvar 1) B (e/fvar 2) g (e/fvar 3) n (e/fvar 4) s (e/fvar 5)
        smapped (e/app* (e/const' (nm "Strm.smap") []) A B g s)
        takeB (fn [strm] (e/app* (e/const' (nm "Strm.take") []) B n strm))
        takeA (e/app* (e/const' (nm "Strm.take") []) A n s)
        rangeN (e/app (e/const' (nm "List.range") []) n)
        mm (e/app* (e/const' (nm "List.map_map") [z z z]) A B natT g s rangeN)
        proof (e/app* (e/const' (nm "Eq.symm") [L1]) (listOf B) (mapL A B g takeA) (takeB smapped) mm)
        concl (e/app* (e/const' (nm "Eq") [L1]) (listOf B) (takeB smapped) (mapL A B g takeA))
        wrap (fn [t mk] (-> t (#(mk "s" (strmOf A) 5 %)) (#(mk "n" natT 4 %))
                            (#(mk "g" (e/forall' "_" A B :default) 3 %)) (#(mk "B" type0 2 %)) (#(mk "A" type0 1 %))))]
    [(wrap concl (fn [n t i b] (e/forall' n t (e/abstract1 b i) :default)))
     (wrap proof (fn [n t i b] (e/lam n t (e/abstract1 b i) :default)))]))

(defn prove-lseq-take-smap []
  (let [A (e/fvar 1) B (e/fvar 2) g (e/fvar 3) n (e/fvar 4) s (e/fvar 5)
        smapped (e/app* (e/const' (nm "LSeq.smap") []) A B g s)
        takeSm (e/app* (e/const' (nm "LSeq.take") []) B n smapped)
        takeS (e/app* (e/const' (nm "LSeq.take") []) A n s)
        mapGtakeS (mapL A B g takeS)
        rangeN (e/app (e/const' (nm "List.range") []) n)
        mm (e/app* (e/const' (nm "List.map_filterMap") [z z z]) natT A B s g rangeN)
        proof (e/app* (e/const' (nm "Eq.symm") [L1]) (listOf B) mapGtakeS takeSm mm)
        concl (e/app* (e/const' (nm "Eq") [L1]) (listOf B) takeSm mapGtakeS)
        wrap (fn [t mk] (-> t (#(mk "s" (lseqOf A) 5 %)) (#(mk "n" natT 4 %))
                            (#(mk "g" (e/forall' "_" A B :default) 3 %)) (#(mk "B" type0 2 %)) (#(mk "A" type0 1 %))))]
    [(wrap concl (fn [n t i b] (e/forall' n t (e/abstract1 b i) :default)))
     (wrap proof (fn [n t i b] (e/lam n t (e/abstract1 b i) :default)))]))

;; ── bisimulation / coinductive equality ─────────────────────────────────────────────────────────
;; <P>.bisim_eq : (∀ n, s n = t n) → s = t  — THE COINDUCTION PRINCIPLE. For the Nat→A reps, two
;; streams are bisimilar iff pointwise-equal, and funext lifts that to genuine equality. `elem` is the
;; per-index observation type (A for Strm, Option A for LSeq).
(defn- prove-bisim-eq [bisimName cOf elem]
  (let [A (e/fvar 1) s (e/fvar 2) t (e/fvar 3) h (e/fvar 4)
        bis (fn [x y] (e/app* (e/const' (nm bisimName) []) A x y))
        ty (-> (eqA (cOf A) s t)
               (#(e/forall' "h" (bis s t) % :default))
               (#(e/forall' "t" (cOf A) (e/abstract1 % 3) :default))
               (#(e/forall' "s" (cOf A) (e/abstract1 % 2) :default))
               (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        pf (-> (e/app* (e/const' (nm "funext") [L1 L1]) natT (e/lam "_" natT (elem A) :default) s t h)
               (#(e/lam "h" (bis s t) (e/abstract1 % 4) :default))
               (#(e/lam "t" (cOf A) (e/abstract1 % 3) :default))
               (#(e/lam "s" (cOf A) (e/abstract1 % 2) :default))
               (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    [ty pf]))

;; <P>.eq_bisim : s = t → ∀ n, s n = t n   (the converse — congrArg at each index)
(defn- prove-eq-bisim [bisimName cOf elem]
  (let [A (e/fvar 1) s (e/fvar 2) t (e/fvar 3) h (e/fvar 4) n (e/fvar 5)
        bis (fn [x y] (e/app* (e/const' (nm bisimName) []) A x y))
        body (e/app* (e/const' (nm "congrArg") [L1 L1]) (cOf A) (elem A) s t
                     (e/lam "f" (cOf A) (e/app (e/bvar 0) n) :default) h)
        ty (-> (bis s t)
               (#(e/forall' "h" (eqA (cOf A) s t) % :default))
               (#(e/forall' "t" (cOf A) (e/abstract1 % 3) :default))
               (#(e/forall' "s" (cOf A) (e/abstract1 % 2) :default))
               (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        pf (-> body
               (#(e/lam "n" natT (e/abstract1 % 5) :default))
               (#(e/lam "h" (eqA (cOf A) s t) (e/abstract1 % 4) :default))
               (#(e/lam "t" (cOf A) (e/abstract1 % 3) :default))
               (#(e/lam "s" (cOf A) (e/abstract1 % 2) :default))
               (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    [ty pf]))

;; DEMO — Strm.smap_congr : (∀x, f x = g x) → smap f s = smap g s.  A genuine STREAM equality (f,g only
;; EXTENSIONALLY equal) proven by COINDUCTION: the pointwise proof (λn. hfg (s n)) lifted via bisim_eq.
(defn- prove-smap-congr []
  (let [A (e/fvar 1) B (e/fvar 2) f (e/fvar 3) g (e/fvar 4) hfg (e/fvar 5) s (e/fvar 6) n (e/fvar 7)
        AB (e/forall' "_" A B :default)
        smapE (fn [h] (e/app* (e/const' (nm "Strm.smap") []) A B h s))
        hfgTy (e/forall' "x" A (eqA B (e/app f (e/bvar 0)) (e/app g (e/bvar 0))) :default)
        ty (-> (eqA (strmOf B) (smapE f) (smapE g))
               (#(e/forall' "s" (strmOf A) (e/abstract1 % 6) :default))
               (#(e/forall' "hfg" hfgTy % :default))
               (#(e/forall' "g" AB (e/abstract1 % 4) :default))
               (#(e/forall' "f" AB (e/abstract1 % 3) :default))
               (#(e/forall' "B" type0 (e/abstract1 % 2) :default))
               (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        pointwise (e/lam "n" natT (e/abstract1 (e/app hfg (e/app s n)) 7) :default)   ; λn. hfg (s n)
        pf (-> (e/app* (e/const' (nm "Strm.bisim_eq") []) B (smapE f) (smapE g) pointwise)
               (#(e/lam "s" (strmOf A) (e/abstract1 % 6) :default))
               (#(e/lam "hfg" hfgTy (e/abstract1 % 5) :default))
               (#(e/lam "g" AB (e/abstract1 % 4) :default))
               (#(e/lam "f" AB (e/abstract1 % 3) :default))
               (#(e/lam "B" type0 (e/abstract1 % 2) :default))
               (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    [ty pf]))

;; ── the BILINEAR streaming join (DBSP differential join) ────────────────────────────────────────
;; Strm.joinCount2 kf lf S T : Strm Nat = λn. |join (take(n+1) S) (take(n+1) T)| — the running join
;; CARDINALITY of two streams (the count keeps it permutation-free).
(defn- jc2-def []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) S (e/fvar 7) T (e/fvar 8)
        XY (prodT X Y)
        body (lengthL XY (joinL K X Y dec kf lf (takeE X (nsucc (e/bvar 0)) S) (takeE Y (nsucc (e/bvar 0)) T)))
        XtoK (e/forall' "_" X K :default) YtoK (e/forall' "_" Y K :default)
        wrap (fn [t mk] (-> t (#(mk "T" (strmOf Y) 8 %)) (#(mk "S" (strmOf X) 7 %)) (#(mk "lf" YtoK 6 %)) (#(mk "kf" XtoK 5 %))
                            (#(mk "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) 4 %))
                            (#(mk "Y" type0 3 %)) (#(mk "X" type0 2 %)) (#(mk "K" type0 1 %))))]
    (kenv/mk-def (nm "Strm.joinCount2") []
      (wrap (strmOf natT) (fn [nme t i bd] (e/forall' nme t (e/abstract1 bd i) :default)))
      (wrap (e/lam "n" natT body :default) (fn [nme t i bd] (e/lam nme t (e/abstract1 bd i) :default))))))

;; Strm.joinCount2_step : the 4-term BILINEAR incremental recurrence (the DBSP differential join):
;;   joinCount2(n+1) = (joinCount2(n) + |[s(n+1)] ⋈ T_n|) + (|S_n ⋈ [t(n+1)]| + |[s(n+1)] ⋈ [t(n+1)]|)
;; = old⋈old + new_x⋈old_y + old_x⋈new_y + new_x⋈new_y. Two take_succ rewrites, then Map.join_count_product.
(defn- prove-jc2-step []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) S (e/fvar 7) T (e/fvar 8) n (e/fvar 9)
        XY (prodT X Y) jf (fn [p b] (lengthL XY (joinL K X Y dec kf lf p b)))
        Sx (e/app S (nsucc n)) Ty (e/app T (nsucc n))
        TSn (takeE X (nsucc n) S) TTn (takeE Y (nsucc n) T)
        a1S (takeE X (nsucc (nsucc n)) S) a2S (appE X TSn (single X Sx))
        a1T (takeE Y (nsucc (nsucc n)) T) a2T (appE Y TTn (single Y Ty))
        cg1 (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf X) natT a1S a2S
                    (e/lam "A" (listOf X) (jf (e/bvar 0) a1T) :default) (take-succ X S (nsucc n)))
        cg2 (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf Y) natT a1T a2T
                    (e/lam "B" (listOf Y) (jf a2S (e/bvar 0)) :default) (take-succ Y T (nsucc n)))
        c12 (e/app* (e/const' (nm "Eq.trans") [L1]) natT (jf a1S a1T) (jf a2S a1T) (jf a2S a2T) cg1 cg2)
        prod (e/app* (e/const' (nm "Map.join_count_product") []) K X Y dec kf lf TSn (single X Sx) TTn (single Y Ty))
        rhs (hadd (hadd (jf TSn TTn) (jf (single X Sx) TTn)) (hadd (jf TSn (single Y Ty)) (jf (single X Sx) (single Y Ty))))
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) natT (jf a1S a1T) (jf a2S a2T) rhs c12 prod)
        XtoK (e/forall' "_" X K :default) YtoK (e/forall' "_" Y K :default)
        jc2 (fn [k] (e/app* (e/const' (nm "Strm.joinCount2") []) K X Y dec kf lf S T k))
        wrap (fn [t mk] (-> t (#(mk "n" natT 9 %)) (#(mk "T" (strmOf Y) 8 %)) (#(mk "S" (strmOf X) 7 %))
                            (#(mk "lf" YtoK 6 %)) (#(mk "kf" XtoK 5 %))
                            (#(mk "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) 4 %))
                            (#(mk "Y" type0 3 %)) (#(mk "X" type0 2 %)) (#(mk "K" type0 1 %))))]
    [(wrap (e/app* (e/const' (nm "Eq") [L1]) natT (jc2 (nsucc n)) rhs) (fn [nme t i bd] (e/forall' nme t (e/abstract1 bd i) :default)))
     (wrap proof (fn [nme t i bd] (e/lam nme t (e/abstract1 bd i) :default)))]))

(declare install!)
(defonce ^:private join-cache (atom nil))
(defn install-join!
  "Admit the BILINEAR streaming join — `Strm.joinCount2` + `Strm.joinCount2_step` (the DBSP differential
   join's 4-term incremental recurrence). Opt-in (needs the relational + DBSP laws); ensures
   kmap/rel-laws/dbsp are installed first. Idempotent."
  []
  ((requiring-resolve 'wandler.kmap/install!))
  ((requiring-resolve 'wandler.clean.laws.faq/install!))
  ((requiring-resolve 'wandler.exec.dbsp/install!))
  (install!)
  (when-not (kenv/lookup (a/env) (nm "Strm.joinCount2_step"))
    (if-let [c @join-cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [d (jc2-def)
            _ (swap! a/ansatz-env kenv/check-constant d)
            [ty pf] (prove-jc2-step)
            st (kenv/mk-thm (nm "Strm.joinCount2_step") [] ty pf)]
        (swap! a/ansatz-env kenv/check-constant st)
        (reset! join-cache [d st]))))
  (a/env))

;; ── the systematic routing: dispatch the surface verbs on Strm / LSeq / List (the TYPE traces it) ─
;; NB: read the type head WITHOUT whnf — `Strm A` is a def that unfolds to `Nat → A`, so whnf would
;; erase the `Strm` head we are trying to detect. The declared/inferred type keeps the `Strm` head.
(defn- type-head [env expr]
  (let [t (a/get-arg-type env nil expr)
        [h _] (when t (e/get-app-fn-args t))]
    (when (e/const? h) (name/->string (e/const-name h)))))

(defn- strm-elem [env strm-expr]
  (let [[_ targs] (e/get-app-fn-args (a/get-arg-type env nil strm-expr))] (first targs)))

(defonce ^{:doc "The pre-routing verb elaborators, captured ONCE (first install). Re-installs
                 (any order vs wandler.clean.surface.collections) reuse these — never wrap a wrapper."}
  originals (atom nil))

(defn- router!
  "Register a stream-routing wrapper for `verb` (tagged so re-installs never wrap a wrapper)."
  [verb f]
  (a/register-term-elaborator! verb (with-meta f {:stream-router true})))

(defn- install-routing! []
  (let [reg @@(requiring-resolve 'ansatz.surface.ingest/term-elaborator-registry)
        captured (select-keys reg '[range map mapv take reduce reductions filter filterv])
        ;; idempotency + order-robustness: capture only entries that are NOT already our
        ;; routers, and merge UNDER previously captured originals — never wrap a wrapper
        fresh (into {} (remove (fn [[_ f]] (:stream-router (meta f))) captured))
        orig (swap! originals (fn [o] (merge fresh o)))]
    ;; (range) with NO args → Strm.range (an infinite source); (range n) stays List.range.
    (router! 'range
      (fn [est args]
        (if (empty? args) (e/const' (nm "Strm.range") [])
            ((orig 'range) est args))))
    ;; map over a Strm/LSeq → smap (productive); else delegate to List.map.
    (doseq [v '[map mapv]]
      (router! v
        (fn [est args]
          (let [[f-form coll-form] args
                coll (api/elab est coll-form)
                kind (#{"Strm" "LSeq"} (type-head (:env est) coll))]
            (if kind
              (let [A (strm-elem (:env est) coll)
                    ;; inject the stream's element type A into the (possibly untyped) map fn — exactly
                    ;; as List.map does — so `(map (fn [v] …) s)` / `(map :k s)` elaborate over a stream.
                    f ((requiring-resolve 'wandler.clean.surface.collections/compile-fn) est f-form [A])
                    B (api/whnf est (e/forall-body (api/arg-type est f)))]   ; map fn's codomain
                (e/app* (e/const' (nm (str kind ".smap")) []) A B f coll))
              ((orig v) est args))))))
    ;; take over a Strm/LSeq → take (the WINDOW, stream → List); else List.take.
    (router! 'take
      (fn [est args]
        (let [[n-form coll-form] args
              coll (api/elab est coll-form)
              kind (#{"Strm" "LSeq"} (type-head (:env est) coll))]
          (if kind
            (e/app* (e/const' (nm (str kind ".take")) []) (strm-elem (:env est) coll)
                    (api/elab est n-form) coll)
            ((orig 'take) est args)))))
    ;; reductions over a Strm → Strm.scan (the INCREMENTAL running aggregate — productive); else scanl.
    (router! 'reductions
      (fn [est args]
        (let [[f-form init-form coll-form] args
              coll (api/elab est coll-form)]
          (if (= "Strm" (type-head (:env est) coll))
            (let [A (strm-elem (:env est) coll)
                  init (api/elab est init-form)
                  B (api/whnf est (api/arg-type est init))
                  f ((requiring-resolve 'wandler.clean.surface.collections/compile-fn) est f-form [B A])]
              (e/app* (e/const' (nm "Strm.scan") []) A B f init coll))
            ((orig 'reductions) est args)))))
    ;; the PRODUCTIVITY GATE: reduce/filter over a raw Strm/LSeq is rejected — window it first.
    (doseq [v '[reduce filter filterv]]
      (router! v
        (fn [est args]
          (let [coll (api/elab est (last args))
                kind (#{"Strm" "LSeq"} (type-head (:env est) coll))]
            (if kind
              (throw (ex-info (str "`" v "` over an infinite " kind " is not productive — window it first "
                                   "with `(take n …)` (stream → List), or incrementalize it (wandler.exec.dbsp).") {:verb v}))
              ((orig v) est args))))))))

(defonce ^:private cache (atom nil))

(defn install!
  "Admit `Strm` (the infinite-stream type) + range/smap/take + `Strm.take_smap`, and ROUTE the surface
   verbs on Strm-vs-List (idempotent). After this, `(range)` is typed `Strm Nat`, `map` over it stays a
   stream, `take` windows it to a `List`, and `reduce`/`filter` over a raw stream are rejected."
  []
  (when-not (kenv/lookup (a/env) (nm "Strm.scan_step"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [defs (op-defs)
            _ (doseq [d defs] (swap! a/ansatz-env kenv/check-constant d))
            thms [["Strm.take_smap" (prove-take-smap)]
                  ["LSeq.take_smap" (prove-lseq-take-smap)]
                  ["Strm.bisim_eq" (prove-bisim-eq "Strm.bisim" strmOf identity)]
                  ["Strm.eq_bisim" (prove-eq-bisim "Strm.bisim" strmOf identity)]
                  ["LSeq.bisim_eq" (prove-bisim-eq "LSeq.bisim" lseqOf optOf)]
                  ["LSeq.eq_bisim" (prove-eq-bisim "LSeq.bisim" lseqOf optOf)]
                  ["Strm.smap_congr" (prove-smap-congr)]
                  ["Strm.scan_step" (prove-scan-step)]]
            cis (mapv (fn [[name [ty pf]]]
                        (let [ci (kenv/mk-thm (nm name) [] ty pf)]
                          (swap! a/ansatz-env kenv/check-constant ci) ci))
                      thms)]
        (reset! cache (into (vec defs) cis)))))
  (install-routing!)
  (a/env))
