;; Verified finite Map — the computable, invariant-carrying carrier.
;;
;;   Map K V  :=  { l : List (K × V) // NodupKeys l }
;;
;; the standard verified-data-structure design: a computable implementation
;; (an assoc-list under a no-duplicate-keys well-formedness proof) that REFINES
;; the extensional lookup spec. The Subtype computes and extracts to a real
;; Clojure map at the `ansatz->clj` boundary; the carried `.property` proof is a
;; Prop, erased at runtime. Built on Init only (no Mathlib): the foundational
;; `List.Nodup.sublist` / `nodup_cons` / `mem_map` / `mem_filter` lemmas are all
;; present.
;;
;; Generic over ANY `[DecidableEq K]` key type and ANY value type (both Type 0 —
;; covers all practical Clojure data: ints, keywords, strings, records, EDN).
;; Defined idempotently on `install!`:
;;   - Map.keys.{u,v}      K V l : List K  := map Prod.fst l       (universe-poly)
;;   - Map.NodupKeys.{u,v} K V l : Prop     := Nodup (keys l)        (universe-poly)
;;   - Map.{u,v} K V := Subtype (List (K×V)) (Map.NodupKeys K V)     (universe-poly)
;;   - Map.insert_nodupkeys : KERNEL-PROVED preservation theorem
;;       ∀ (K V : Type) (inst : DecidableEq K) (k v l) (h : NodupKeys l),
;;         NodupKeys ((k,v) :: l.filter (fun p => ¬(p.fst == k)))
;;   - Map.empty  : ∀ K V, Map K V                       := ⟨[], nodup_nil⟩
;;   - Map.insert : ∀ K V [DecidableEq K] (k v m), Map K V
;;                  := ⟨(k,v) :: m.val.filter (·.fst≠k), insert_nodupkeys …⟩
;;   - Map.lookup : ∀ K V [DecidableEq K] (k m), Option V := List.lookup k m.val
;;
;; The proof: part_b (keys of the filtered tail is a Sublist of keys l ⇒ Nodup via
;; Nodup.sublist) + part_a (the new key is absent from the filtered tail: mem_map ∘
;; mem_filter ⇒ predtrue ⇒ via `Bool.not_eq_true'` then `of_decide_eq_false`
;; (instBEqOfDecidableEq's beq IS decide, definitionally) ⇒ fst≠k), combined by
;; nodup_cons.mpr ∘ And.intro. grind/simp can't close it — built by hand as a closed
;; term, FVAR-FIRST (outer K/V/inst/k/v/l/h are fvars abstracted at the end via
;; e/abstract1; inner binders p/a/ha/hm use local bvars), which avoids threading 7
;; binders' de Bruijn indices through ~40 positions.

(ns ansatz.kmap
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ z))
(def ^:private type0 (e/sort' L1))                ; Type 0 = Sort 1

;; ---- Map.keys / Map.NodupKeys / Map (universe-polymorphic, level-based) -----

(defn- define-keys! []
  (let [u (nm "u") v (nm "v") lu (lvl/param u) lv (lvl/param v)
        su (e/sort' (lvl/succ lu)) sv (e/sort' (lvl/succ lv)) muv (lvl/level-max lu lv)
        prod-d2 (e/app* (e/const' (nm "Prod") [lu lv]) (e/bvar 1) (e/bvar 0))
        listPair-d2 (e/app (e/const' (nm "List") [muv]) prod-d2)
        ty (e/forall' "K" su (e/forall' "V" sv
             (e/forall' "l" listPair-d2 (e/app (e/const' (nm "List") [lu]) (e/bvar 2)) :default) :default) :default)
        body (e/app* (e/const' (nm "List.map") [muv lu])
                     (e/app* (e/const' (nm "Prod") [lu lv]) (e/bvar 2) (e/bvar 1)) (e/bvar 2)
                     (e/app* (e/const' (nm "Prod.fst") [lu lv]) (e/bvar 2) (e/bvar 1)) (e/bvar 0))
        val (e/lam "K" su (e/lam "V" sv (e/lam "l" listPair-d2 body :default) :default) :default)]
    (kenv/mk-def (nm "Map.keys") [u v] ty val :hints :abbrev)))

(defn- define-nodupkeys! []
  (let [u (nm "u") v (nm "v") lu (lvl/param u) lv (lvl/param v)
        su (e/sort' (lvl/succ lu)) sv (e/sort' (lvl/succ lv)) muv (lvl/level-max lu lv)
        prod-d2 (e/app* (e/const' (nm "Prod") [lu lv]) (e/bvar 1) (e/bvar 0))
        listPair-d2 (e/app (e/const' (nm "List") [muv]) prod-d2)
        ty (e/forall' "K" su (e/forall' "V" sv (e/forall' "l" listPair-d2 (e/sort' z) :default) :default) :default)
        body (e/app* (e/const' (nm "List.Nodup") [lu]) (e/bvar 2)
                     (e/app* (e/const' (nm "Map.keys") [lu lv]) (e/bvar 2) (e/bvar 1) (e/bvar 0)))
        val (e/lam "K" su (e/lam "V" sv (e/lam "l" listPair-d2 body :default) :default) :default)]
    (kenv/mk-def (nm "Map.NodupKeys") [u v] ty val :hints :abbrev)))

(defn- define-map! []
  (let [u (nm "u") v (nm "v") lu (lvl/param u) lv (lvl/param v)
        su (e/sort' (lvl/succ lu)) sv (e/sort' (lvl/succ lv)) muv (lvl/level-max lu lv)
        prod-d2 (e/app* (e/const' (nm "Prod") [lu lv]) (e/bvar 1) (e/bvar 0))
        listPair-d2 (e/app (e/const' (nm "List") [muv]) prod-d2)
        ty (e/forall' "K" su (e/forall' "V" sv (e/sort' (lvl/succ muv)) :default) :default)
        body (e/app* (e/const' (nm "Subtype") [(lvl/succ muv)]) listPair-d2
                     (e/app* (e/const' (nm "Map.NodupKeys") [lu lv]) (e/bvar 1) (e/bvar 0)))
        val (e/lam "K" su (e/lam "V" sv body :default) :default)]
    (kenv/mk-def (nm "Map") [u v] ty val :hints :abbrev)))

;; ---- fvar-first machinery for the generic (Type-0 K V) theorem + ops --------
;; Outer binders are stable fvars; inner binders (pred's p, Exists.elim's a/ha,
;; part_a's hm) use local bvars; e/abstract1 closes the fvars at the end.

(def ^:private fK (e/fvar 90001)) (def ^:private fV (e/fvar 90002)) (def ^:private fI (e/fvar 90003))
(def ^:private fk (e/fvar 90004)) (def ^:private fv (e/fvar 90005)) (def ^:private fl (e/fvar 90006))
(def ^:private fh (e/fvar 90007)) (def ^:private fm (e/fvar 90008))
(def ^:private ff (e/fvar 90009)) (def ^:private fxs (e/fvar 90010))
;; join fvars (K shares fK; X Y kf lf xs ys are join-specific)
(def ^:private jX (e/fvar 91002)) (def ^:private jY (e/fvar 91003))
(def ^:private jkf (e/fvar 91005)) (def ^:private jlf (e/fvar 91006))
(def ^:private jxs (e/fvar 91007)) (def ^:private jys (e/fvar 91008))

(def ^:private prodKV (e/app* (e/const' (nm "Prod") [z z]) fK fV))
(def ^:private fstFn (e/app* (e/const' (nm "Prod.fst") [z z]) fK fV))
(defn- fst- [p] (e/app fstFn p))
(def ^:private beqInst (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fI))
(defn- listOf [t] (e/app (e/const' (nm "List") [z]) t))
(def ^:private listKV (listOf prodKV))
(def ^:private deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK))
(def ^:private ndkPredKV (e/app* (e/const' (nm "Map.NodupKeys") [z z]) fK fV))
(def ^:private mapKV (e/app* (e/const' (nm "Map") [z z]) fK fV))
(defn- keys- [X] (e/app* (e/const' (nm "List.map") [z z]) prodKV fK fstFn X))
(defn- ndk [X] (e/app* (e/const' (nm "Map.NodupKeys") [z z]) fK fV X))
(defn- nodupK [X] (e/app* (e/const' (nm "List.Nodup") [z]) fK X))
(defn- memof [T lst el]
  (e/app* (e/const' (nm "Membership.mem") [z z]) T (listOf T)
          (e/app (e/const' (nm "List.instMembership") [z]) T) lst el))
(defn- eqOf [T x y] (e/app* (e/const' (nm "Eq") [L1]) T x y))
(def ^:private bool-t (e/const' (nm "Bool") []))
(def ^:private true-c (e/const' (nm "Bool.true") []))
(def ^:private false-c (e/const' (nm "Bool.false") []))
(def ^:private boolnot (e/const' (nm "Bool.not") []))
(def ^:private pred
  (e/lam "p" prodKV
    (e/app boolnot (e/app* (e/const' (nm "BEq.beq") [z]) fK beqInst (fst- (e/bvar 0)) fk)) :default))
(def ^:private FL (e/app* (e/const' (nm "List.filter") [z]) prodKV pred fl))
(defn- subval [m] (e/app* (e/const' (nm "Subtype.val") [L1]) listKV ndkPredKV m))
(defn- subprop [m] (e/app* (e/const' (nm "Subtype.property") [L1]) listKV ndkPredKV m))
(def ^:private reflInst                       ; ReflBEq for the DecidableEq-derived BEq
  (e/app* (e/const' (nm "LawfulBEq.toReflBEq") [z]) fK beqInst
          (e/app* (e/const' (nm "instLawfulBEq") [z]) fK fI)))
(def ^:private optV (e/app (e/const' (nm "Option") [z]) fV))
(defn- eqL1 [T x y] (e/app* (e/const' (nm "Eq") [L1]) T x y))

(def ^:private part-b
  (e/app* (e/const' (nm "List.Nodup.sublist") [z]) fK (keys- FL) (keys- fl)
          (e/app* (e/const' (nm "List.Sublist.map") [z z]) prodKV fK fstFn FL fl
                  (e/app* (e/const' (nm "List.filter_sublist") [z]) prodKV pred fl))
          fh))

(def ^:private exPredFn
  (e/lam "a" prodKV
    (e/app* (e/const' (nm "And") []) (memof prodKV FL (e/bvar 0)) (eqOf fK (fst- (e/bvar 0)) fk)) :default))

(def ^:private part-a
  (e/lam "hm" (memof fK (keys- FL) fk)
    (let [exty (e/app* (e/const' (nm "Exists") [L1]) prodKV exPredFn)
          memMap (e/app* (e/const' (nm "List.mem_map") [z z]) prodKV fK fk fstFn FL)
          ex (e/app* (e/const' (nm "Iff.mp") []) (memof fK (keys- FL) fk) exty memMap (e/bvar 0))
          H (e/lam "a" prodKV
              (e/lam "ha" (e/app* (e/const' (nm "And") []) (memof prodKV FL (e/bvar 0)) (eqOf fK (fst- (e/bvar 0)) fk))
                (let [a1 (e/bvar 1) ha (e/bvar 0)
                      mem-a (memof prodKV FL a1)
                      eq-a  (eqOf fK (fst- a1) fk)
                      ha_mem (e/app* (e/const' (nm "And.left") []) mem-a eq-a ha)
                      pa (e/app pred a1)
                      filtRHS (e/app* (e/const' (nm "And") []) (memof prodKV fl a1) (eqOf bool-t pa true-c))
                      filtIff (e/app* (e/const' (nm "List.mem_filter") [z]) prodKV pred fl a1)
                      filt (e/app* (e/const' (nm "Iff.mp") []) (memof prodKV FL a1) filtRHS filtIff ha_mem)
                      predtrue (e/app* (e/const' (nm "And.right") []) (memof prodKV fl a1) (eqOf bool-t pa true-c) filt)
                      c (e/app* (e/const' (nm "BEq.beq") [z]) fK beqInst (fst- a1) fk)
                      cfalse (e/app* (e/const' (nm "Eq.mp") [z])
                                     (eqOf bool-t (e/app boolnot c) true-c) (eqOf bool-t c false-c)
                                     (e/app (e/const' (nm "Bool.not_eq_true'") []) c) predtrue)
                      decinst (e/app* fI (fst- a1) fk)
                      ne (e/app* (e/const' (nm "of_decide_eq_false") []) (eqOf fK (fst- a1) fk) decinst cfalse)
                      ha_eq (e/app* (e/const' (nm "And.right") []) mem-a eq-a ha)]
                  (e/app ne ha_eq)) :default) :default)]
      (e/app* (e/const' (nm "Exists.elim") [L1]) prodKV exPredFn (e/const' (nm "False") []) ex H)) :default))

;; abstract the outer fvars (innermost binder first). `extra` adds binders
;; between l/h and k (here: m for the ops); `klist` is the [name type fvar-id]
;; sequence from innermost to outermost.
(defn- close [mk body klist]
  (reduce (fn [acc [bname btype fid]] (mk bname btype (e/abstract1 acc fid))) body klist))
(defn- lam* [bname btype b] (e/lam bname btype b :default))
(defn- pi*  [bname btype b] (e/forall' bname btype b :default))

;; theorem binders: K V inst k v l h  (innermost = h)
(def ^:private thm-binders
  [["h" (ndk fl) 90007] ["l" listKV 90006] ["v" fV 90005] ["k" fK 90004]
   ["i" deceqK 90003] ["V" type0 90002] ["K" type0 90001]])

(defn- define-insert-thm! []
  (let [proofBody
        (let [klFL (keys- FL)
              A (e/app (e/const' (nm "Not") []) (memof fK klFL fk))
              B (nodupK klFL)
              nodupCons (e/app* (e/const' (nm "List.nodup_cons") [z]) fK fk klFL)
              andv (e/app* (e/const' (nm "And.intro") []) A B part-a part-b)]
          (e/app* (e/const' (nm "Iff.mpr") [])
                  (nodupK (e/app* (e/const' (nm "List.cons") [z]) fK fk klFL))
                  (e/app* (e/const' (nm "And") []) A B) nodupCons andv))
        concl (ndk (e/app* (e/const' (nm "List.cons") [z]) prodKV
                           (e/app* (e/const' (nm "Prod.mk") [z z]) fK fV fk fv) FL))]
    (kenv/mk-def (nm "Map.insert_nodupkeys") []
                 (close pi* concl thm-binders) (close lam* proofBody thm-binders) :hints :opaque)))

;; ---- proof-carrying ops ----------------------------------------------------

(defn- define-empty! []
  (let [bs [["V" type0 90002] ["K" type0 90001]]
        body (e/app* (e/const' (nm "Subtype.mk") [L1]) listKV ndkPredKV
                     (e/app (e/const' (nm "List.nil") [z]) prodKV)
                     (e/app (e/const' (nm "List.nodup_nil") [z]) fK))]
    (kenv/mk-def (nm "Map.empty") [] (close pi* mapKV bs) (close lam* body bs) :hints :opaque)))

(defn- define-insert! []
  ;; binder order (innermost→outermost): m, v, k, inst, V, K
  (let [bs2 [["m" mapKV 90008] ["v" fV 90005] ["k" fK 90004] ["i" deceqK 90003] ["V" type0 90002] ["K" type0 90001]]
        body (e/app* (e/const' (nm "Subtype.mk") [L1]) listKV ndkPredKV
                     (e/app* (e/const' (nm "List.cons") [z]) prodKV
                             (e/app* (e/const' (nm "Prod.mk") [z z]) fK fV fk fv)
                             (e/app* (e/const' (nm "List.filter") [z]) prodKV pred (subval fm)))
                     (e/app* (e/const' (nm "Map.insert_nodupkeys") []) fK fV fI fk fv (subval fm) (subprop fm)))]
    (kenv/mk-def (nm "Map.insert") [] (close pi* mapKV bs2) (close lam* body bs2) :hints :opaque)))

(defn- define-lookup! []
  (let [bs [["m" mapKV 90008] ["k" fK 90004] ["i" deceqK 90003] ["V" type0 90002] ["K" type0 90001]]
        body (e/app* (e/const' (nm "List.lookup") [z z]) fK fV beqInst fk (subval fm))]
    (kenv/mk-def (nm "Map.lookup") [] (close pi* (e/app (e/const' (nm "Option") [z]) fV) bs)
                 (close lam* body bs) :hints :opaque)))

;; ---- group-by (verified BY CONSTRUCTION: foldl of Map.insert) + entries -----

(defn- define-group-by! []
  ;; Map.group_by : ∀ K V [DecidableEq K] (f : V→K) (xs : List V), Map K (List V)
  ;;   := foldl (fun m x => insert (f x) (x :: (lookup (f x) m).getD []) m) empty xs
  ;; reuses Map.insert's proof — no new theorem needed.
  (let [listV (e/app (e/const' (nm "List") [z]) fV)
        mapKLV (e/app* (e/const' (nm "Map") [z z]) fK listV)
        vToK (e/forall' "_" fV fK :default)
        empty- (e/app* (e/const' (nm "Map.empty") []) fK listV)
        step (e/lam "m" mapKLV
               (e/lam "x" fV
                 (let [x (e/bvar 0) m (e/bvar 1) fx (e/app ff x)
                       grp (e/app* (e/const' (nm "Map.lookup") []) fK listV fI fx m)
                       cur (e/app* (e/const' (nm "Option.getD") [z]) listV grp (e/app (e/const' (nm "List.nil") [z]) fV))
                       newg (e/app* (e/const' (nm "List.cons") [z]) fV x cur)]
                   (e/app* (e/const' (nm "Map.insert") []) fK listV fI fx newg m)) :default) :default)
        body (e/app* (e/const' (nm "List.foldl") [z z]) mapKLV fV step empty- fxs)
        bs [["xs" listV 90010] ["f" vToK 90009] ["d" deceqK 90003] ["V" type0 90002] ["K" type0 90001]]]
    (kenv/mk-def (nm "Map.group_by") [] (close pi* mapKLV bs) (close lam* body bs) :hints :opaque)))

(defn- define-entries! []
  ;; Map.entries : ∀ K V, Map K V → List (K×V)  := Subtype.val  (the ->map boundary)
  (let [bs [["m" mapKV 90008] ["V" type0 90002] ["K" type0 90001]]]
    (kenv/mk-def (nm "Map.entries") [] (close pi* listKV bs) (close lam* (subval fm) bs) :hints :opaque)))

(defn- define-join! []
  ;; Map.join : ∀ K X Y [DecidableEq K] (kf:X→K)(lf:Y→K)(xs:List X)(ys:List Y), List (X×Y)
  ;;   := xs.flatMap (fun x => ((lookup (kf x) (group_by lf ys)).getD []).map (fun y => (x,y)))
  ;; verified by construction — composes Map.group_by/Map.lookup, returns a plain List.
  (let [listY (e/app (e/const' (nm "List") [z]) jY)
        prodXY (e/app* (e/const' (nm "Prod") [z z]) jX jY)
        listXY (e/app (e/const' (nm "List") [z]) prodXY)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        xToK (e/forall' "_" jX fK :default)
        yToK (e/forall' "_" jY fK :default)
        grp (e/app* (e/const' (nm "Map.group_by") []) fK jY fI jlf jys)
        innerFn (e/lam "x" jX
                  (let [x (e/bvar 0)
                        key (e/app jkf x)
                        opt (e/app* (e/const' (nm "Map.lookup") []) fK listY fI key grp)
                        matches (e/app* (e/const' (nm "Option.getD") [z]) listY opt
                                        (e/app (e/const' (nm "List.nil") [z]) jY))
                        mapfn (e/lam "y" jY (e/app* (e/const' (nm "Prod.mk") [z z]) jX jY (e/bvar 1) (e/bvar 0)) :default)]
                    (e/app* (e/const' (nm "List.map") [z z]) jY prodXY mapfn matches)) :default)
        body (e/app* (e/const' (nm "List.flatMap") [z z]) jX prodXY innerFn jxs)
        bs [["ys" (e/app (e/const' (nm "List") [z]) jY) 91008]
            ["xs" (e/app (e/const' (nm "List") [z]) jX) 91007]
            ["lf" yToK 91006] ["kf" xToK 91005] ["d" deceqK 90003]
            ["Y" type0 91003] ["X" type0 91002] ["K" type0 90001]]]
    (kenv/mk-def (nm "Map.join") [] (close pi* listXY bs) (close lam* body bs) :hints :opaque)))

;; ---- lookup refinement laws (impl refines the extensional spec) -------------
;; Stated about the underlying construction (= empty.val / insert.val by def).

(defn- define-lookup-empty! []
  ;; lookup k [] = none
  (let [bs [["k" fK 90004] ["i" deceqK 90003] ["V" type0 90002] ["K" type0 90001]]
        nilKV (e/app (e/const' (nm "List.nil") [z]) prodKV)
        lhs (e/app* (e/const' (nm "List.lookup") [z z]) fK fV beqInst fk nilKV)
        stmt (eqL1 optV lhs (e/app (e/const' (nm "Option.none") [z]) fV))
        proof (e/app* (e/const' (nm "List.lookup_nil") [z z]) fK fV fk beqInst)]
    (kenv/mk-def (nm "Map.lookup_empty_eq") [] (close pi* stmt bs) (close lam* proof bs) :hints :opaque)))

;; ============================================================================
;; EXTRINSIC association-list map: AList K V := List (K×V), with NO NodupKeys proof.
;; The operations are plain List-op COMPOSITIONS, so they compose freely (no per-op
;; preservation proof — unlike the intrinsic Subtype-Map). Runtime is a Clojure hash-map
;; (codegen lowers empty→{}, get→get, put→assoc). The map invariant (NodupKeys) is a
;; SEPARATE proposition, established only at a boundary that consumes it as a verified Map.
;; ============================================================================

(defn- define-alist-empty! []
  ;; AList.empty : ∀ (K V : Type), List (K×V)  :=  []
  (let [bs [["V" type0 90002] ["K" type0 90001]]
        body (e/app (e/const' (nm "List.nil") [z]) prodKV)]
    (kenv/mk-def (nm "AList.empty") [] (close pi* listKV bs) (close lam* body bs) :hints :opaque)))

(defn- define-alist-get! []
  ;; AList.get : ∀ (K V : Type) [DecidableEq K], K → V → List(K×V) → V
  ;;   := fun k d l => (List.lookup k l).getD d        (90005 = the default `d`)
  (let [bs [["l" listKV 90006] ["d" fV 90005] ["k" fK 90004]
            ["i" deceqK 90003] ["V" type0 90002] ["K" type0 90001]]
        body (e/app* (e/const' (nm "Option.getD") [z]) fV
                     (e/app* (e/const' (nm "List.lookup") [z z]) fK fV beqInst fk fl)
                     fv)]
    (kenv/mk-def (nm "AList.get") [] (close pi* fV bs) (close lam* body bs) :hints :opaque)))

(defn- define-alist-put! []
  ;; AList.put : ∀ (K V : Type) [DecidableEq K], K → V → List(K×V) → List(K×V)
  ;;   := fun k v l => (k,v) :: l.filter (fun p => ! (p.fst == k))
  (let [pred (e/lam "p" prodKV          ; p = bvar 0 inside (manual de Bruijn, like group-by)
                    (e/app (e/const' (nm "Bool.not") [])
                           (e/app* (e/const' (nm "BEq.beq") [z]) fK beqInst
                                   (e/app* (e/const' (nm "Prod.fst") [z z]) fK fV (e/bvar 0)) fk))
                    :default)
        bs [["l" listKV 90006] ["v" fV 90005] ["k" fK 90004]
            ["i" deceqK 90003] ["V" type0 90002] ["K" type0 90001]]
        body (e/app* (e/const' (nm "List.cons") [z]) prodKV
                     (e/app* (e/const' (nm "Prod.mk") [z z]) fK fV fk fv)
                     (e/app* (e/const' (nm "List.filter") [z]) prodKV pred fl))]
    (kenv/mk-def (nm "AList.put") [] (close pi* listKV bs) (close lam* body bs) :hints :opaque)))

(defn- define-lawful-beq! []
  ;; instLawfulBEqOfDecidableEq : ∀ K [dec:DecidableEq K], LawfulBEq K (instBEqOfDecidableEq K dec)
  ;; The BEq derived from DecidableEq compares via `decide (a = b)`, so its laws are
  ;; the decide lemmas: ReflBEq from `decide_eq_true … rfl`, eq_of_beq from
  ;; `of_decide_eq_true`. Init has the instance's COMPONENTS but not the instance —
  ;; this fills that gap so the Map lookup laws can use beq_iff_eq / beq_eq_false_iff_ne.
  (let [eqK (fn [aa bb] (e/app* (e/const' (nm "Eq") [L1]) fK aa bb))
        refl-proof (e/lam "a" fK
                     (e/app* (e/const' (nm "decide_eq_true") [])
                             (eqK (e/bvar 0) (e/bvar 0))
                             (e/app* fI (e/bvar 0) (e/bvar 0))
                             (e/app* (e/const' (nm "Eq.refl") [L1]) fK (e/bvar 0))) :default)
        reflbeq (e/app* (e/const' (nm "ReflBEq.mk") [z]) fK beqInst refl-proof)
        beqab (fn [aa bb] (e/app* (e/const' (nm "BEq.beq") [z]) fK beqInst aa bb))
        eqofbeq (e/lam "a" fK (e/lam "b" fK
                  (e/lam "h" (e/app* (e/const' (nm "Eq") [L1]) bool-t (beqab (e/bvar 1) (e/bvar 0)) true-c)
                    (e/app* (e/const' (nm "of_decide_eq_true") [])
                            (eqK (e/bvar 2) (e/bvar 1)) (e/app* fI (e/bvar 2) (e/bvar 1)) (e/bvar 0))
                    :default) :default) :default)
        proof (e/app* (e/const' (nm "LawfulBEq.mk") [z]) fK beqInst reflbeq eqofbeq)
        stmt (e/app* (e/const' (nm "LawfulBEq") [z]) fK beqInst)
        bs [["dec" deceqK 90003] ["K" type0 90001]]]
    (kenv/mk-def (nm "instLawfulBEqOfDecidableEq") [] (close pi* stmt bs) (close lam* proof bs) :hints :opaque)))

(defn- define-lookup-insert-head! []
  ;; lookup k ((k,v) :: l.filter (·.fst≠k)) = some v   (= lookup k (insert k v m).val)
  (let [bs [["l" listKV 90006] ["v" fV 90005] ["k" fK 90004] ["i" deceqK 90003] ["V" type0 90002] ["K" type0 90001]]
        consKV (e/app* (e/const' (nm "List.cons") [z]) prodKV
                       (e/app* (e/const' (nm "Prod.mk") [z z]) fK fV fk fv) FL)
        lhs (e/app* (e/const' (nm "List.lookup") [z z]) fK fV beqInst fk consKV)
        stmt (eqL1 optV lhs (e/app* (e/const' (nm "Option.some") [z]) fV fv))
        ;; lookup_cons_self order: K beq V value es refl key
        proof (e/app* (e/const' (nm "List.lookup_cons_self") [z z]) fK beqInst fV fv FL reflInst fk)]
    (kenv/mk-def (nm "Map.lookup_insert_head") [] (close pi* stmt bs) (close lam* proof bs) :hints :opaque)))

(defn install!
  "Define the verified Map (keys/NodupKeys/Map type, the insert-preservation
   theorem, and the generic proof-carrying ops empty/insert/lookup over any
   [DecidableEq K] key + any value) idempotently into the global ansatz env.
   Returns the set of names ensured."
  []
  (let [defs [["Map.keys" define-keys!]
              ["Map.NodupKeys" define-nodupkeys!]
              ["Map" define-map!]
              ["Map.insert_nodupkeys" define-insert-thm!]
              ["Map.empty" define-empty!]
              ["Map.insert" define-insert!]
              ["Map.lookup" define-lookup!]
              ["Map.group_by" define-group-by!]
              ["Map.entries" define-entries!]
              ["Map.join" define-join!]
              ["instLawfulBEqOfDecidableEq" define-lawful-beq!]
              ["Map.lookup_empty_eq" define-lookup-empty!]
              ["Map.lookup_insert_head" define-lookup-insert-head!]
              ["AList.empty" define-alist-empty!]
              ["AList.get" define-alist-get!]
              ["AList.put" define-alist-put!]]]
    (doseq [[n mk] defs]
      (when-not (kenv/lookup @a/ansatz-env (nm n))
        (swap! a/ansatz-env kenv/check-constant (mk))))
    (set (map first defs))))
