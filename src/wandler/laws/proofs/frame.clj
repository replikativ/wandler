(ns wandler.laws.proofs.frame
  "§6 — the FAQ FRAME-RULE + semiring-generalization proof family, split out of wandler.laws.proofs to
   keep that file to the foundational List/Map/Perm/join lemmas. This ns owns the separable-weight frame
   factorization over Map.join and its semiring-generic lift: foldl_const_mul_pull, foldl_add_init,
   cond_and_mul_split, foldl_join_sum_factor, foldl_join_frame, bucket_factor_pull, lookup_reweight,
   keyfactor_float — each as a `_generic` proof over an abstract carrier plus a thin Nat-instantiation
   wrapper — and their `ff-*`/`sf-*` assembly helpers. Registered (generic + Nat) by wandler.laws.relational.
   The few §0 primitives this block needs are duplicated below (trivial const/proof-state builders)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]))

;; ── §0 primitives (duplicated from wandler.laws.proofs — trivial, stable kernel-term builders) ──────
(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(def ^:private boolT (e/const' (nm "Bool") []))
(def ^:private btrue (e/const' (nm "Bool.true") [])) (def ^:private bfalse (e/const' (nm "Bool.false") []))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- new-goals [before after] (vec (remove (set before) after)))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- mapOf [aX aY f l] (e/app* (e/const' (nm "List.map") [z z]) aX aY f l))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- fstOf [X Y p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
(defn- sndOf [X Y p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
(defn- mkP [X Y x y] (e/app* (e/const' (nm "Prod.mk") [z z]) X Y x y))
(defn- beqK [K dec x y] (e/app* (e/const' (nm "BEq.beq") [z]) K (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec) x y))

;; ── §6 frame family (moved verbatim from wandler.laws.proofs) ───────────────────────────────────────
;; ── §6 pre-aggregated index (FAQ) — separable-monoid (SUM) factorization ──────
;; List.foldl_add_init : foldl (λa y. a + g y) acc l = acc + foldl (λa y. a + g y) 0 l.
;; The init-extraction that turns the inner per-bucket fold into a precomputable SUM (independent of
;; the running accumulator) — the algebraic core of the O(distinct-keys) pre-aggregated join index.
;; Proved through basic/induction (acc generalized); the cons case rewrites by the IH at (acc+g h)
;; and (0+g h) and closes the residual Nat identity by add_assoc∘zero_add.
(defn- gh-natT [] (e/const' (nm "Nat") []))
(defn- gh-addN [a b] (e/app* (e/const' (nm "Nat.add") []) a b))
(defn- gh-zeroN [] (e/const' (nm "Nat.zero") []))
(defn- gh-stepfn [Y g] (e/lam "a" (gh-natT) (e/lam "y" Y (gh-addN (e/bvar 1) (e/app g (e/bvar 0))) :default) :default))
(defn- gh-foldlN [Y stp init l] (e/app* (e/const' (nm "List.foldl") [z z]) (gh-natT) Y stp init l))

;; ── List.foldl_add_init (SEMIRING-GENERIC additive-monoid init pull) ──────────────
;; ∀ (S:Type)(add:S→S→S)(zero:S)
;;   (hAA:∀a b c, add (add a b) c = add a (add b c))(hZA:∀a, add zero a = a)(hAZ:∀a, add a zero = a)
;;   (Y:Type)(g:Y→S)(l:List Y)(acc:S),
;;   foldl (λa y. add a (g y)) acc l = add acc (foldl (λa y. add a (g y)) zero l).
;; The init-pull needs exactly the ADDITIVE MONOID (associativity + both identities) — no product, no
;; comm. The Nat law instantiates at (Nat,+,0,Nat.add_assoc,Nat.zero_add,Nat.add_zero).
(defn prove-foldl-add-init-generic []
  (let [S (e/fvar 10) addF (e/fvar 11) zeroF (e/fvar 13) hAA (e/fvar 14) hZA (e/fvar 16) hAZ (e/fvar 17)
        addG (fn [x y] (e/app* addF x y))
        eqS (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) S x y))
        gstepf (fn [Y g] (e/lam "a" S (e/lam "y" Y (addG (e/bvar 1) (e/app g (e/bvar 0))) :default) :default))
        foldlS (fn [Y stp init l] (e/app* (e/const' (nm "List.foldl") [z z]) S Y stp init l))
        hAA-ty (e/forall' "a" S (e/forall' "b" S (e/forall' "c" S
                  (eqS (addG (addG (e/bvar 2) (e/bvar 1)) (e/bvar 0))
                       (addG (e/bvar 2) (addG (e/bvar 1) (e/bvar 0)))) :default) :default) :default)
        hZA-ty (e/forall' "a" S (eqS (addG zeroF (e/bvar 0)) (e/bvar 0)) :default)
        hAZ-ty (e/forall' "a" S (eqS (addG (e/bvar 0) zeroF) (e/bvar 0)) :default)
        arrow (fn [a b] (e/forall' "_" a b :default))
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hAZ" hAZ-ty (e/abstract1 % 17) :default))
                  (#(e/forall' "hZA" hZA-ty (e/abstract1 % 16) :default))
                  (#(e/forall' "hAA" hAA-ty (e/abstract1 % 14) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 13) :default))
                  (#(e/forall' "add" (arrow S (arrow S S)) (e/abstract1 % 11) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 10) :default))))
        Y (e/fvar 1) g (e/fvar 2) l (e/fvar 3) stp (gstepf Y g)
        goal (-> (e/forall' "acc" S
                   (eqS (foldlS Y stp (e/bvar 0) l) (addG (e/bvar 0) (foldlS Y stp zeroF l))) :default)
                 (#(e/forall' "l" (listOf Y) (e/abstract1 % 3) :default))
                 (#(e/forall' "g" (arrow Y S) (e/abstract1 % 2) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 1) :default))
                 sem-pi)
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["S" "add" "zero" "hAA" "hZA" "hAZ" "Y" "g" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cg (proof/current-goal psg)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx cg))]
                (if cons?
                  (let [psg (basic/intros psg ["acc"])
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        ih (e/fvar ihid)
                        Sp (gf psg "S") addp (gf psg "add") zerop (gf psg "zero")
                        haa (gf psg "hAA") hza (gf psg "hZA")
                        ad (fn [x y] (e/app* addp x y))
                        g (gf psg "g") head (gf psg "head") acc (gf psg "acc")
                        Y (gf psg "Y") tail (gf psg "tail")
                        ;; rebuild step/foldl with PROOF-STATE S/add (not the closure's construction-time fvars)
                        stpP (fn [Y g] (e/lam "a" Sp (e/lam "y" Y (ad (e/bvar 1) (e/app g (e/bvar 0))) :default) :default))
                        foldlP (fn [Y stp init l] (e/app* (e/const' (nm "List.foldl") [z z]) Sp Y stp init l))
                        gh (e/app g head) stp (stpP Y g) F (foldlP Y stp zerop tail)
                        q (simp/simp psg ['List.foldl_cons])
                        q (basic/rewrite q (e/app ih (ad acc gh)))
                        q (basic/rewrite q (e/app ih (ad zerop gh)))
                        cgf (fn [fexpr a1 a2 h] (e/app* (e/const' (nm "congrArg") [L1 L1]) Sp Sp a1 a2 fexpr h))
                        addAssoc (e/app* haa acc gh F)
                        zaS (e/app* (e/const' (nm "Eq.symm") [L1]) Sp (ad zerop gh) gh (e/app* hza gh))
                        plusF   (e/lam "w" Sp (ad (e/bvar 0) F) :default)
                        accPlus (e/lam "w" Sp (ad acc (e/bvar 0)) :default)
                        inner (cgf plusF gh (ad zerop gh) zaS)
                        p2    (cgf accPlus (ad gh F) (ad (ad zerop gh) F) inner)
                        result (e/app* (e/const' (nm "Eq.trans") [L1]) Sp
                                       (ad (ad acc gh) F) (ad acc (ad gh F))
                                       (ad acc (ad (ad zerop gh) F)) addAssoc p2)]
                    (basic/exact q result))
                  (let [psg (basic/intros psg ["acc"])
                        Sp (gf psg "S") acc (gf psg "acc") zerop (gf psg "zero") haz (gf psg "hAZ")
                        q (simp/simp psg ['List.foldl_nil])
                        ;; goal now: acc = add acc zero  (RHS inner foldl reduced to zero)
                        symAZ (e/app* (e/const' (nm "Eq.symm") [L1]) Sp (e/app* (gf psg "add") acc zerop) acc
                                      (e/app* haz acc))]
                    (basic/exact q symAZ)))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Nat law: thin instantiation at (Nat,+,0,Nat.add_assoc,Nat.zero_add,Nat.add_zero). Goal byte-identical.
(defn prove-foldl-add-init []
  (let [[_ pGen] (prove-foldl-add-init-generic)
        Y (e/fvar 1) g (e/fvar 2) l (e/fvar 3) stp (gh-stepfn Y g)
        goal (-> (e/forall' "acc" (gh-natT)
                   (e/app* (e/const' (nm "Eq") [L1]) (gh-natT)
                           (gh-foldlN Y stp (e/bvar 0) l)
                           (gh-addN (e/bvar 0) (gh-foldlN Y stp (gh-zeroN) l))) :default)
                 (#(e/forall' "l" (listOf Y) (e/abstract1 % 3) :default))
                 (#(e/forall' "g" (e/forall' "_" Y (gh-natT) :default) (e/abstract1 % 2) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 1) :default)))
        proof (when pGen
                (e/app* pGen (gh-natT) (e/const' (nm "Nat.add") []) (gh-zeroN)
                        (e/const' (nm "Nat.add_assoc") []) (e/const' (nm "Nat.zero_add") [])
                        (e/const' (nm "Nat.add_zero") [])))]
    [goal proof]))

;; List.lookup_map_kv : lookup k (map (λp.(fst p, f(snd p))) l) = Option.map f (lookup k l).
;; The CRUX of the pre-aggregated (FAQ) join index: probing a key/value-mapped assoc list equals
;; mapping the value-fn over the raw probe. Because `Map.lookup k m` def-unfolds to
;; `List.lookup k (Map.entries m)`, this pure-List lemma is exactly what lets us replace per-row
;; bucket folds with one O(distinct-keys) pre-summed index — no Subtype/NodupKeys/map_values.
;; Proof: induction on l; nil = simp[map_nil,lookup_nil]; cons = Prod-eta nudge on the opaque pair
;; (so both lookups reduce by iota) then Bool.casesOn on (k == fst head): true → some(f sp)=Option.map
;; f (some sp) by rfl, false → the IH.
(defn- lk-optionOf [W] (e/app (e/const' (nm "Option") [z]) W))
(defn- lk-someOf [W x] (e/app* (e/const' (nm "Option.some") [z]) W x))
(defn- lk-optionMapOf [V W f o] (e/app* (e/const' (nm "Option.map") [z z]) V W f o))
(defn- lk-beqInst [K inst x y] (e/app* (e/const' (nm "BEq.beq") [z]) K inst x y))
(defn- lk-lookupOf [K V inst k l] (e/app* (e/const' (nm "List.lookup") [z z]) K V inst k l))
(defn- lk-eqAt [ty x y] (e/app* (e/const' (nm "Eq") [L1]) ty x y))
(defn- lk-match1 [motive disc fT fF] (e/app* (e/const' (nm "List.filter.match_1") [L1]) motive disc fT fF))
(def ^:private lk-unitT (e/const' (nm "Unit") []))
(defn- lk-kv-lam [K V W f]
  (e/lam "p" (prodT K V)
         (mkP K W (fstOf K V (e/bvar 0)) (e/app f (sndOf K V (e/bvar 0)))) :default))

(defn prove-lookup-map-kv []
  (let [K (e/fvar 1) V (e/fvar 2) W (e/fvar 3) inst (e/fvar 4) f (e/fvar 5) k (e/fvar 6) l (e/fvar 7)
        kv (lk-kv-lam K V W f)
        concl (lk-eqAt (lk-optionOf W)
                       (lk-lookupOf K W inst k (mapOf (prodT K V) (prodT K W) kv l))
                       (lk-optionMapOf V W f (lk-lookupOf K V inst k l)))
        goal (-> concl
                 (#(e/forall' "l" (listOf (prodT K V)) (e/abstract1 % 7) :default))
                 (#(e/forall' "k" K (e/abstract1 % 6) :default))
                 (#(e/forall' "f" (e/forall' "_" V W :default) (e/abstract1 % 5) :default))
                 (#(e/forall' "inst" (e/app (e/const' (nm "BEq") [z]) K) (e/abstract1 % 4) :default))
                 (#(e/forall' "W" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "V" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "W" "inst" "f" "k" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cg (proof/current-goal psg)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx cg))]
                (if cons?
                  (let [K (gf psg "K") V (gf psg "V") W (gf psg "W")
                        inst (gf psg "inst") f (gf psg "f") k (gf psg "k")
                        head (gf psg "head") tail (gf psg "tail")
                        etaSymm (e/app* (e/const' (nm "Eq.symm") [L1]) (prodT K V)
                                        (mkP K V (fstOf K V head) (sndOf K V head)) head
                                        (e/app* (e/const' (nm "Prod.eta") [z z]) K V head))
                        psg (basic/rewrite psg etaSymm)
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        ih (e/fvar ihid)
                        kv (lk-kv-lam K V W f)
                        fp (fstOf K V head) sp (sndOf K V head)
                        s (lk-beqInst K inst k fp)
                        mappedTail (mapOf (prodT K V) (prodT K W) kv tail)
                        motL (e/lam "b" boolT (lk-optionOf W) :default)
                        motR (e/lam "b" boolT (lk-optionOf V) :default)
                        matchL (fn [b] (lk-match1 motL b
                                         (e/lam "u" lk-unitT (lk-someOf W (e/app f sp)) :default)
                                         (e/lam "u" lk-unitT (lk-lookupOf K W inst k mappedTail) :default)))
                        matchR (fn [b] (lk-match1 motR b
                                         (e/lam "u" lk-unitT (lk-someOf V sp) :default)
                                         (e/lam "u" lk-unitT (lk-lookupOf K V inst k tail) :default)))
                        mu (e/lam "b" boolT
                             (lk-eqAt (lk-optionOf W) (matchL (e/bvar 0))
                                      (lk-optionMapOf V W f (matchR (e/bvar 0)))) :default)
                        trueCase (e/app* (e/const' (nm "Eq.refl") [L1]) (lk-optionOf W) (lk-someOf W (e/app f sp)))
                        casesT (e/app* (e/const' (nm "Bool.casesOn") [z]) mu s ih trueCase)]
                    (basic/exact psg casesT))
                  (simp/simp psg ['List.map_nil 'List.lookup_nil]))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; List.foldl_congr : (∀ b a, f b a = g b a) → foldl f e l = foldl g e l.
;; Pointwise step-function congruence for foldl — lifts a per-element identity through the fold.
;; Proof: induction on l (acc generalized); nil = rfl; cons = congrArg(λw.foldl f w t)(hyp e head) ∘
;; ih (g e head). Reusable; here it lifts the per-bucket pre-agg identity to the whole outer fold.
(defn- sf-arrow [a b] (e/forall' "_" a b :default))
;; gh-foldlN' = foldl over an arbitrary accumulator type (the §6 gh-foldlN is Nat-acc only).
(defn- gh-foldlN' [Acc Elem step init l] (e/app* (e/const' (nm "List.foldl") [z z]) Acc Elem step init l))
(defn prove-foldl-congr []
  (let [Acc (e/fvar 1) Elem (e/fvar 2) f (e/fvar 3) g (e/fvar 4) l (e/fvar 5) e (e/fvar 6)
        hypType (e/forall' "b" Acc
                  (e/forall' "a" Elem
                    (lk-eqAt Acc (e/app* f (e/bvar 1) (e/bvar 0)) (e/app* g (e/bvar 1) (e/bvar 0))) :default) :default)
        concl (e/forall' "h" hypType
                (lk-eqAt Acc (gh-foldlN' Acc Elem f e l) (gh-foldlN' Acc Elem g e l)) :default)
        goal (-> concl
                 (#(e/forall' "e" Acc (e/abstract1 % 6) :default))
                 (#(e/forall' "l" (listOf Elem) (e/abstract1 % 5) :default))
                 (#(e/forall' "g" (sf-arrow Acc (sf-arrow Elem Acc)) (e/abstract1 % 4) :default))
                 (#(e/forall' "f" (sf-arrow Acc (sf-arrow Elem Acc)) (e/abstract1 % 3) :default))
                 (#(e/forall' "Elem" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "Acc" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["Acc" "Elem" "f" "g" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cg (proof/current-goal psg)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx cg))]
                (if cons?
                  (let [psg (basic/intros psg ["e" "h"])
                        Acc (gf psg "Acc") Elem (gf psg "Elem") f (gf psg "f") g (gf psg "g")
                        e (gf psg "e") h (gf psg "h") head (gf psg "head") tail (gf psg "tail")
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        ih (e/fvar ihid)
                        feh (e/app* f e head) geh (e/app* g e head)
                        congrStep (e/app* (e/const' (nm "congrArg") [L1 L1]) Acc Acc feh geh
                                          (e/lam "w" Acc (gh-foldlN' Acc Elem f (e/bvar 0) tail) :default)
                                          (e/app* h e head))
                        ihStep (e/app* ih geh h)
                        result (e/app* (e/const' (nm "Eq.trans") [L1]) Acc
                                       (gh-foldlN' Acc Elem f feh tail)
                                       (gh-foldlN' Acc Elem f geh tail)
                                       (gh-foldlN' Acc Elem g geh tail)
                                       congrStep ihStep)]
                    (basic/exact psg result))
                  (let [psg (basic/intros psg ["e" "h"])
                        Acc (gf psg "Acc") e (gf psg "e")]
                    (basic/exact psg (e/app* (e/const' (nm "Eq.refl") [L1]) Acc e))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.foldl_join_sum_factor : the pre-aggregated (FAQ) join index for SEPARABLE SUM aggregates.
;;   foldl (λacc p. acc + g (snd p)) e (Map.join kf lf xs ys)
;;     = foldl (λacc x. acc + getD (List.lookup (kf x) PREIDX) 0) e xs
;;   where PREIDX = map (λkb. (fst kb, foldl (λa y. a + g y) 0 (snd kb))) (Map.entries (group_by lf ys))
;; The held index is O(distinct keys), not O(|ys|): each bucket is pre-summed once. Assembled from
;; Map.foldl_join_factor (general) ∘ List.foldl_congr with a per-x identity built from foldl_add_init
;; (init-extraction) + lookup_map_kv + Option.getD_map, using Map.lookup ≡ List.lookup∘Map.entries.
(defn- sf-getD [W o d] (e/app* (e/const' (nm "Option.getD") [z]) W o d))
(defn- sf-parts [K X Y dec g kf lf e xs ys]
  (let [LY (listOf Y)
        beq (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        idx (e/app* (e/const' (nm "Map.group_by") []) K Y dec lf ys)
        entries (e/app* (e/const' (nm "Map.entries") []) K LY idx)
        stepAdd (e/lam "a" (gh-natT) (e/lam "y" Y (gh-addN (e/bvar 1) (e/app g (e/bvar 0))) :default) :default)
        bucketSumFn (e/lam "blk" LY (gh-foldlN' (gh-natT) Y stepAdd (gh-zeroN) (e/bvar 0)) :default)
        KV (e/lam "p" (prodT K LY)
             (mkP K (gh-natT) (fstOf K LY (e/bvar 0)) (e/app bucketSumFn (sndOf K LY (e/bvar 0)))) :default)
        preidx (e/app* (e/const' (nm "List.map") [z z]) (prodT K LY) (prodT K (gh-natT)) KV entries)
        op (e/lam "acc" (gh-natT) (e/lam "p" (prodT X Y)
             (gh-addN (e/bvar 1) (e/app g (sndOf X Y (e/bvar 0)))) :default) :default)
        join (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys)
        lhs (gh-foldlN' (gh-natT) (prodT X Y) op e join)
        llookupNat (fn [k] (e/app* (e/const' (nm "List.lookup") [z z]) K (gh-natT) beq k preidx))]
    {:LY LY :beq beq :idx idx :entries entries :stepAdd stepAdd :bucketSumFn bucketSumFn
     :KV KV :preidx preidx :op op :join join :lhs lhs :llookupNat llookupNat}))

(defn- sf-g-outer [K X Y dec g kf lf e xs ys]
  (let [P (sf-parts K X Y dec g kf lf e xs ys)
        af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        body (gh-addN acc (sf-getD (gh-natT) ((:llookupNat P) (e/app kf x)) (gh-zeroN)))]
    (e/lam "acc" (gh-natT) (e/abstract1 (e/lam "x" X (e/abstract1 body xf) :default) af) :default)))

;; the monoid-generic version is defined after the frame block (it reuses sf-parts-g); declared here so
;; the Nat law below can instantiate it.
(declare prove-foldl-join-sum-factor-generic)

(defn prove-foldl-join-sum-factor []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) g (e/fvar 5)
        kf (e/fvar 6) lf (e/fvar 7) e (e/fvar 8) xs (e/fvar 9) ys (e/fvar 10)
        P (sf-parts K X Y dec g kf lf e xs ys)
        concl (lk-eqAt (gh-natT) (:lhs P) (gh-foldlN' (gh-natT) X (sf-g-outer K X Y dec g kf lf e xs ys) e xs))
        goal (-> concl
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 10) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 9) :default))
                 (#(e/forall' "e" (gh-natT) (e/abstract1 % 8) :default))
                 (#(e/forall' "lf" (sf-arrow Y K) (e/abstract1 % 7) :default))
                 (#(e/forall' "kf" (sf-arrow X K) (e/abstract1 % 6) :default))
                 (#(e/forall' "g" (sf-arrow Y (gh-natT)) (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        ;; thin instantiation of the monoid-generic sum-factor at (Nat,+,0). Goal byte-identical.
        [_ pGen] (prove-foldl-join-sum-factor-generic)
        proof (when pGen
                (e/app* pGen (gh-natT) (e/const' (nm "Nat.add") []) (gh-zeroN)
                        (e/const' (nm "Nat.add_assoc") []) (e/const' (nm "Nat.zero_add") [])
                        (e/const' (nm "Nat.add_zero") [])))]
    [goal proof]))

;; ── List.sum_map_mul_const (loop-invariant distributive law) ──────────────────
;; foldl (+) 0 (map (λx. f x * c) xs)  =  (foldl (+) 0 (map f xs)) * c   (c is x-free).
;; The certificate for loop-invariant code motion / 1-variable elimination: a multiplicative
;; factor that does not depend on the fold variable distributes OUT of the sum (the measured
;; O(|xs|·|c-cost|) → O(|xs|) hoist). Proved via the accumulator-GENERALIZED lemma
;;   G : ∀ a, foldl (+) (a*c) (map (λx. f x*c) xs) = (foldl (+) a (map f xs)) * c
;; which inducts cleanly (cons closes by Nat.add_mul + the ∀a IH, no foldl_add_init needed);
;; the a=0 instance + Nat.zero_mul gives the headline form.
(defn- smc-fvidH [ps n]
  (reduce (fn [best [id d]] (if (and (= n (:name d)) (or (nil? best) (> (long id) (long best)))) id best))
          nil (:lctx (proof/current-goal ps))))
(defn- smc-mul [x y] (e/app* (e/const' (nm "Nat.mul") []) x y))
(defn- smc-add [x y] (e/app* (e/const' (nm "Nat.add") []) x y))
(defn- smc-eqN [x y] (e/app* (e/const' (nm "Eq") [L1]) (gh-natT) x y))
(defn- smc-mapN [f l] (e/app* (e/const' (nm "List.map") [z z]) (gh-natT) (gh-natT) f l))
(defn- smc-foldlN [init l] (e/app* (e/const' (nm "List.foldl") [z z]) (gh-natT) (gh-natT) (e/const' (nm "Nat.add") []) init l))
(defn- smc-arrowNN [] (e/forall' "_" (gh-natT) (gh-natT) :default))
(defn- smc-step [f c] (e/lam "x" (gh-natT) (smc-mul (e/app f (e/bvar 0)) c) :default))

(defn prove-sum-map-mul-const []
  (let [;; ── G : the accumulator-generalized lemma ──
        gf1 (e/fvar 1) c1 (e/fvar 2) xs1 (e/fvar 3) a1 (e/fvar 4)
        stepG (smc-step gf1 c1)
        conclG (smc-eqN (smc-foldlN (smc-mul a1 c1) (smc-mapN stepG xs1))
                        (smc-mul (smc-foldlN a1 (smc-mapN gf1 xs1)) c1))
        goalG (-> conclG
                  (#(e/forall' "a"  (gh-natT) (e/abstract1 % 4) :default))
                  (#(e/forall' "xs" (listOf (gh-natT)) (e/abstract1 % 3) :default))
                  (#(e/forall' "c"  (gh-natT) (e/abstract1 % 2) :default))
                  (#(e/forall' "f"  (smc-arrowNN) (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goalG)
        ps (basic/intros ps ["f" "c" "xs"])
        ps (basic/induction ps (fvid ps "xs"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cg  (proof/current-goal psg)
                    cons? (some (fn [[_ d]] (= "tail" (:name d))) (:lctx cg))
                    psg (basic/intros psg ["a"])]
                (if cons?
                  (let [a (gf psg "a") c (gf psg "c") f (gf psg "f") head (gf psg "head")
                        psg (simp/simp psg ['List.map_cons 'List.foldl_cons])
                        addmul (e/app* (e/const' (nm "Nat.add_mul") []) a (e/app f head) c)
                        sym (e/app* (e/const' (nm "Eq.symm") [L1]) (gh-natT)
                                    (smc-mul (smc-add a (e/app f head)) c)
                                    (smc-add (smc-mul a c) (smc-mul (e/app f head) c)) addmul)
                        psg (basic/rewrite psg sym)
                        ih  (e/fvar (or (smc-fvidH psg "ih_tail'") (smc-fvidH psg "ih_tail") (smc-fvidH psg "ih")))]
                    (basic/exact psg (e/app ih (smc-add a (e/app f head)))))
                  (simp/simp psg ['List.map_nil 'List.foldl_nil]))))
            ps (vec (:goals ps)))
        pfG (when (proof/solved? ps) (extract/extract ps))
        ;; ── corollary at a=0 : the headline form ──
        f (e/fvar 1) c (e/fvar 2) xs (e/fvar 3)
        step (smc-step f c)
        zeroN (e/const' (nm "Nat.zero") [])
        lhs0 (smc-foldlN zeroN (smc-mapN step xs))
        rhs0 (smc-mul (smc-foldlN zeroN (smc-mapN f xs)) c)
        goal0 (-> (smc-eqN lhs0 rhs0)
                  (#(e/forall' "xs" (listOf (gh-natT)) (e/abstract1 % 3) :default))
                  (#(e/forall' "c"  (gh-natT) (e/abstract1 % 2) :default))
                  (#(e/forall' "f"  (smc-arrowNN) (e/abstract1 % 1) :default)))
        pf0 (when pfG
              (let [ginst (e/app* pfG f c xs zeroN)
                    zm (e/app* (e/const' (nm "Nat.zero_mul") []) c)
                    zmsym (e/app* (e/const' (nm "Eq.symm") [L1]) (gh-natT) (smc-mul zeroN c) zeroN zm)
                    motive (e/lam "i" (gh-natT) (smc-foldlN (e/bvar 0) (smc-mapN step xs)) :default)
                    coer (e/app* (e/const' (nm "congrArg") [(lvl/succ z) (lvl/succ z)]) (gh-natT) (gh-natT)
                                 zeroN (smc-mul zeroN c) motive zmsym)
                    body (e/app* (e/const' (nm "Eq.trans") [L1]) (gh-natT)
                                 lhs0 (smc-foldlN (smc-mul zeroN c) (smc-mapN step xs)) rhs0 coer ginst)]
                (-> body
                    (#(e/lam "xs" (listOf (gh-natT)) (e/abstract1 % 3) :default))
                    (#(e/lam "c"  (gh-natT) (e/abstract1 % 2) :default))
                    (#(e/lam "f"  (smc-arrowNN) (e/abstract1 % 1) :default)))))]
    [goal0 pf0]))

;; ── sum-semiring LINEARITY laws (the additive structure for FAQ elimination) ──────
;; These are the building blocks the optimizer / e-graph composes for sum-product
;; rewriting: ∑ distributes over +, ∑ of zeros is 0, and a fold's init extracts.
(defn- smc-zero [] (e/const' (nm "Nat.zero") []))

;; List.sum_map_add_distrib : ∀ f g xs a b,
;;   foldl(+) (a+b) (map (λx. f x + g x) xs) = (foldl(+) a (map f xs)) + (foldl(+) b (map g xs))
;; Accumulator-generalized (clean induction); cons closes by Nat.add_add_add_comm + the ∀a∀b IH.
(defn prove-sum-map-add-distrib []
  (let [f (e/fvar 1) g (e/fvar 2) xs (e/fvar 3) a (e/fvar 4) b (e/fvar 5)
        step (e/lam "x" (gh-natT) (smc-add (e/app f (e/bvar 0)) (e/app g (e/bvar 0))) :default)
        concl (smc-eqN (smc-foldlN (smc-add a b) (smc-mapN step xs))
                       (smc-add (smc-foldlN a (smc-mapN f xs)) (smc-foldlN b (smc-mapN g xs))))
        goal (-> concl
                 (#(e/forall' "b" (gh-natT) (e/abstract1 % 5) :default))
                 (#(e/forall' "a" (gh-natT) (e/abstract1 % 4) :default))
                 (#(e/forall' "xs" (listOf (gh-natT)) (e/abstract1 % 3) :default))
                 (#(e/forall' "g" (smc-arrowNN) (e/abstract1 % 2) :default))
                 (#(e/forall' "f" (smc-arrowNN) (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["f" "g" "xs"])
        ps (basic/induction ps (fvid ps "xs"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "tail" (:name d))) (:lctx (proof/current-goal psg)))
                    psg (basic/intros psg ["a" "b"])]
                (if cons?
                  (let [a (gf psg "a") b (gf psg "b") f (gf psg "f") g (gf psg "g") head (gf psg "head")
                        psg (simp/simp psg ['List.map_cons 'List.foldl_cons])
                        fh (e/app f head) gh (e/app g head)
                        arith (e/app* (e/const' (nm "Nat.add_add_add_comm") []) a b fh gh)
                        psg (basic/rewrite psg arith)
                        ih (e/fvar (or (smc-fvidH psg "ih_tail'") (smc-fvidH psg "ih_tail") (smc-fvidH psg "ih")))]
                    (basic/exact psg (e/app* ih (smc-add a fh) (smc-add b gh))))
                  (simp/simp psg ['List.map_nil 'List.foldl_nil]))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; List.sum_map_zero : ∀ ys acc, foldl(+) acc (map (λ_. 0) ys) = acc
(defn prove-sum-map-zero []
  (let [ys (e/fvar 1) acc (e/fvar 2)
        zstep (e/lam "y" (gh-natT) (smc-zero) :default)
        goal (-> (smc-eqN (smc-foldlN acc (smc-mapN zstep ys)) acc)
                 (#(e/forall' "acc" (gh-natT) (e/abstract1 % 2) :default))
                 (#(e/forall' "ys" (listOf (gh-natT)) (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["ys"])
        ps (basic/induction ps (fvid ps "ys"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "tail" (:name d))) (:lctx (proof/current-goal psg)))
                    psg (basic/intros psg ["acc"])]
                (if cons?
                  (let [acc (gf psg "acc")
                        psg (simp/simp psg ['List.map_cons 'List.foldl_cons 'Nat.add_zero])
                        ih (e/fvar (or (smc-fvidH psg "ih_tail'") (smc-fvidH psg "ih_tail") (smc-fvidH psg "ih")))]
                    (basic/exact psg (e/app ih acc)))
                  (simp/simp psg ['List.map_nil 'List.foldl_nil]))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; List.foldl_add_pull : ∀ L acc, foldl(+) acc L = acc + foldl(+) 0 L  (bare-form init extraction)
(defn prove-foldl-add-pull []
  (let [L (e/fvar 1) acc (e/fvar 2)
        goal (-> (smc-eqN (smc-foldlN acc L) (smc-add acc (smc-foldlN (smc-zero) L)))
                 (#(e/forall' "acc" (gh-natT) (e/abstract1 % 2) :default))
                 (#(e/forall' "L" (listOf (gh-natT)) (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["L"])
        ps (basic/induction ps (fvid ps "L"))
        grind (requiring-resolve 'ansatz.tactic.grind/grind)
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "tail" (:name d))) (:lctx (proof/current-goal psg)))
                    psg (basic/intros psg ["acc"])]
                (if cons?
                  (let [acc (gf psg "acc") head (gf psg "head") zeroN (smc-zero)
                        psg (simp/simp psg ['List.foldl_cons])
                        ih (e/fvar (or (smc-fvidH psg "ih_tail'") (smc-fvidH psg "ih_tail") (smc-fvidH psg "ih")))
                        psg (basic/rewrite psg (e/app ih (smc-add acc head)))
                        psg (basic/rewrite psg (e/app ih (smc-add zeroN head)))]
                    (grind psg []))
                  (simp/simp psg ['List.foldl_nil 'Nat.add_zero]))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── List.sum_map_const_mul (left-invariant mirror of sum_map_mul_const) ────────────
;; foldl(+) 0 (map (λx. c * f x) xs)  =  c * (foldl(+) 0 (map f xs)).  The invariant on the
;; LEFT of the product. Same accumulator-generalized shape; cons closes by Nat.mul_add (left
;; distributivity) and the a=0 corollary by Nat.mul_zero.
(defn- smc-step-left [c f] (e/lam "x" (gh-natT) (smc-mul c (e/app f (e/bvar 0))) :default))

(defn prove-sum-map-const-mul []
  (let [gf1 (e/fvar 1) c1 (e/fvar 2) xs1 (e/fvar 3) a1 (e/fvar 4)
        stepG (smc-step-left c1 gf1)
        conclG (smc-eqN (smc-foldlN (smc-mul c1 a1) (smc-mapN stepG xs1))
                        (smc-mul c1 (smc-foldlN a1 (smc-mapN gf1 xs1))))
        goalG (-> conclG
                  (#(e/forall' "a"  (gh-natT) (e/abstract1 % 4) :default))
                  (#(e/forall' "xs" (listOf (gh-natT)) (e/abstract1 % 3) :default))
                  (#(e/forall' "c"  (gh-natT) (e/abstract1 % 2) :default))
                  (#(e/forall' "f"  (smc-arrowNN) (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goalG)
        ps (basic/intros ps ["f" "c" "xs"])
        ps (basic/induction ps (fvid ps "xs"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "tail" (:name d))) (:lctx (proof/current-goal psg)))
                    psg (basic/intros psg ["a"])]
                (if cons?
                  (let [a (gf psg "a") c (gf psg "c") f (gf psg "f") head (gf psg "head")
                        psg (simp/simp psg ['List.map_cons 'List.foldl_cons])
                        muladd (e/app* (e/const' (nm "Nat.mul_add") []) c a (e/app f head))
                        sym (e/app* (e/const' (nm "Eq.symm") [L1]) (gh-natT)
                                    (smc-mul c (smc-add a (e/app f head)))
                                    (smc-add (smc-mul c a) (smc-mul c (e/app f head))) muladd)
                        psg (basic/rewrite psg sym)
                        ih (e/fvar (or (smc-fvidH psg "ih_tail'") (smc-fvidH psg "ih_tail") (smc-fvidH psg "ih")))]
                    (basic/exact psg (e/app ih (smc-add a (e/app f head)))))
                  (simp/simp psg ['List.map_nil 'List.foldl_nil]))))
            ps (vec (:goals ps)))
        pfG (when (proof/solved? ps) (extract/extract ps))
        f (e/fvar 1) c (e/fvar 2) xs (e/fvar 3)
        step (smc-step-left c f) zeroN (e/const' (nm "Nat.zero") [])
        lhs0 (smc-foldlN zeroN (smc-mapN step xs))
        rhs0 (smc-mul c (smc-foldlN zeroN (smc-mapN f xs)))
        goal0 (-> (smc-eqN lhs0 rhs0)
                  (#(e/forall' "xs" (listOf (gh-natT)) (e/abstract1 % 3) :default))
                  (#(e/forall' "c"  (gh-natT) (e/abstract1 % 2) :default))
                  (#(e/forall' "f"  (smc-arrowNN) (e/abstract1 % 1) :default)))
        pf0 (when pfG
              (let [ginst (e/app* pfG f c xs zeroN)
                    mz (e/app* (e/const' (nm "Nat.mul_zero") []) c)
                    mzsym (e/app* (e/const' (nm "Eq.symm") [L1]) (gh-natT) (smc-mul c zeroN) zeroN mz)
                    motive (e/lam "i" (gh-natT) (smc-foldlN (e/bvar 0) (smc-mapN step xs)) :default)
                    coer (e/app* (e/const' (nm "congrArg") [(lvl/succ z) (lvl/succ z)]) (gh-natT) (gh-natT)
                                 zeroN (smc-mul c zeroN) motive mzsym)
                    body (e/app* (e/const' (nm "Eq.trans") [L1]) (gh-natT)
                                 lhs0 (smc-foldlN (smc-mul c zeroN) (smc-mapN step xs)) rhs0 coer ginst)]
                (-> body
                    (#(e/lam "xs" (listOf (gh-natT)) (e/abstract1 % 3) :default))
                    (#(e/lam "c"  (gh-natT) (e/abstract1 % 2) :default))
                    (#(e/lam "f"  (smc-arrowNN) (e/abstract1 % 1) :default)))))]
    [goal0 pf0]))

;; ── List.foldl_const_mul_pull (polymorphic foldl-form const-factor pull) ──────────
;; foldl (λa y. a + c·(g y)) 0 l  =  c · foldl (λa y. a + g y) 0 l   (c is loop-invariant).
;; The element-POLYMORPHIC, foldl-form sibling of List.sum_map_const_mul (which is Nat→Nat,
;; List Nat only). Needed by the FAQ frame rule: a bucket is `List Y` with weight `g : Y → Nat`,
;; so the Nat-only sum_map_const_mul does not apply. Same accumulator-generalized induction:
;;   G : ∀ a, foldl (λp y. p + c·g y) (c·a) l = c · foldl (λp y. p + g y) a l
;; cons closes by Nat.mul_add (left distributivity) + the ∀a IH; the a=0 instance + Nat.mul_zero
;; gives the headline. (No map round-trip — directly in foldl form.)
;; ── List.foldl_const_mul_pull_generic (SEMIRING-GENERIC product-pull) ─────────────
;; ∀ (S:Type)(add mul:S→S→S)(zero:S)
;;   (hMA:∀a b c, mul a (add b c) = add (mul a b) (mul a c))   -- LEFT distributivity
;;   (hMZ:∀a, mul a zero = zero)                               -- right annihilator
;;   (α:Type)(c:S)(g:α→S)(l:List α),
;;   foldl (λa y. add a (mul c (g y))) zero l = mul c (foldl (λa y. add a (g y)) zero l).
;; This lemma carries ALL of the value-algebra of the FAQ frame rule's product-pull step — and it needs
;; ONLY a `·` that left-distributes over `+` and annihilates the additive zero, i.e. ANY semiring (no
;; commutativity, no associativity, no multiplicative identity). The Nat law below is its instantiation
;; at (Nat,+,·,0,Nat.mul_add,Nat.mul_zero); the SAME proof term certifies Bool, tropical, Float-trusted,
;; … semirings. The induction/rewrite skeleton is type-generic (only List.foldl_cons/nil + the two
;; hypotheses fire) — see the PoC note in [[faq-variable-elimination]]. Returns the FULLY-quantified
;; (sem-params included) [goal proof]; the Nat law instantiates the proof term directly.
(defn prove-foldl-const-mul-pull-generic []
  (let [S (e/fvar 10) addF (e/fvar 11) mulF (e/fvar 12) zeroF (e/fvar 13) hMA (e/fvar 14) hMZ (e/fvar 15)
        addG (fn [x y] (e/app* addF x y)) mulG (fn [x y] (e/app* mulF x y))
        eqS (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) S x y))
        foldlS (fn [stp init l alpha] (e/app* (e/const' (nm "List.foldl") [z z]) S alpha stp init l))
        cstepf (fn [c g alpha] (e/lam "a" S (e/lam "y" alpha (addG (e/bvar 1) (mulG c (e/app g (e/bvar 0)))) :default) :default))
        gstepf (fn [g alpha] (e/lam "a" S (e/lam "y" alpha (addG (e/bvar 1) (e/app g (e/bvar 0))) :default) :default))
        ;; the semiring-parameter telescope (S add mul zero hMA hMZ), S outermost — shared by goal & proof
        hMZ-ty (e/forall' "a" S (eqS (mulG (e/bvar 0) zeroF) zeroF) :default)
        hMA-ty (e/forall' "a" S (e/forall' "b" S (e/forall' "c" S
                  (eqS (mulG (e/bvar 2) (addG (e/bvar 1) (e/bvar 0)))
                       (addG (mulG (e/bvar 2) (e/bvar 1)) (mulG (e/bvar 2) (e/bvar 0)))) :default) :default) :default)
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/forall' "hMA" hMA-ty (e/abstract1 % 14) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 13) :default))
                  (#(e/forall' "mul" (sf-arrow S (sf-arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/forall' "add" (sf-arrow S (sf-arrow S S)) (e/abstract1 % 11) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 10) :default))))
        sem-lam (fn [t] (-> t
                  (#(e/lam "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/lam "hMA" hMA-ty (e/abstract1 % 14) :default))
                  (#(e/lam "zero" S (e/abstract1 % 13) :default))
                  (#(e/lam "mul" (sf-arrow S (sf-arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/lam "add" (sf-arrow S (sf-arrow S S)) (e/abstract1 % 11) :default))
                  (#(e/lam "S" type0 (e/abstract1 % 10) :default))))
        ;; ---- G (accumulator-generalized), proved by induction on l ----
        alpha (e/fvar 1) c1 (e/fvar 2) g1 (e/fvar 3) l1 (e/fvar 4) a1 (e/fvar 5)
        conclG (eqS (foldlS (cstepf c1 g1 alpha) (mulG c1 a1) l1 alpha)
                    (mulG c1 (foldlS (gstepf g1 alpha) a1 l1 alpha)))
        goalG (-> conclG
                  (#(e/forall' "a"  S (e/abstract1 % 5) :default))
                  (#(e/forall' "l"  (listOf alpha) (e/abstract1 % 4) :default))
                  (#(e/forall' "g"  (sf-arrow alpha S) (e/abstract1 % 3) :default))
                  (#(e/forall' "c"  S (e/abstract1 % 2) :default))
                  (#(e/forall' "α"  type0 (e/abstract1 % 1) :default))
                  sem-pi)
        [ps _] (proof/start-proof (a/env) goalG)
        ps (basic/intros ps ["S" "add" "mul" "zero" "hMA" "hMZ" "α" "c" "g" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "tail" (:name d))) (:lctx (proof/current-goal psg)))
                    psg (basic/intros psg ["a"])]
                (if cons?
                  (let [Sp (gf psg "S") a (gf psg "a") c (gf psg "c") g (gf psg "g") head (gf psg "head")
                        addp (gf psg "add") mulp (gf psg "mul") hma (gf psg "hMA")
                        ad (fn [x y] (e/app* addp x y)) mu (fn [x y] (e/app* mulp x y))
                        psg (simp/simp psg ['List.foldl_cons])
                        gh (e/app g head)
                        ;; c·(a+gh) = c·a + c·gh ; rewrite the accumulator c·a + c·gh ← c·(a+gh)
                        muladd (e/app* hma c a gh)
                        sym (e/app* (e/const' (nm "Eq.symm") [L1]) Sp
                                    (mu c (ad a gh)) (ad (mu c a) (mu c gh)) muladd)
                        psg (basic/rewrite psg sym)
                        ih (e/fvar (or (smc-fvidH psg "ih_tail'") (smc-fvidH psg "ih_tail") (smc-fvidH psg "ih")))]
                    (basic/exact psg (e/app ih (ad a gh))))
                  (simp/simp psg ['List.foldl_nil]))))
            ps (vec (:goals ps)))
        pfG (when (proof/solved? ps) (extract/extract ps))
        ;; ---- headline at a := zero (generic) ----
        alpha (e/fvar 1) c (e/fvar 2) g (e/fvar 3) l (e/fvar 4)
        cstep (cstepf c g alpha) gstep (gstepf g alpha)
        lhs0 (foldlS cstep zeroF l alpha)
        rhs0 (mulG c (foldlS gstep zeroF l alpha))
        goal0 (-> (eqS lhs0 rhs0)
                  (#(e/forall' "l" (listOf alpha) (e/abstract1 % 4) :default))
                  (#(e/forall' "g" (sf-arrow alpha S) (e/abstract1 % 3) :default))
                  (#(e/forall' "c" S (e/abstract1 % 2) :default))
                  (#(e/forall' "α" type0 (e/abstract1 % 1) :default))
                  sem-pi)
        pf0 (when pfG
              (let [ginst (e/app* pfG S addF mulF zeroF hMA hMZ alpha c g l zeroF) ; foldl cstep (c·0) l = c·foldl gstep 0 l
                    mz (e/app* hMZ c)                                              ; c·0 = 0
                    mzsym (e/app* (e/const' (nm "Eq.symm") [L1]) S (mulG c zeroF) zeroF mz)  ; 0 = c·0
                    motive (e/lam "i" S (foldlS cstep (e/bvar 0) l alpha) :default)
                    coer (e/app* (e/const' (nm "congrArg") [L1 L1]) S S
                                 zeroF (mulG c zeroF) motive mzsym)                ; foldl cstep 0 l = foldl cstep (c·0) l
                    body (e/app* (e/const' (nm "Eq.trans") [L1]) S
                                 lhs0 (foldlS cstep (mulG c zeroF) l alpha) rhs0 coer ginst)]
                (-> body
                    (#(e/lam "l" (listOf alpha) (e/abstract1 % 4) :default))
                    (#(e/lam "g" (sf-arrow alpha S) (e/abstract1 % 3) :default))
                    (#(e/lam "c" S (e/abstract1 % 2) :default))
                    (#(e/lam "α" type0 (e/abstract1 % 1) :default))
                    sem-lam)))]
    [goal0 pf0]))

;; The Nat law (registered as List.foldl_const_mul_pull, consumed by the frame proof) is now a thin
;; INSTANTIATION of the semiring-generic lemma at (Nat,+,·,0,Nat.mul_add,Nat.mul_zero). The goal is
;; byte-identical to the previous Nat-specific construction; only the proof term changed (it is the
;; generic proof applied to the Nat semiring witnesses), so all downstream consumers are unaffected.
(defn prove-foldl-const-mul-pull []
  (let [[_ pGen] (prove-foldl-const-mul-pull-generic)
        alpha (e/fvar 1) c (e/fvar 2) g (e/fvar 3) l (e/fvar 4) zeroN (gh-zeroN)
        cstepf (fn [c g] (e/lam "a" (gh-natT)
                           (e/lam "y" alpha (gh-addN (e/bvar 1) (smc-mul c (e/app g (e/bvar 0)))) :default) :default))
        gstepf (fn [g] (gh-stepfn alpha g))
        cstep (cstepf c g) gstep (gstepf g)
        lhs0 (gh-foldlN alpha cstep zeroN l)
        rhs0 (smc-mul c (gh-foldlN alpha gstep zeroN l))
        goal0 (-> (smc-eqN lhs0 rhs0)
                  (#(e/forall' "l" (listOf alpha) (e/abstract1 % 4) :default))
                  (#(e/forall' "g" (sf-arrow alpha (gh-natT)) (e/abstract1 % 3) :default))
                  (#(e/forall' "c" (gh-natT) (e/abstract1 % 2) :default))
                  (#(e/forall' "α" type0 (e/abstract1 % 1) :default)))
        pf0 (when pGen
              (e/app* pGen (gh-natT) (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.mul") []) (gh-zeroN)
                      (e/const' (nm "Nat.mul_add") []) (e/const' (nm "Nat.mul_zero") [])))]
    [goal0 pf0]))

;; ── Map.foldl_join_frame (the FAQ FRAME RULE — two-sided separable weight) ────────
;; foldl (λacc p. acc + (f (fst p)) · (g (snd p))) e (Map.join kf lf xs ys)
;;   = foldl (λacc x. acc + (f x) · getD (lookup (kf x) PREIDX) 0) e xs
;; where PREIDX is the SAME g-only O(distinct-keys) pre-aggregated index as Map.foldl_join_sum_factor.
;; This GENERALIZES Map.foldl_join_sum_factor (its f≡1 instance): the FRAME separates the x-side weight
;; `f x` from the pre-summed y-side `Σ g`. It is the aggregation frame rule — the SPN/FAQ "product node"
;; expressed over Map.join: Σ_{x⋈y} f(x)·g(y) = Σ_x f(x)·(Σ_{y∈bucket(x)} g(y)). Same assembly as
;; foldl_join_sum_factor (Map.foldl_join_factor ∘ List.foldl_congr), with the per-x identity splicing
;; the f(x)-extraction (List.foldl_const_mul_pull) between foldl_add_init and the preAgg rewrite.
(defn- ff-op [X Y f g]
  (e/lam "acc" (gh-natT)
    (e/lam "p" (prodT X Y)
      (gh-addN (e/bvar 1) (smc-mul (e/app f (fstOf X Y (e/bvar 0)))
                                   (e/app g (sndOf X Y (e/bvar 0))))) :default) :default))

(defn- ff-parts [K X Y dec f g kf lf e xs ys]
  (let [P (sf-parts K X Y dec g kf lf e xs ys)        ; g-only preidx/idx/entries/bucketSumFn/llookupNat
        op (ff-op X Y f g)]
    (assoc P :op op :lhs (gh-foldlN' (gh-natT) (prodT X Y) op e (:join P)))))

(defn- ff-g-outer [K X Y dec f g kf lf e xs ys]
  (let [P (ff-parts K X Y dec f g kf lf e xs ys)
        af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        body (gh-addN acc (smc-mul (e/app f x)
                                   (sf-getD (gh-natT) ((:llookupNat P) (e/app kf x)) (gh-zeroN))))]
    (e/lam "acc" (gh-natT) (e/abstract1 (e/lam "x" X (e/abstract1 body xf) :default) af) :default)))

;; ── SEMIRING-GENERIC frame rule ──────────────────────────────────────────────────
;; The whole frame proof is pure structural plumbing over the three generic leaves
;; (foldl_add_init_generic, foldl_const_mul_pull_generic) plus value-type-generic lemmas
;; (Map.foldl_join_factor, List.foldl_congr, List.lookup_map_kv, Option.map/getD_map). The generic
;; variants thread a semiring context sr = {S, add, mul, zero, hAA, hZA, hAZ, hMA, hMZ} (a left-
;; distributive semiring: additive monoid + left-distrib + two-sided annihilator) where the Nat versions
;; hardcode Nat. Built after `intros`, so every term uses proof-state fvars — no construction-vs-state mix.
(defn- ff-op-g [sr X Y f g]
  (let [{:keys [S addF mulF]} sr
        addG (fn [a b] (e/app* addF a b)) mulG (fn [a b] (e/app* mulF a b))]
    (e/lam "acc" S (e/lam "p" (prodT X Y)
      (addG (e/bvar 1) (mulG (e/app f (fstOf X Y (e/bvar 0))) (e/app g (sndOf X Y (e/bvar 0))))) :default) :default)))

(defn- sf-parts-g [sr K X Y dec g kf lf e xs ys]
  (let [{:keys [S addF zeroF]} sr
        addG (fn [a b] (e/app* addF a b))
        gfold (fn [Elem step init l] (e/app* (e/const' (nm "List.foldl") [z z]) S Elem step init l))
        LY (listOf Y)
        beq (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        idx (e/app* (e/const' (nm "Map.group_by") []) K Y dec lf ys)
        entries (e/app* (e/const' (nm "Map.entries") []) K LY idx)
        stepAdd (e/lam "a" S (e/lam "y" Y (addG (e/bvar 1) (e/app g (e/bvar 0))) :default) :default)
        bucketSumFn (e/lam "blk" LY (gfold Y stepAdd zeroF (e/bvar 0)) :default)
        KV (e/lam "p" (prodT K LY)
             (mkP K S (fstOf K LY (e/bvar 0)) (e/app bucketSumFn (sndOf K LY (e/bvar 0)))) :default)
        preidx (e/app* (e/const' (nm "List.map") [z z]) (prodT K LY) (prodT K S) KV entries)
        op (e/lam "acc" S (e/lam "p" (prodT X Y)
             (addG (e/bvar 1) (e/app g (sndOf X Y (e/bvar 0)))) :default) :default)
        join (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys)
        lhs (gfold (prodT X Y) op e join)
        llookup (fn [k] (e/app* (e/const' (nm "List.lookup") [z z]) K S beq k preidx))]
    {:LY LY :beq beq :idx idx :entries entries :stepAdd stepAdd :bucketSumFn bucketSumFn
     :KV KV :preidx preidx :op op :join join :lhs lhs :llookupNat llookup}))

(defn- ff-parts-g [sr K X Y dec f g kf lf e xs ys]
  (let [{:keys [S]} sr
        P (sf-parts-g sr K X Y dec g kf lf e xs ys)
        op (ff-op-g sr X Y f g)]
    (assoc P :op op :lhs (e/app* (e/const' (nm "List.foldl") [z z]) S (prodT X Y) op e (:join P)))))

(defn- ff-f-outer-g [sr K X Y dec f g kf lf e xs ys]
  (let [{:keys [S]} sr
        P (ff-parts-g sr K X Y dec f g kf lf e xs ys)
        af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        BKT (sf-getD (:LY P) (e/app* (e/const' (nm "Map.lookup") []) K (:LY P) dec (e/app kf x) (:idx P)) (nilOf Y))
        innerStep (e/lam "a" S (e/lam "y" Y (e/app* (:op P) (e/bvar 1) (mkP X Y x (e/bvar 0))) :default) :default)
        body (e/app* (e/const' (nm "List.foldl") [z z]) S Y innerStep acc BKT)]
    (e/lam "acc" S (e/abstract1 (e/lam "x" X (e/abstract1 body xf) :default) af) :default)))

(defn- ff-g-outer-g [sr K X Y dec f g kf lf e xs ys]
  (let [{:keys [S addF mulF zeroF]} sr
        addG (fn [a b] (e/app* addF a b)) mulG (fn [a b] (e/app* mulF a b))
        P (ff-parts-g sr K X Y dec f g kf lf e xs ys)
        af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        body (addG acc (mulG (e/app f x) (sf-getD S ((:llookupNat P) (e/app kf x)) zeroF)))]
    (e/lam "acc" S (e/abstract1 (e/lam "x" X (e/abstract1 body xf) :default) af) :default)))

(defn- ff-hyp-g [sr K X Y dec f g kf lf e xs ys]
  (let [{:keys [S addF mulF zeroF hAA hZA hAZ hMA hMZ]} sr
        addG (fn [a b] (e/app* addF a b)) mulG (fn [a b] (e/app* mulF a b))
        gfold (fn [Elem step init l] (e/app* (e/const' (nm "List.foldl") [z z]) S Elem step init l))
        P (ff-parts-g sr K X Y dec f g kf lf e xs ys)
        LY (:LY P) af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        kfx (e/app kf x) fx (e/app f x)
        BKT (sf-getD LY (e/app* (e/const' (nm "Map.lookup") []) K LY dec kfx (:idx P)) (nilOf Y))
        h (e/lam "y" Y (mulG fx (e/app g (e/bvar 0))) :default)
        hstep (e/lam "a" S (e/lam "y" Y (addG (e/bvar 1) (mulG fx (e/app g (e/bvar 0)))) :default) :default)
        bsBKT (gfold Y (:stepAdd P) zeroF BKT)
        hBKT0 (gfold Y hstep zeroF BKT)
        addInitEq (e/app* (e/const' (nm "List.foldl_add_init_generic") []) S addF zeroF hAA hZA hAZ Y h BKT acc)
        pull (e/app* (e/const' (nm "List.foldl_const_mul_pull_generic") []) S addF mulF zeroF hMA hMZ Y fx g BKT)
        Oprime (e/app* (e/const' (nm "List.lookup") [z z]) K LY (:beq P) kfx (:entries P))
        lmkv (e/app* (e/const' (nm "List.lookup_map_kv") []) K LY S (:beq P) (:bucketSumFn P) kfx (:entries P))
        optMapB (fn [o] (e/app* (e/const' (nm "Option.map") [z z]) LY S (:bucketSumFn P) o))
        lookPre ((:llookupNat P) kfx)
        optS (e/app (e/const' (nm "Option") [z]) S)
        getDNfn (e/lam "o" optS (sf-getD S (e/bvar 0) zeroF) :default)
        congGetD (e/app* (e/const' (nm "congrArg") [L1 L1]) optS S lookPre (optMapB Oprime) getDNfn lmkv)
        getdMap (e/app* (e/const' (nm "Option.getD_map") [z z]) LY S (:bucketSumFn P) (nilOf Y) Oprime)
        targetRHS (sf-getD S lookPre zeroF)
        presumQ (e/app* (e/const' (nm "Eq.trans") [L1]) S
                        targetRHS (sf-getD S (optMapB Oprime) zeroF) bsBKT congGetD getdMap)
        symPresum (e/app* (e/const' (nm "Eq.symm") [L1]) S targetRHS bsBKT presumQ)
        mulFx (e/lam "w" S (mulG fx (e/bvar 0)) :default)
        congMulPresum (e/app* (e/const' (nm "congrArg") [L1 L1]) S S bsBKT targetRHS mulFx symPresum)
        hBKT0ToFxTarget (e/app* (e/const' (nm "Eq.trans") [L1]) S
                                hBKT0 (mulG fx bsBKT) (mulG fx targetRHS) pull congMulPresum)
        accPlus (e/lam "w" S (addG acc (e/bvar 0)) :default)
        congAcc (e/app* (e/const' (nm "congrArg") [L1 L1]) S S hBKT0 (mulG fx targetRHS) accPlus hBKT0ToFxTarget)
        proofBody (e/app* (e/const' (nm "Eq.trans") [L1]) S
                          (gfold Y hstep acc BKT) (addG acc hBKT0) (addG acc (mulG fx targetRHS))
                          addInitEq congAcc)]
    (e/lam "acc" S (e/abstract1 (e/lam "x" X (e/abstract1 proofBody xf) :default) af) :default)))

(defn prove-foldl-join-frame-generic []
  (let [S (e/fvar 20) addF (e/fvar 21) mulF (e/fvar 22) zeroF (e/fvar 23)
        arrow (fn [a b] (e/forall' "_" a b :default))
        addG (fn [a b] (e/app* addF a b)) mulG (fn [a b] (e/app* mulF a b))
        eqS (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) S x y))
        hAA-ty (e/forall' "a" S (e/forall' "b" S (e/forall' "c" S
                  (eqS (addG (addG (e/bvar 2) (e/bvar 1)) (e/bvar 0))
                       (addG (e/bvar 2) (addG (e/bvar 1) (e/bvar 0)))) :default) :default) :default)
        hZA-ty (e/forall' "a" S (eqS (addG zeroF (e/bvar 0)) (e/bvar 0)) :default)
        hAZ-ty (e/forall' "a" S (eqS (addG (e/bvar 0) zeroF) (e/bvar 0)) :default)
        hMA-ty (e/forall' "a" S (e/forall' "b" S (e/forall' "c" S
                  (eqS (mulG (e/bvar 2) (addG (e/bvar 1) (e/bvar 0)))
                       (addG (mulG (e/bvar 2) (e/bvar 1)) (mulG (e/bvar 2) (e/bvar 0)))) :default) :default) :default)
        hMZ-ty (e/forall' "a" S (eqS (mulG (e/bvar 0) zeroF) zeroF) :default)
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hMZ" hMZ-ty (e/abstract1 % 28) :default))
                  (#(e/forall' "hMA" hMA-ty (e/abstract1 % 27) :default))
                  (#(e/forall' "hAZ" hAZ-ty (e/abstract1 % 26) :default))
                  (#(e/forall' "hZA" hZA-ty (e/abstract1 % 25) :default))
                  (#(e/forall' "hAA" hAA-ty (e/abstract1 % 24) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 23) :default))
                  (#(e/forall' "mul" (arrow S (arrow S S)) (e/abstract1 % 22) :default))
                  (#(e/forall' "add" (arrow S (arrow S S)) (e/abstract1 % 21) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 20) :default))))
        sr0 {:S S :addF addF :mulF mulF :zeroF zeroF}
        K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) f (e/fvar 5) g (e/fvar 6)
        kf (e/fvar 7) lf (e/fvar 8) e (e/fvar 9) xs (e/fvar 10) ys (e/fvar 11)
        P (ff-parts-g sr0 K X Y dec f g kf lf e xs ys)
        concl (eqS (:lhs P) (e/app* (e/const' (nm "List.foldl") [z z]) S X
                              (ff-g-outer-g sr0 K X Y dec f g kf lf e xs ys) e xs))
        goal (-> concl
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 11) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 10) :default))
                 (#(e/forall' "e" S (e/abstract1 % 9) :default))
                 (#(e/forall' "lf" (arrow Y K) (e/abstract1 % 8) :default))
                 (#(e/forall' "kf" (arrow X K) (e/abstract1 % 7) :default))
                 (#(e/forall' "g" (arrow Y S) (e/abstract1 % 6) :default))
                 (#(e/forall' "f" (arrow X S) (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default))
                 sem-pi)
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["S" "add" "mul" "zero" "hAA" "hZA" "hAZ" "hMA" "hMZ"
                             "K" "X" "Y" "dec" "f" "g" "kf" "lf" "e" "xs" "ys"])
        sr {:S (gf ps "S") :addF (gf ps "add") :mulF (gf ps "mul") :zeroF (gf ps "zero")
            :hAA (gf ps "hAA") :hZA (gf ps "hZA") :hAZ (gf ps "hAZ") :hMA (gf ps "hMA") :hMZ (gf ps "hMZ")}
        Sp (:S sr)
        K (gf ps "K") X (gf ps "X") Y (gf ps "Y") dec (gf ps "dec") f (gf ps "f") g (gf ps "g")
        kf (gf ps "kf") lf (gf ps "lf") e (gf ps "e") xs (gf ps "xs") ys (gf ps "ys")
        P (ff-parts-g sr K X Y dec f g kf lf e xs ys)
        f-outer (ff-f-outer-g sr K X Y dec f g kf lf e xs ys)
        g-outer (ff-g-outer-g sr K X Y dec f g kf lf e xs ys)
        hyp (ff-hyp-g sr K X Y dec f g kf lf e xs ys)
        gfold (fn [Elem step init l] (e/app* (e/const' (nm "List.foldl") [z z]) Sp Elem step init l))
        factorEq (e/app* (e/const' (nm "Map.foldl_join_factor") []) K X Y Sp dec (:op P) e kf lf xs ys)
        congrEq (e/app* (e/const' (nm "List.foldl_congr") []) Sp X f-outer g-outer xs e hyp)
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) Sp (:lhs P)
                      (gfold X f-outer e xs) (gfold X g-outer e xs) factorEq congrEq)
        ps (basic/exact ps proof)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── MONOID-GENERIC SUM factorization (the f≡1 sibling of the frame) ───────────────
;; The pre-aggregated SUM index needs only an ADDITIVE MONOID (no product), so its generic carries just
;; (S,add,zero) + add_assoc + both identities. Reuses sf-parts-g (g-only op/index machinery).
(defn- sf-g-outer-g [srm K X Y dec g kf lf e xs ys]
  (let [{:keys [S addF zeroF]} srm
        addG (fn [a b] (e/app* addF a b))
        P (sf-parts-g srm K X Y dec g kf lf e xs ys)
        af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        body (addG acc (sf-getD S ((:llookupNat P) (e/app kf x)) zeroF))]
    (e/lam "acc" S (e/abstract1 (e/lam "x" X (e/abstract1 body xf) :default) af) :default)))

(defn- sf-f-outer-g [srm K X Y dec g kf lf e xs ys]
  (let [{:keys [S]} srm
        P (sf-parts-g srm K X Y dec g kf lf e xs ys)
        af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        BKT (sf-getD (:LY P) (e/app* (e/const' (nm "Map.lookup") []) K (:LY P) dec (e/app kf x) (:idx P)) (nilOf Y))
        innerStep (e/lam "a" S (e/lam "y" Y (e/app* (:op P) (e/bvar 1) (mkP X Y x (e/bvar 0))) :default) :default)
        body (e/app* (e/const' (nm "List.foldl") [z z]) S Y innerStep acc BKT)]
    (e/lam "acc" S (e/abstract1 (e/lam "x" X (e/abstract1 body xf) :default) af) :default)))

(defn- sf-hyp-g [srm K X Y dec g kf lf e xs ys]
  (let [{:keys [S addF zeroF hAA hZA hAZ]} srm
        addG (fn [a b] (e/app* addF a b))
        gfold (fn [Elem step init l] (e/app* (e/const' (nm "List.foldl") [z z]) S Elem step init l))
        P (sf-parts-g srm K X Y dec g kf lf e xs ys)
        LY (:LY P) af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        kfx (e/app kf x)
        BKT (sf-getD LY (e/app* (e/const' (nm "Map.lookup") []) K LY dec kfx (:idx P)) (nilOf Y))
        bsBKT (gfold Y (:stepAdd P) zeroF BKT)
        addInitEq (e/app* (e/const' (nm "List.foldl_add_init_generic") []) S addF zeroF hAA hZA hAZ Y g BKT acc)
        Oprime (e/app* (e/const' (nm "List.lookup") [z z]) K LY (:beq P) kfx (:entries P))
        lmkv (e/app* (e/const' (nm "List.lookup_map_kv") []) K LY S (:beq P) (:bucketSumFn P) kfx (:entries P))
        optMapB (fn [o] (e/app* (e/const' (nm "Option.map") [z z]) LY S (:bucketSumFn P) o))
        lookPre ((:llookupNat P) kfx)
        optS (e/app (e/const' (nm "Option") [z]) S)
        getDNfn (e/lam "o" optS (sf-getD S (e/bvar 0) zeroF) :default)
        congGetD (e/app* (e/const' (nm "congrArg") [L1 L1]) optS S lookPre (optMapB Oprime) getDNfn lmkv)
        getdMap (e/app* (e/const' (nm "Option.getD_map") [z z]) LY S (:bucketSumFn P) (nilOf Y) Oprime)
        targetRHS (sf-getD S lookPre zeroF)
        presumQ (e/app* (e/const' (nm "Eq.trans") [L1]) S
                        targetRHS (sf-getD S (optMapB Oprime) zeroF) bsBKT congGetD getdMap)
        symPresum (e/app* (e/const' (nm "Eq.symm") [L1]) S targetRHS bsBKT presumQ)
        addAccFn (e/lam "w" S (addG acc (e/bvar 0)) :default)
        congAdd (e/app* (e/const' (nm "congrArg") [L1 L1]) S S bsBKT targetRHS addAccFn symPresum)
        proofBody (e/app* (e/const' (nm "Eq.trans") [L1]) S
                          (gfold Y (:stepAdd P) acc BKT) (addG acc bsBKT) (addG acc targetRHS) addInitEq congAdd)]
    (e/lam "acc" S (e/abstract1 (e/lam "x" X (e/abstract1 proofBody xf) :default) af) :default)))

(defn prove-foldl-join-sum-factor-generic []
  (let [S (e/fvar 20) addF (e/fvar 21) zeroF (e/fvar 23)
        arrow (fn [a b] (e/forall' "_" a b :default))
        addG (fn [a b] (e/app* addF a b))
        eqS (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) S x y))
        hAA-ty (e/forall' "a" S (e/forall' "b" S (e/forall' "c" S
                  (eqS (addG (addG (e/bvar 2) (e/bvar 1)) (e/bvar 0))
                       (addG (e/bvar 2) (addG (e/bvar 1) (e/bvar 0)))) :default) :default) :default)
        hZA-ty (e/forall' "a" S (eqS (addG zeroF (e/bvar 0)) (e/bvar 0)) :default)
        hAZ-ty (e/forall' "a" S (eqS (addG (e/bvar 0) zeroF) (e/bvar 0)) :default)
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hAZ" hAZ-ty (e/abstract1 % 26) :default))
                  (#(e/forall' "hZA" hZA-ty (e/abstract1 % 25) :default))
                  (#(e/forall' "hAA" hAA-ty (e/abstract1 % 24) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 23) :default))
                  (#(e/forall' "add" (arrow S (arrow S S)) (e/abstract1 % 21) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 20) :default))))
        srm0 {:S S :addF addF :zeroF zeroF}
        K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) g (e/fvar 5)
        kf (e/fvar 6) lf (e/fvar 7) e (e/fvar 8) xs (e/fvar 9) ys (e/fvar 10)
        P (sf-parts-g srm0 K X Y dec g kf lf e xs ys)
        concl (eqS (:lhs P) (e/app* (e/const' (nm "List.foldl") [z z]) S X
                              (sf-g-outer-g srm0 K X Y dec g kf lf e xs ys) e xs))
        goal (-> concl
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 10) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 9) :default))
                 (#(e/forall' "e" S (e/abstract1 % 8) :default))
                 (#(e/forall' "lf" (arrow Y K) (e/abstract1 % 7) :default))
                 (#(e/forall' "kf" (arrow X K) (e/abstract1 % 6) :default))
                 (#(e/forall' "g" (arrow Y S) (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default))
                 sem-pi)
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["S" "add" "zero" "hAA" "hZA" "hAZ"
                             "K" "X" "Y" "dec" "g" "kf" "lf" "e" "xs" "ys"])
        srm {:S (gf ps "S") :addF (gf ps "add") :zeroF (gf ps "zero")
             :hAA (gf ps "hAA") :hZA (gf ps "hZA") :hAZ (gf ps "hAZ")}
        Sp (:S srm)
        K (gf ps "K") X (gf ps "X") Y (gf ps "Y") dec (gf ps "dec") g (gf ps "g")
        kf (gf ps "kf") lf (gf ps "lf") e (gf ps "e") xs (gf ps "xs") ys (gf ps "ys")
        P (sf-parts-g srm K X Y dec g kf lf e xs ys)
        f-outer (sf-f-outer-g srm K X Y dec g kf lf e xs ys)
        g-outer (sf-g-outer-g srm K X Y dec g kf lf e xs ys)
        hyp (sf-hyp-g srm K X Y dec g kf lf e xs ys)
        gfold (fn [Elem step init l] (e/app* (e/const' (nm "List.foldl") [z z]) Sp Elem step init l))
        factorEq (e/app* (e/const' (nm "Map.foldl_join_factor") []) K X Y Sp dec (:op P) e kf lf xs ys)
        congrEq (e/app* (e/const' (nm "List.foldl_congr") []) Sp X f-outer g-outer xs e hyp)
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) Sp (:lhs P)
                      (gfold X f-outer e xs) (gfold X g-outer e xs) factorEq congrEq)
        ps (basic/exact ps proof)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-foldl-join-frame []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) f (e/fvar 5) g (e/fvar 6)
        kf (e/fvar 7) lf (e/fvar 8) e (e/fvar 9) xs (e/fvar 10) ys (e/fvar 11)
        P (ff-parts K X Y dec f g kf lf e xs ys)
        concl (lk-eqAt (gh-natT) (:lhs P) (gh-foldlN' (gh-natT) X (ff-g-outer K X Y dec f g kf lf e xs ys) e xs))
        goal (-> concl
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 11) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 10) :default))
                 (#(e/forall' "e" (gh-natT) (e/abstract1 % 9) :default))
                 (#(e/forall' "lf" (sf-arrow Y K) (e/abstract1 % 8) :default))
                 (#(e/forall' "kf" (sf-arrow X K) (e/abstract1 % 7) :default))
                 (#(e/forall' "g" (sf-arrow Y (gh-natT)) (e/abstract1 % 6) :default))
                 (#(e/forall' "f" (sf-arrow X (gh-natT)) (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        ;; thin instantiation of the semiring-generic frame at the Nat semiring; goal byte-identical.
        [_ pGen] (prove-foldl-join-frame-generic)
        proof (when pGen
                (e/app* pGen (gh-natT) (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.mul") []) (gh-zeroN)
                        (e/const' (nm "Nat.add_assoc") []) (e/const' (nm "Nat.zero_add") []) (e/const' (nm "Nat.add_zero") [])
                        (e/const' (nm "Nat.mul_add") []) (e/const' (nm "Nat.mul_zero") [])))]
    [goal proof]))

;; ── Nat.cond_and_mul_split (CONDITIONAL SEPARATION — the dependent-types win) ─────
;; cond (a && b) (u·v) 0  =  (cond a u 0) · (cond b v 0)   for a,b : Bool, u,v : Nat.
;; A SEPARABLE conjunctive guard `P(x) ∧ Q(y)` factors a weighted product into per-side guarded
;; weights: indicator(P∧Q)·f(x)·g(y) = (indicator(P)·f(x)) · (indicator(Q)·g(y)). This is exactly
;; what makes a CONDITIONAL aggregation separable — once split, f' = [P]·f and g' = [Q]·g are each
;; closed, so the FAQ frame rule (Map.foldl_join_frame) fires. The Subtype/refined-domain view: a join
;; filtered by a separable predicate factors as a product of independently-filtered sides.
;; Proof: nested Bool.casesOn (a, then b). Because Nat.mul recurses on its SECOND arg, `_·0 ≡ 0`,
;; `cond false`, and `Bool.and false` all reduce DEFINITIONALLY — so 3 of 4 leaves are Eq.refl and only
;; the a=false,b=true leaf (0 = 0·v) needs Nat.zero_mul. The casesOn motive is Prop ⇒ level 0.
;; ── Nat.cond_and_mul_split (SEMIRING-GENERIC conditional split) ───────────────────
;; ∀ (S:Type)(mul:S→S→S)(zero:S)(hZM:∀v, mul zero v = zero)(hMZ:∀u, mul u zero = zero)(a b:Bool)(u v:S),
;;   cond (a && b) (mul u v) zero = mul (cond a u zero) (cond b v zero).
;; The conditional-guard separation needs ONLY a two-sided annihilator (mul zero v = zero = mul u zero) —
;; the rest is Bool case analysis + cond/and reduction. The Nat law hid BOTH annihilators behind Nat.mul's
;; definitional computation (the refl leaves typecheck because Nat.mul u 0 / Nat.mul 0 0 compute to 0); over
;; an abstract mul they become explicit hypotheses. Nat law below instantiates at (Nat,·,0,zero_mul,mul_zero).
(defn prove-cond-and-mul-split-generic []
  (let [S (e/fvar 10) mulF (e/fvar 12) zeroF (e/fvar 13) hZM (e/fvar 16) hMZ (e/fvar 15)
        mulG (fn [x y] (e/app* mulF x y))
        condS (fn [c x y] (e/app* (e/const' (nm "cond") [L1]) S c x y))
        andB  (fn [x y] (e/app* (e/const' (nm "Bool.and") []) x y))
        eqS (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) S x y))
        reflS (fn [x] (e/app* (e/const' (nm "Eq.refl") [L1]) S x))
        symS (fn [x y h] (e/app* (e/const' (nm "Eq.symm") [L1]) S x y h))
        hZM-ty (e/forall' "v" S (eqS (mulG zeroF (e/bvar 0)) zeroF) :default)
        hMZ-ty (e/forall' "u" S (eqS (mulG (e/bvar 0) zeroF) zeroF) :default)
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/forall' "hZM" hZM-ty (e/abstract1 % 16) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 13) :default))
                  (#(e/forall' "mul" (sf-arrow S (sf-arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 10) :default))))
        sem-lam (fn [t] (-> t
                  (#(e/lam "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/lam "hZM" hZM-ty (e/abstract1 % 16) :default))
                  (#(e/lam "zero" S (e/abstract1 % 13) :default))
                  (#(e/lam "mul" (sf-arrow S (sf-arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/lam "S" type0 (e/abstract1 % 10) :default))))
        a (e/fvar 1) b (e/fvar 2) u (e/fvar 3) v (e/fvar 4)
        concl (eqS (condS (andB a b) (mulG u v) zeroF)
                   (mulG (condS a u zeroF) (condS b v zeroF)))
        goal (-> concl
                 (#(e/forall' "v" S (e/abstract1 % 4) :default))
                 (#(e/forall' "u" S (e/abstract1 % 3) :default))
                 (#(e/forall' "b" boolT (e/abstract1 % 2) :default))
                 (#(e/forall' "a" boolT (e/abstract1 % 1) :default))
                 sem-pi)
        mot-a (e/lam "a'" boolT
                (eqS (condS (andB (e/bvar 0) b) (mulG u v) zeroF)
                     (mulG (condS (e/bvar 0) u zeroF) (condS b v zeroF))) :default)
        mot-b (fn [aLit] (e/lam "b'" boolT
                 (eqS (condS (andB aLit (e/bvar 0)) (mulG u v) zeroF)
                      (mulG (condS aLit u zeroF) (condS (e/bvar 0) v zeroF))) :default))
        bcases (fn [mot major mfalse mtrue]
                 (e/app* (e/const' (nm "Bool.casesOn") [z]) mot major mfalse mtrue))
        leaf-ff (symS (mulG zeroF zeroF) zeroF (e/app* hZM zeroF))   ; zero = mul zero zero
        leaf-ft (symS (mulG zeroF v)     zeroF (e/app* hZM v))       ; zero = mul zero v
        leaf-tf (symS (mulG u zeroF)     zeroF (e/app* hMZ u))       ; zero = mul u zero
        leaf-tt (reflS (mulG u v))                                   ; mul u v = mul u v
        branch-F (bcases (mot-b bfalse) b leaf-ff leaf-ft)           ; a=F: (F,F)→mul0,0  (F,T)→zero_mul
        branch-T (bcases (mot-b btrue)  b leaf-tf leaf-tt)           ; a=T: (T,F)→mul_zero (T,T)→rfl
        body (bcases mot-a a branch-F branch-T)
        proof (-> body
                  (#(e/lam "v" S (e/abstract1 % 4) :default))
                  (#(e/lam "u" S (e/abstract1 % 3) :default))
                  (#(e/lam "b" boolT (e/abstract1 % 2) :default))
                  (#(e/lam "a" boolT (e/abstract1 % 1) :default))
                  sem-lam)]
    [goal proof]))

;; Nat law: thin instantiation of the generic at (Nat,·,0,Nat.zero_mul,Nat.mul_zero). Goal byte-identical.
(defn prove-cond-and-mul-split []
  (let [[_ pGen] (prove-cond-and-mul-split-generic)
        a (e/fvar 1) b (e/fvar 2) u (e/fvar 3) v (e/fvar 4)
        natT (gh-natT) zeroN (gh-zeroN)
        condN (fn [c x y] (e/app* (e/const' (nm "cond") [L1]) natT c x y))
        andB  (fn [x y] (e/app* (e/const' (nm "Bool.and") []) x y))
        concl (lk-eqAt natT (condN (andB a b) (smc-mul u v) zeroN)
                       (smc-mul (condN a u zeroN) (condN b v zeroN)))
        goal (-> concl
                 (#(e/forall' "v" natT (e/abstract1 % 4) :default))
                 (#(e/forall' "u" natT (e/abstract1 % 3) :default))
                 (#(e/forall' "b" boolT (e/abstract1 % 2) :default))
                 (#(e/forall' "a" boolT (e/abstract1 % 1) :default)))
        proof (when pGen
                (e/app* pGen natT (e/const' (nm "Nat.mul") []) zeroN
                        (e/const' (nm "Nat.zero_mul") []) (e/const' (nm "Nat.mul_zero") [])))]
    [goal proof]))

;; ── Map.bucket_key_subst (the FD SCOPE QUOTIENT foundation) ───────────────────────
;; map (λy. h (lf y) y) (filter (λy. k == lf y) ys) = map (λy. h k y) (filter (λy. k == lf y) ys)
;; A key-FUNCTIONAL-DEPENDENCY fact: on a group_by bucket (= the keyed filter, by Map.bucket_content),
;; every element y satisfies lf y = k, so substituting the JOIN KEY k for (lf y) anywhere is sound. This
;; is the dependent-types scope quotient: the matched key is SHARED scope across the two join sides, so a
;; build-side factor that reads the key (h (lf y) y) equals one that reads it as the constant k = kf x —
;; letting a key-dependent weight FLOAT to whichever side is cheaper (e.g. into the per-key pre-aggregated
;; index instead of per row). Proof: induction on ys; cons splits by-cases on (k == lf head) — the
;; filter_cons_of_pos branch gets `(k == lf head) = true`, so beq_iff_eq gives k = lf head and
;; congrArg (λkey. h key head) closes the head while the IH closes the tail; filter_cons_of_neg drops the
;; head to the IH. (h : K → Y → W is fully general, so it covers a key-factor × residual w(lf y)·g(y).)
(def ^:private bks-LEM
  ['List.map_nil 'List.map_cons 'List.filter_nil 'List.filter_cons_of_pos 'List.filter_cons_of_neg
   'cond 'cond_true 'cond_false])
(defn prove-bucket-key-subst []
  (let [K (e/fvar 1) W (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) lf (e/fvar 5) h (e/fvar 6) k (e/fvar 7) ys (e/fvar 8)
        beqK (fn [x y] (e/app* (e/const' (nm "BEq.beq") [z]) K (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec) x y))
        filtP (e/lam "y" Y (beqK k (e/app lf (e/bvar 0))) :default)
        filt (fn [l] (e/app* (e/const' (nm "List.filter") [z]) Y filtP l))
        lhsFn (e/lam "y" Y (e/app* h (e/app lf (e/bvar 0)) (e/bvar 0)) :default)
        rhsFn (e/lam "y" Y (e/app* h k (e/bvar 0)) :default)
        mapW (fn [fn l] (e/app* (e/const' (nm "List.map") [z z]) Y W fn l))
        concl (e/app* (e/const' (nm "Eq") [L1]) (listOf W) (mapW lhsFn (filt ys)) (mapW rhsFn (filt ys)))
        goal (-> concl
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 8) :default))
                 (#(e/forall' "k" K (e/abstract1 % 7) :default))
                 (#(e/forall' "h" (e/forall' "_" K (e/forall' "_" Y W :default) :default) (e/abstract1 % 6) :default))
                 (#(e/forall' "lf" (e/forall' "_" Y K :default) (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "W" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "W" "Y" "dec" "lf" "h" "k" "ys"])
        ps (basic/induction ps (fvid ps "ys"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))]
                (if cons?
                  (let [hd (gf psg "head")
                        Kp (gf psg "K") dp (gf psg "dec") lfp (gf psg "lf")
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        ih (e/fvar ihid)
                        beqhd (e/app* (e/const' (nm "BEq.beq") [z]) Kp (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) Kp dp) (gf psg "k") (e/app lfp hd))
                        br (basic/by-cases psg beqhd)
                        bids (new-goals (:goals psg) (:goals br))]
                    (reduce (fn [qq bid]
                              (let [qb (focus qq bid)
                                    hc (fvid qb "hc")
                                    hctype (:type (some (fn [[_ d]] (when (= "hc" (:name d)) d)) (:lctx (proof/current-goal qb))))
                                    pos? (= "Bool.true" (name/->string (e/const-name (nth (second (e/get-app-fn-args hctype)) 2))))
                                    r (try (basic/rewrite qb (e/fvar hc)) (catch Throwable _ qb))
                                    r (try (simp/simp-all r bks-LEM) (catch Throwable _ r))
                                    r (if pos?
                                        (let [Kp (gf r "K") dp (gf r "dec") lfp (gf r "lf") hp (gf r "h") kp (gf r "k") Wp (gf r "W")
                                              lawful (e/app* (e/const' (nm "instLawfulBEqOfDecidableEq") []) Kp dp)
                                              biff (e/app* (e/const' (nm "beq_iff_eq") [z]) Kp (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) Kp dp) lawful kp (e/app lfp hd))
                                              hfeq (e/app* (e/const' (nm "Iff.mp") [])
                                                           (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") [])
                                                                   (e/app* (e/const' (nm "BEq.beq") [z]) Kp (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) Kp dp) kp (e/app lfp hd))
                                                                   (e/const' (nm "Bool.true") []))
                                                           (e/app* (e/const' (nm "Eq") [L1]) Kp kp (e/app lfp hd)) biff (e/fvar hc))
                                              symh (e/app* (e/const' (nm "Eq.symm") [L1]) Kp kp (e/app lfp hd) hfeq)       ; lf head = k
                                              hmot (e/lam "key" Kp (e/app* hp (e/bvar 0) hd) :default)                    ; λkey. h key head
                                              wheq (e/app* (e/const' (nm "congrArg") [L1 L1]) Kp Wp (e/app lfp hd) kp hmot symh) ; h(lf head) head = h k head
                                              r2 (try (basic/rewrite r wheq) (catch Throwable _ r))
                                              r2 (try (basic/rewrite r2 ih) (catch Throwable _ r2))]
                                          (try (simp/simp-all r2 bks-LEM) (catch Throwable _ r2)))
                                        (let [r2 (try (basic/rewrite r ih) (catch Throwable _ r))]
                                          (try (simp/simp-all r2 bks-LEM) (catch Throwable _ r2))))]
                                (if (proof/solved? r) r (try (basic/rfl r) (catch Throwable _ r)))))
                            br bids))
                  (let [q (try (simp/simp-all psg bks-LEM) (catch Throwable _ psg))]
                    (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── Map.bucket_factor_pull (FD scope quotient — key-factor pull, Phase 5 layer 2) ─
;; foldl(+) 0 (map (λy. (w (lf y)) · (g y)) (filter (λy. k == lf y) ys))
;;   = (w k) · foldl(+) 0 (map g (filter (λy. k == lf y) ys))
;; A key-dependent build-side factor `w(lf y)` is CONSTANT on the bucket (= w k, by the FD
;; Map.bucket_key_subst), so it pulls OUT of the per-bucket sum — computed ONCE per distinct key, not
;; per matching row. Pure assembly (NO new induction): bucket_key_subst rewrites w(lf y)→w(k) inside the
;; map, then List.foldl_map + List.foldl_const_mul_pull (the §P1 const pull) factor (w k) out, then
;; foldl_map back. The certificate the optimizer needs to FLOAT a key-factor into the per-key
;; pre-aggregated index (the win when distinct-keys ≪ |xs|).
;; ── Map.bucket_factor_pull (SEMIRING-GENERIC FD factor-pull) ──────────────────────
;; A key-dependent build-side factor w(lf y) is constant on a bucket (where lf y = k), so it pulls OUT of
;; the per-bucket sum. Generic over (S,+,·,0) + left-distrib + right-annihilator (via const_mul_pull_generic);
;; bucket_key_subst is already W-generic, foldl_map is value-generic. Nat law instantiates at (Nat,+,·,0).
(defn prove-bucket-factor-pull-generic []
  (let [S (e/fvar 10) addF (e/fvar 11) mulF (e/fvar 12) zeroF (e/fvar 13) hMA (e/fvar 14) hMZ (e/fvar 15)
        addG (fn [a b] (e/app* addF a b)) mulG (fn [a b] (e/app* mulF a b))
        arrow (fn [a b] (e/forall' "_" a b :default))
        eqS (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) S x y))
        hMA-ty (e/forall' "a" S (e/forall' "b" S (e/forall' "c" S
                  (eqS (mulG (e/bvar 2) (addG (e/bvar 1) (e/bvar 0)))
                       (addG (mulG (e/bvar 2) (e/bvar 1)) (mulG (e/bvar 2) (e/bvar 0)))) :default) :default) :default)
        hMZ-ty (e/forall' "a" S (eqS (mulG (e/bvar 0) zeroF) zeroF) :default)
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/forall' "hMA" hMA-ty (e/abstract1 % 14) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 13) :default))
                  (#(e/forall' "mul" (arrow S (arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/forall' "add" (arrow S (arrow S S)) (e/abstract1 % 11) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 10) :default))))
        sem-lam (fn [t] (-> t
                  (#(e/lam "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/lam "hMA" hMA-ty (e/abstract1 % 14) :default))
                  (#(e/lam "zero" S (e/abstract1 % 13) :default))
                  (#(e/lam "mul" (arrow S (arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/lam "add" (arrow S (arrow S S)) (e/abstract1 % 11) :default))
                  (#(e/lam "S" type0 (e/abstract1 % 10) :default))))
        K (e/fvar 1) Y (e/fvar 2) dec (e/fvar 3) lf (e/fvar 4) w (e/fvar 5) g (e/fvar 6) k (e/fvar 7) ys (e/fvar 8)
        instB (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        filtP (e/lam "y" Y (e/app* (e/const' (nm "BEq.beq") [z]) K instB k (e/app lf (e/bvar 0))) :default)
        bf (e/app* (e/const' (nm "List.filter") [z]) Y filtP ys)
        mapY (fn [fn l] (e/app* (e/const' (nm "List.map") [z z]) Y S fn l))
        foldlS (fn [l] (e/app* (e/const' (nm "List.foldl") [z z]) S S addF zeroF l))
        wlfg (e/lam "y" Y (mulG (e/app w (e/app lf (e/bvar 0))) (e/app g (e/bvar 0))) :default)
        wkg  (e/lam "y" Y (mulG (e/app w k) (e/app g (e/bvar 0))) :default)
        h (e/lam "key" K (e/lam "y" Y (mulG (e/app w (e/bvar 1)) (e/app g (e/bvar 0))) :default) :default)
        bks (e/app* (e/const' (nm "Map.bucket_key_subst") []) K S Y dec lf h k ys)
        stepA (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf S) S
                      (mapY wlfg bf) (mapY wkg bf)
                      (e/lam "l" (listOf S) (foldlS (e/bvar 0)) :default) bks)
        fusedWk (e/app* (e/const' (nm "List.foldl") [z z]) S Y
                        (e/lam "a" S (e/lam "y" Y (addG (e/bvar 1) (mulG (e/app w k) (e/app g (e/bvar 0)))) :default) :default)
                        zeroF bf)
        fusedG  (e/app* (e/const' (nm "List.foldl") [z z]) S Y
                        (e/lam "a" S (e/lam "y" Y (addG (e/bvar 1) (e/app g (e/bvar 0))) :default) :default)
                        zeroF bf)
        fm1 (e/app* (e/const' (nm "List.foldl_map") [z z z]) Y S S wkg addF bf zeroF)
        cmp (e/app* (e/const' (nm "List.foldl_const_mul_pull_generic") []) S addF mulF zeroF hMA hMZ Y (e/app w k) g bf)
        fm2 (e/app* (e/const' (nm "List.foldl_map") [z z z]) Y S S g addF bf zeroF)
        fm2sym (e/app* (e/const' (nm "Eq.symm") [L1]) S (foldlS (mapY g bf)) fusedG fm2)
        congMul (e/app* (e/const' (nm "congrArg") [L1 L1]) S S fusedG (foldlS (mapY g bf))
                        (e/lam "v" S (mulG (e/app w k) (e/bvar 0)) :default) fm2sym)
        stepB (e/app* (e/const' (nm "Eq.trans") [L1]) S
                      (foldlS (mapY wkg bf)) (mulG (e/app w k) fusedG) (mulG (e/app w k) (foldlS (mapY g bf)))
                      (e/app* (e/const' (nm "Eq.trans") [L1]) S (foldlS (mapY wkg bf)) fusedWk (mulG (e/app w k) fusedG) fm1 cmp)
                      congMul)
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) S
                      (foldlS (mapY wlfg bf)) (foldlS (mapY wkg bf)) (mulG (e/app w k) (foldlS (mapY g bf)))
                      stepA stepB)
        concl (eqS (foldlS (mapY wlfg bf)) (mulG (e/app w k) (foldlS (mapY g bf))))
        goal (-> concl
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 8) :default))
                 (#(e/forall' "k" K (e/abstract1 % 7) :default))
                 (#(e/forall' "g" (arrow Y S) (e/abstract1 % 6) :default))
                 (#(e/forall' "w" (arrow K S) (e/abstract1 % 5) :default))
                 (#(e/forall' "lf" (arrow Y K) (e/abstract1 % 4) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 3) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default))
                 sem-pi)
        fproof (-> proof
                   (#(e/lam "ys" (listOf Y) (e/abstract1 % 8) :default))
                   (#(e/lam "k" K (e/abstract1 % 7) :default))
                   (#(e/lam "g" (arrow Y S) (e/abstract1 % 6) :default))
                   (#(e/lam "w" (arrow K S) (e/abstract1 % 5) :default))
                   (#(e/lam "lf" (arrow Y K) (e/abstract1 % 4) :default))
                   (#(e/lam "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 3) :default))
                   (#(e/lam "Y" type0 (e/abstract1 % 2) :default))
                   (#(e/lam "K" type0 (e/abstract1 % 1) :default))
                   sem-lam)]
    [goal fproof]))

(defn prove-bucket-factor-pull []
  (let [[_ pGen] (prove-bucket-factor-pull-generic)
        K (e/fvar 1) Y (e/fvar 2) dec (e/fvar 3) lf (e/fvar 4) w (e/fvar 5) g (e/fvar 6) k (e/fvar 7) ys (e/fvar 8)
        natT (gh-natT) zeroN (gh-zeroN) addC (e/const' (nm "Nat.add") [])
        instB (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        filtP (e/lam "y" Y (e/app* (e/const' (nm "BEq.beq") [z]) K instB k (e/app lf (e/bvar 0))) :default)
        bf (e/app* (e/const' (nm "List.filter") [z]) Y filtP ys)
        mapY (fn [fn l] (e/app* (e/const' (nm "List.map") [z z]) Y natT fn l))
        foldlS (fn [l] (e/app* (e/const' (nm "List.foldl") [z z]) natT natT addC zeroN l))
        wlfg (e/lam "y" Y (smc-mul (e/app w (e/app lf (e/bvar 0))) (e/app g (e/bvar 0))) :default)
        wkg  (e/lam "y" Y (smc-mul (e/app w k) (e/app g (e/bvar 0))) :default)
        h (e/lam "key" K (e/lam "y" Y (smc-mul (e/app w (e/bvar 1)) (e/app g (e/bvar 0))) :default) :default)
        bks (e/app* (e/const' (nm "Map.bucket_key_subst") []) K natT Y dec lf h k ys)
        stepA (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf natT) natT
                      (mapY wlfg bf) (mapY wkg bf)
                      (e/lam "l" (listOf natT) (foldlS (e/bvar 0)) :default) bks)
        fusedWk (e/app* (e/const' (nm "List.foldl") [z z]) natT Y
                        (e/lam "a" natT (e/lam "y" Y (e/app* addC (e/bvar 1) (smc-mul (e/app w k) (e/app g (e/bvar 0)))) :default) :default)
                        zeroN bf)
        fusedG  (e/app* (e/const' (nm "List.foldl") [z z]) natT Y
                        (e/lam "a" natT (e/lam "y" Y (e/app* addC (e/bvar 1) (e/app g (e/bvar 0))) :default) :default)
                        zeroN bf)
        fm1 (e/app* (e/const' (nm "List.foldl_map") [z z z]) Y natT natT wkg addC bf zeroN)
        cmp (e/app* (e/const' (nm "List.foldl_const_mul_pull") []) Y (e/app w k) g bf)
        fm2 (e/app* (e/const' (nm "List.foldl_map") [z z z]) Y natT natT g addC bf zeroN)
        fm2sym (e/app* (e/const' (nm "Eq.symm") [L1]) natT (foldlS (mapY g bf)) fusedG fm2)
        congMul (e/app* (e/const' (nm "congrArg") [L1 L1]) natT natT fusedG (foldlS (mapY g bf))
                        (e/lam "v" natT (smc-mul (e/app w k) (e/bvar 0)) :default) fm2sym)
        stepB (e/app* (e/const' (nm "Eq.trans") [L1]) natT
                      (foldlS (mapY wkg bf)) (smc-mul (e/app w k) fusedG) (smc-mul (e/app w k) (foldlS (mapY g bf)))
                      (e/app* (e/const' (nm "Eq.trans") [L1]) natT (foldlS (mapY wkg bf)) fusedWk (smc-mul (e/app w k) fusedG) fm1 cmp)
                      congMul)
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) natT
                      (foldlS (mapY wlfg bf)) (foldlS (mapY wkg bf)) (smc-mul (e/app w k) (foldlS (mapY g bf)))
                      stepA stepB)
        concl (lk-eqAt natT (foldlS (mapY wlfg bf)) (smc-mul (e/app w k) (foldlS (mapY g bf))))
        goal (-> concl
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 8) :default))
                 (#(e/forall' "k" K (e/abstract1 % 7) :default))
                 (#(e/forall' "g" (e/forall' "_" Y natT :default) (e/abstract1 % 6) :default))
                 (#(e/forall' "w" (e/forall' "_" K natT :default) (e/abstract1 % 5) :default))
                 (#(e/forall' "lf" (e/forall' "_" Y K :default) (e/abstract1 % 4) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 3) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        ;; thin instantiation of the semiring-generic factor-pull at (Nat,+,·,0). Goal byte-identical.
        fproof (when pGen
                 (e/app* pGen natT addC (e/const' (nm "Nat.mul") []) zeroN
                         (e/const' (nm "Nat.mul_add") []) (e/const' (nm "Nat.mul_zero") [])))]
    [goal fproof]))

;; ── List.lookup_reweight (FD scope quotient — float a key-factor into the index) ─
;; (w k) · getD (lookup k idx) 0 = getD (lookup k (map (λp. (fst p, w(fst p)·snd p)) idx)) 0
;; A key-factor that multiplies a per-key index lookup can be BAKED INTO the index (each entry's value
;; reweighted by w of its key), because the lookup key IS k so w(fst entry) = w(k) on the found entry
;; (and 0·w = 0 when absent). This is the certificate for FLOATING a key-factor `w(kf x)` out of the
;; per-row x-side and into the O(distinct-keys) pre-aggregated index — the Phase-5 win when ndv ≪ |xs|.
;; Proof: induction on idx; cons eta-expands the head (so List.lookup reduces on the literal pair), then
;; by-cases on (k == fst head) — simp exposes the matcher, rewriting hc reduces it, and the
;; (k == fst head)=true branch closes via beq_iff_eq → w k = w(fst head); the false branch is the IH.
(def ^:private lrw-LEM
  ['List.lookup_nil 'List.lookup_cons 'List.lookup_cons_self 'List.map_nil 'List.map_cons
   'Option.getD 'cond 'cond_true 'cond_false 'Nat.mul_zero])
;; SEMIRING-GENERIC reweight: the only value-algebra is the absent-key (nil) case `mul (w k) 0 = 0`
;; (every cons branch closes structurally + beq_iff_eq + IH), so the generic carries just (S,mul,zero) +
;; a right-annihilator hMZ. The structural simp set drops Nat.mul_zero; the nil goal is closed via hMZ.
(defn prove-lookup-reweight-generic []
  (let [S (e/fvar 10) mulF (e/fvar 12) zeroF (e/fvar 13) hMZ (e/fvar 15)
        mulG (fn [a b] (e/app* mulF a b))
        arrow (fn [a b] (e/forall' "_" a b :default))
        eqAt (fn [ty x y] (e/app* (e/const' (nm "Eq") [L1]) ty x y))
        hMZ-ty (e/forall' "a" S (eqAt S (mulG (e/bvar 0) zeroF) zeroF) :default)
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 13) :default))
                  (#(e/forall' "mul" (arrow S (arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 10) :default))))
        lrw-struct (vec (remove #(= 'Nat.mul_zero %) lrw-LEM))
        K (e/fvar 1) dec (e/fvar 2) w (e/fvar 3) k (e/fvar 4) idx (e/fvar 5)
        KN (prodT K S)
        instB (fn [kk dd] (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) kk dd))
        lookupN (fn [kk dd key l] (e/app* (e/const' (nm "List.lookup") [z z]) kk S (instB kk dd) key l))
        getD (fn [o] (e/app* (e/const' (nm "Option.getD") [z]) S o zeroF))
        rwf (fn [ww KK] (e/lam "p" (prodT KK S)
                          (mkP KK S (fstOf KK S (e/bvar 0)) (mulG (e/app ww (fstOf KK S (e/bvar 0))) (sndOf KK S (e/bvar 0)))) :default))
        mapped (fn [ww KK dd l] (e/app* (e/const' (nm "List.map") [z z]) (prodT KK S) (prodT KK S) (rwf ww KK) l))
        lhs (mulG (e/app w k) (getD (lookupN K dec k idx)))
        rhs (getD (lookupN K dec k (mapped w K dec idx)))
        goal (-> (eqAt S lhs rhs)
                 (#(e/forall' "idx" (listOf KN) (e/abstract1 % 5) :default))
                 (#(e/forall' "k" K (e/abstract1 % 4) :default))
                 (#(e/forall' "w" (arrow K S) (e/abstract1 % 3) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default))
                 sem-pi)
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["S" "mul" "zero" "hMZ" "K" "dec" "w" "k" "idx"])
        ps (basic/induction ps (fvid ps "idx"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))]
                (if cons?
                  (let [Sp (gf psg "S") hd (gf psg "head") Kp (gf psg "K") dp (gf psg "dec") wp (gf psg "w") kp (gf psg "k")
                        etaSymm (e/app* (e/const' (nm "Eq.symm") [L1]) (prodT Kp Sp)
                                        (mkP Kp Sp (fstOf Kp Sp hd) (sndOf Kp Sp hd)) hd
                                        (e/app* (e/const' (nm "Prod.eta") [z z]) Kp Sp hd))
                        psg (basic/rewrite psg etaSymm)
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        ih (e/fvar ihid)
                        beqhd (e/app* (e/const' (nm "BEq.beq") [z]) Kp (instB Kp dp) kp (fstOf Kp Sp hd))
                        br (basic/by-cases psg beqhd)
                        bids (new-goals (:goals psg) (:goals br))]
                    (reduce (fn [qq bid]
                              (let [qb (focus qq bid)
                                    hc (fvid qb "hc")
                                    hctype (:type (some (fn [[_ d]] (when (= "hc" (:name d)) d)) (:lctx (proof/current-goal qb))))
                                    pos? (= "Bool.true" (name/->string (e/const-name (nth (second (e/get-app-fn-args hctype)) 2))))
                                    r (try (simp/simp-all qb lrw-struct) (catch Throwable _ qb))
                                    r (try (basic/rewrite r (e/fvar hc)) (catch Throwable _ r))
                                    r (try (simp/simp-all r lrw-struct) (catch Throwable _ r))
                                    r (if pos?
                                        (let [Sp (gf r "S") Kp (gf r "K") dp (gf r "dec") wp (gf r "w") kp (gf r "k")
                                              lawful (e/app* (e/const' (nm "instLawfulBEqOfDecidableEq") []) Kp dp)
                                              biff (e/app* (e/const' (nm "beq_iff_eq") [z]) Kp (instB Kp dp) lawful kp (fstOf Kp Sp hd))
                                              hfeq (e/app* (e/const' (nm "Iff.mp") [])
                                                           (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") [])
                                                                   (e/app* (e/const' (nm "BEq.beq") [z]) Kp (instB Kp dp) kp (fstOf Kp Sp hd))
                                                                   (e/const' (nm "Bool.true") []))
                                                           (e/app* (e/const' (nm "Eq") [L1]) Kp kp (fstOf Kp Sp hd)) biff (e/fvar hc))
                                              wkeq (e/app* (e/const' (nm "congrArg") [L1 L1]) Kp Sp kp (fstOf Kp Sp hd) wp hfeq)
                                              r2 (try (basic/rewrite r wkeq) (catch Throwable _ r))]
                                          (try (simp/simp-all r2 lrw-struct) (catch Throwable _ r2)))
                                        (let [r2 (try (basic/rewrite r ih) (catch Throwable _ r))]
                                          (try (simp/simp-all r2 lrw-struct) (catch Throwable _ r2))))]
                                (if (proof/solved? r) r (try (basic/rfl r) (catch Throwable _ r)))))
                            br bids))
                  ;; NIL: structural simp reduces to `mul (w k) zero = zero`; close via hMZ (w k).
                  (let [q (try (simp/simp-all psg lrw-struct) (catch Throwable _ psg))]
                    (if (proof/solved? q) q
                        (let [wp (gf q "w") kp (gf q "k") hmz (gf q "hMZ")]
                          (or (try (basic/exact q (e/app* hmz (e/app wp kp))) (catch Throwable _ nil))
                              (try (basic/rfl q) (catch Throwable _ q)))))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-lookup-reweight []
  (let [[_ pGen] (prove-lookup-reweight-generic)
        K (e/fvar 1) dec (e/fvar 2) w (e/fvar 3) k (e/fvar 4) idx (e/fvar 5)
        natT (gh-natT) zeroN (gh-zeroN) KN (prodT K natT)
        instB (fn [kk dd] (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) kk dd))
        lookupN (fn [kk dd key l] (e/app* (e/const' (nm "List.lookup") [z z]) kk natT (instB kk dd) key l))
        getD (fn [o] (e/app* (e/const' (nm "Option.getD") [z]) natT o zeroN))
        rwf (fn [ww KK] (e/lam "p" (prodT KK natT)
                          (mkP KK natT (fstOf KK natT (e/bvar 0)) (smc-mul (e/app ww (fstOf KK natT (e/bvar 0))) (sndOf KK natT (e/bvar 0)))) :default))
        mapped (fn [ww KK dd l] (e/app* (e/const' (nm "List.map") [z z]) (prodT KK natT) (prodT KK natT) (rwf ww KK) l))
        lhs (smc-mul (e/app w k) (getD (lookupN K dec k idx)))
        rhs (getD (lookupN K dec k (mapped w K dec idx)))
        concl (lk-eqAt natT lhs rhs)
        goal (-> concl
                 (#(e/forall' "idx" (listOf KN) (e/abstract1 % 5) :default))
                 (#(e/forall' "k" K (e/abstract1 % 4) :default))
                 (#(e/forall' "w" (e/forall' "_" K natT :default) (e/abstract1 % 3) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        ;; thin instantiation of the generic at (Nat,·,0,Nat.mul_zero). Goal byte-identical.
        proof (when pGen
                (e/app* pGen natT (e/const' (nm "Nat.mul") []) zeroN (e/const' (nm "Nat.mul_zero") [])))]
    [goal proof]))

;; ── Map.foldl_keyfactor_float (FD scope quotient — the optimizer float law, Phase 5 layer 3) ─
;; foldl (λacc x. acc + (w (kf x)) · getD (lookup (kf x) idx) 0) e xs
;;   = foldl (λacc x. acc + getD (lookup (kf x) (map (λp. (fst p, w(fst p)·snd p)) idx)) 0) e xs
;; A key-factor `w(kf x)` multiplying a per-key index lookup FLOATS into the index (reweighting each
;; entry by w of its key) — over an ARBITRARY index, so it composes directly with the frame's output
;; (idx := the frame's pre-aggregated index). Moves w from per-row (|xs|) to per-key (|distinct-keys|).
;; Pure assembly: List.foldl_congr lifts the per-x List.lookup_reweight identity (congrArg under acc+·).
;; SEMIRING-GENERIC: pure assembly (foldl_congr lifting the per-x lookup_reweight_generic identity).
;; No add/mul LAWS used here beyond what lookup_reweight needs (hMZ); add/mul/zero are just ops.
(defn prove-keyfactor-float-generic []
  (let [S (e/fvar 10) addF (e/fvar 11) mulF (e/fvar 12) zeroF (e/fvar 13) hMZ (e/fvar 15)
        addG (fn [a b] (e/app* addF a b)) mulG (fn [a b] (e/app* mulF a b))
        arrow (fn [a b] (e/forall' "_" a b :default))
        eqAt (fn [ty x y] (e/app* (e/const' (nm "Eq") [L1]) ty x y))
        hMZ-ty (e/forall' "a" S (eqAt S (mulG (e/bvar 0) zeroF) zeroF) :default)
        sem-pi (fn [t] (-> t
                  (#(e/forall' "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/forall' "zero" S (e/abstract1 % 13) :default))
                  (#(e/forall' "mul" (arrow S (arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/forall' "add" (arrow S (arrow S S)) (e/abstract1 % 11) :default))
                  (#(e/forall' "S" type0 (e/abstract1 % 10) :default))))
        sem-lam (fn [t] (-> t
                  (#(e/lam "hMZ" hMZ-ty (e/abstract1 % 15) :default))
                  (#(e/lam "zero" S (e/abstract1 % 13) :default))
                  (#(e/lam "mul" (arrow S (arrow S S)) (e/abstract1 % 12) :default))
                  (#(e/lam "add" (arrow S (arrow S S)) (e/abstract1 % 11) :default))
                  (#(e/lam "S" type0 (e/abstract1 % 10) :default))))
        K (e/fvar 1) X (e/fvar 2) dec (e/fvar 3) w (e/fvar 4) kf (e/fvar 5) e (e/fvar 6) xs (e/fvar 7) idx (e/fvar 8)
        KN (prodT K S)
        instB (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        lookupN (fn [key l] (e/app* (e/const' (nm "List.lookup") [z z]) K S instB key l))
        getD (fn [o] (e/app* (e/const' (nm "Option.getD") [z]) S o zeroF))
        reweight (e/lam "p" KN (mkP K S (fstOf K S (e/bvar 0)) (mulG (e/app w (fstOf K S (e/bvar 0))) (sndOf K S (e/bvar 0)))) :default)
        mappedIdx (e/app* (e/const' (nm "List.map") [z z]) KN KN reweight idx)
        R1step (e/lam "acc" S (e/lam "x" X (addG (e/bvar 1) (mulG (e/app w (e/app kf (e/bvar 0))) (getD (lookupN (e/app kf (e/bvar 0)) idx)))) :default) :default)
        R2step (e/lam "acc" S (e/lam "x" X (addG (e/bvar 1) (getD (lookupN (e/app kf (e/bvar 0)) mappedIdx))) :default) :default)
        foldlX (fn [step] (e/app* (e/const' (nm "List.foldl") [z z]) S X step e xs))
        af 201 xf 202 acc (e/fvar af) x (e/fvar xf)
        lrw (e/app* (e/const' (nm "List.lookup_reweight_generic") []) S mulF zeroF hMZ K dec w (e/app kf x) idx)
        accPlus (e/lam "v" S (addG acc (e/bvar 0)) :default)
        hbody (e/app* (e/const' (nm "congrArg") [L1 L1]) S S
                      (mulG (e/app w (e/app kf x)) (getD (lookupN (e/app kf x) idx)))
                      (getD (lookupN (e/app kf x) mappedIdx))
                      accPlus lrw)
        hyp (e/lam "acc" S (e/abstract1 (e/lam "x" X (e/abstract1 hbody xf) :default) af) :default)
        proof (e/app* (e/const' (nm "List.foldl_congr") []) S X R1step R2step xs e hyp)
        goal (-> (eqAt S (foldlX R1step) (foldlX R2step))
                 (#(e/forall' "idx" (listOf KN) (e/abstract1 % 8) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 7) :default))
                 (#(e/forall' "e" S (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" (arrow X K) (e/abstract1 % 5) :default))
                 (#(e/forall' "w" (arrow K S) (e/abstract1 % 4) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default))
                 sem-pi)
        fproof (-> proof
                   (#(e/lam "idx" (listOf KN) (e/abstract1 % 8) :default))
                   (#(e/lam "xs" (listOf X) (e/abstract1 % 7) :default))
                   (#(e/lam "e" S (e/abstract1 % 6) :default))
                   (#(e/lam "kf" (arrow X K) (e/abstract1 % 5) :default))
                   (#(e/lam "w" (arrow K S) (e/abstract1 % 4) :default))
                   (#(e/lam "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 3) :default))
                   (#(e/lam "X" type0 (e/abstract1 % 2) :default))
                   (#(e/lam "K" type0 (e/abstract1 % 1) :default))
                   sem-lam)]
    [goal fproof]))

(defn prove-keyfactor-float []
  (let [[_ pGen] (prove-keyfactor-float-generic)
        K (e/fvar 1) X (e/fvar 2) dec (e/fvar 3) w (e/fvar 4) kf (e/fvar 5) e (e/fvar 6) xs (e/fvar 7) idx (e/fvar 8)
        natT (gh-natT) zeroN (gh-zeroN) KN (prodT K natT)
        instB (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        lookupN (fn [key l] (e/app* (e/const' (nm "List.lookup") [z z]) K natT instB key l))
        getD (fn [o] (e/app* (e/const' (nm "Option.getD") [z]) natT o zeroN))
        reweight (e/lam "p" KN (mkP K natT (fstOf K natT (e/bvar 0)) (smc-mul (e/app w (fstOf K natT (e/bvar 0))) (sndOf K natT (e/bvar 0)))) :default)
        mappedIdx (e/app* (e/const' (nm "List.map") [z z]) KN KN reweight idx)
        R1step (e/lam "acc" natT (e/lam "x" X (gh-addN (e/bvar 1) (smc-mul (e/app w (e/app kf (e/bvar 0))) (getD (lookupN (e/app kf (e/bvar 0)) idx)))) :default) :default)
        R2step (e/lam "acc" natT (e/lam "x" X (gh-addN (e/bvar 1) (getD (lookupN (e/app kf (e/bvar 0)) mappedIdx))) :default) :default)
        foldlX (fn [step] (e/app* (e/const' (nm "List.foldl") [z z]) natT X step e xs))
        concl (lk-eqAt natT (foldlX R1step) (foldlX R2step))
        goal (-> concl
                 (#(e/forall' "idx" (listOf KN) (e/abstract1 % 8) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 7) :default))
                 (#(e/forall' "e" natT (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" (e/forall' "_" X K :default) (e/abstract1 % 5) :default))
                 (#(e/forall' "w" (e/forall' "_" K natT :default) (e/abstract1 % 4) :default))
                 (#(e/forall' "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        ;; thin instantiation of the generic at (Nat,+,·,0,Nat.mul_zero). Goal byte-identical.
        fproof (when pGen
                 (e/app* pGen natT (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.mul") []) zeroN
                         (e/const' (nm "Nat.mul_zero") [])))]
    [goal fproof]))
