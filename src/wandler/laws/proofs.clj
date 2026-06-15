(ns wandler.laws.proofs
  "The clean SRC home for the relational-algebra law PROOFS (previously scattered across test
   files). Pure proof functions `(env assumed) → [goal proof|nil]`, organized by dependency layer:
     §2 perm    — List.Perm helpers (flatMap_congr_perm, flatMap_map_comm, foldl_cons_perm, …)
     §3 bucket  — Map.bucket_content(_gen)
     §4 join    — BEq.beq_comm, Map.bucket_perm, Map.join_filtered_product, Map.join_comm,
                  Map.join_length_comm  (the commutativity capstone + the Perm→Eq count bridge)
   wandler.laws.relational orchestrates these (with the lookup/group_by foundation it already builds) in
   dependency order, check-constant's each, and admits + memoizes. The capstone proofs register
   their own intermediates (pushouts/qeq/claimC/…) into the env as side effects (via reg-anon!).
   Built on Init's List.Perm constructors + the verified Map foundation. See [[rel-laws-installer]]."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]))

;; ── §0 helpers ────────────────────────────────────────────────────────────────
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
(defn- consOf [a x l] (e/app* (e/const' (nm "List.cons") [z]) a x l))
(defn- singletonOf [a x] (consOf a x (nilOf a)))
(defn- mapOf [aX aY f l] (e/app* (e/const' (nm "List.map") [z z]) aX aY f l))
(defn- flatMap [aX aY f l] (e/app* (e/const' (nm "List.flatMap") [z z]) aX aY f l))
(def ^:private flatMapOf flatMap)
(defn- filterOf [a p l] (e/app* (e/const' (nm "List.filter") [z]) a p l))
(defn- foldlOf [a init l flip] (e/app* (e/const' (nm "List.foldl") [z z]) (listOf a) a flip init l))
(defn- appendOf [a l r] (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) (listOf a) (listOf a) (listOf a)
                                (e/app* (e/const' (nm "instHAppendOfAppend") [z]) (listOf a) (e/app (e/const' (nm "List.instAppend") [z]) a)) l r))
(defn- permOf [a l r] (e/app* (e/const' (nm "List.Perm") [z]) a l r))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- fstOf [X Y p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
(defn- sndOf [X Y p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
(defn- mkP [X Y x y] (e/app* (e/const' (nm "Prod.mk") [z z]) X Y x y))
(defn- beqK [K dec x y] (e/app* (e/const' (nm "BEq.beq") [z]) K (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec) x y))

(defn- p-refl [a l] (e/app* (e/const' (nm "List.Perm.refl") [z]) a l))
(defn- p-symm [a x y h] (e/app* (e/const' (nm "List.Perm.symm") [z]) a x y h))
(defn- p-trans [a x y w h1 h2] (e/app* (e/const' (nm "List.Perm.trans") [z]) a x y w h1 h2))
(defn- p-append [a l1 l2 r1 r2 h1 h2] (e/app* (e/const' (nm "List.Perm.append") [z]) a l1 l2 r1 r2 h1 h2))
(defn- p-aleft [a x y l h] (e/app* (e/const' (nm "List.Perm.append_left") [z]) a x y l h))
(defn- p-caa [a x y w] (e/app* (e/const' (nm "List.perm_append_comm_assoc") [z]) a x y w))
(defn- p-cons [a x l1 l2 h] (e/app* (e/const' (nm "List.Perm.cons") [z]) a x l1 l2 h))

(defn- eqB [x y] (e/app* (e/const' (nm "Eq") [L1]) boolT x y))
(defn- eqK [K x y] (e/app* (e/const' (nm "Eq") [L1]) K x y))
(defn- tr [ty x y w h1 h2] (e/app* (e/const' (nm "Eq.trans") [L1]) ty x y w h1 h2))
(defn- sy [ty x y h] (e/app* (e/const' (nm "Eq.symm") [L1]) ty x y h))
(defn- imp [P Q h ha] (e/app* (e/const' (nm "Iff.mp") []) P Q h ha))
(defn- impr [P Q h hb] (e/app* (e/const' (nm "Iff.mpr") []) P Q h hb))
(def ^:dynamic *admit-sink*
  "When bound (by rel-laws/build-all) to an atom, every intermediate admitted by reg-anon!
   is ALSO recorded there — so the law cache carries the full dependency closure and the
   strict replay path can re-check capstones whose proofs reference the intermediates."
  nil)

(defn- reg-anon!
  "Admit an intermediate theorem STRICTLY (check-constant, the kernel gate) — intermediates
   are part of the trust chain even when the capstone only references their types."
  [n g p]
  (let [ci (kenv/mk-thm (nm n) [] g p)]
    (swap! a/ansatz-env kenv/check-constant ci)
    (when *admit-sink* (swap! *admit-sink* conj ci))
    ci))
(defn- eq-via-simp [goal lems names]
  (let [[ps _] (proof/start-proof (a/env) goal) ps (basic/intros ps names)
        ps (try (simp/simp ps lems) (catch Throwable _ ps))]
    (when (proof/solved? ps) (extract/extract ps))))

;; ── §2 perm ─────────────────────────────────────────────────────────────────
(defn prove-flatMap-const-nil []
  (let [fX (e/fvar 1) fZ (e/fvar 2) fl (e/fvar 3)
        fn0 (e/lam "_" fX (nilOf fZ) :default)
        body (e/app* (e/const' (nm "Eq") [L1]) (listOf fZ) (flatMap fX fZ fn0 fl) (nilOf fZ))
        goal (-> body
                 (#(e/forall' "l" (listOf fX) (e/abstract1 % 3) :default))
                 (#(e/forall' "Z" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "Z" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce (fn [ps gid]
                     (let [psg (focus ps gid)
                           cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))]
                       (if cons?
                         (let [ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                               q (simp/simp psg ['List.flatMap_cons 'List.nil_append])]
                           (try (basic/exact q (e/fvar ihid)) (catch Throwable _ (basic/rfl q))))
                         (let [q (simp/simp psg ['List.flatMap_nil])]
                           (if (proof/solved? q) q (basic/rfl q))))))
                   ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-flatMap-congr-perm []
  (let [fX (e/fvar 1) fY (e/fvar 2)
        xToLY (e/forall' "_" fX (listOf fY) :default)
        ff (e/fvar 3) fg (e/fvar 4)
        hTy (e/forall' "x" fX (permOf fY (e/app ff (e/bvar 0)) (e/app fg (e/bvar 0))) :default)
        body (permOf fY (flatMap fX fY ff (e/fvar 6)) (flatMap fX fY fg (e/fvar 6)))
        goal (-> body
                 (#(e/forall' "l" (listOf fX) (e/abstract1 % 6) :default))
                 (#(e/forall' "h" hTy (e/abstract1 % 5) :default))
                 (#(e/forall' "g" xToLY (e/abstract1 % 4) :default))
                 (#(e/forall' "f" xToLY (e/abstract1 % 3) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "Y" "f" "g" "h" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce (fn [ps gid]
                     (let [psg (focus ps gid)
                           cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))
                           X (gf psg "X") Y (gf psg "Y") f (gf psg "f") g (gf psg "g") h (gf psg "h")]
                       (if cons?
                         (let [ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                               hd (gf psg "head") tl (gf psg "tail")
                               q (simp/simp psg ['List.flatMap_cons])]
                           (basic/exact q (p-append Y (e/app f hd) (e/app g hd)
                                                    (flatMap X Y f tl) (flatMap X Y g tl)
                                                    (e/app h hd) (e/fvar ihid))))
                         (let [q (simp/simp psg ['List.flatMap_nil])]
                           (basic/exact q (p-refl Y (nilOf Y)))))))
                   ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-flatMap-append-distrib []
  (let [fX (e/fvar 1) fY (e/fvar 2)
        xToLY (e/forall' "_" fX (listOf fY) :default)
        ff (e/fvar 3) fg (e/fvar 4)
        fn0 (e/lam "a" fX (appendOf fY (e/app ff (e/bvar 0)) (e/app fg (e/bvar 0))) :default)
        body (permOf fY (flatMap fX fY fn0 (e/fvar 5))
                     (appendOf fY (flatMap fX fY ff (e/fvar 5)) (flatMap fX fY fg (e/fvar 5))))
        goal (-> body
                 (#(e/forall' "l" (listOf fX) (e/abstract1 % 5) :default))
                 (#(e/forall' "g" xToLY (e/abstract1 % 4) :default))
                 (#(e/forall' "f" xToLY (e/abstract1 % 3) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "Y" "f" "g" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce (fn [ps gid]
                     (let [psg (focus ps gid)
                           cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))
                           X (gf psg "X") Y (gf psg "Y") f (gf psg "f") g (gf psg "g")]
                       (if cons?
                         (let [ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                               hd (gf psg "head") tl (gf psg "tail")
                               fh (e/app f hd) gh (e/app g hd)
                               fn0' (e/lam "a" X (appendOf Y (e/app f (e/bvar 0)) (e/app g (e/bvar 0))) :default)
                               M (flatMap X Y fn0' tl) FT (flatMap X Y f tl) GT (flatMap X Y g tl)
                               q (simp/simp psg ['List.flatMap_cons 'List.append_assoc])
                               inner (p-trans Y (appendOf Y gh M) (appendOf Y gh (appendOf Y FT GT)) (appendOf Y FT (appendOf Y gh GT))
                                              (p-aleft Y M (appendOf Y FT GT) gh (e/fvar ihid))
                                              (p-caa Y gh FT GT))]
                           (basic/exact q (p-aleft Y (appendOf Y gh M) (appendOf Y FT (appendOf Y gh GT)) fh inner)))
                         (let [q (simp/simp psg ['List.flatMap_nil 'List.append_nil 'List.nil_append])]
                           (basic/exact q (p-refl Y (nilOf Y)))))))
                   ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-join-filter-append-perm
  "GRACE-HASH partition lemma (filter form). A join's per-row filter distributes over the build-side
   APPEND: flatMap (λx. map (x,·) (filter (kf x =· lf ·) (ys1++ys2))) xs
         ~ flatMap (…ys1) xs  ++  flatMap (…ys2) xs.  So a join can process the build side in BLOCKS
   (each ≤ memory budget) and concatenate the per-block results — the certified core of grace-hash.
   Proof: simp[filter_append, map_append] aligns the body to `f x ++ g x`, then flatMap_append_distrib.
   Requires List.flatMap_append_distrib registered."
  []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys1 (e/fvar 8) ys2 (e/fvar 9)
        PXY (prodT X Y) listX (listOf X) listY (listOf Y)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        mkF (e/lam "y" Y (mkP X Y (e/bvar 1) (e/bvar 0)) :default)
        matchF (e/lam "y" Y (beqK K dec (e/app kf (e/bvar 1)) (e/app lf (e/bvar 0))) :default)
        Fb (fn [ys] (e/lam "x" X (mapOf Y PXY mkF (filterOf Y matchF ys)) :default))
        flatM (fn [ys] (flatMap X PXY (Fb ys) xs))
        body (permOf PXY (flatM (appendOf Y ys1 ys2)) (appendOf PXY (flatM ys1) (flatM ys2)))
        goal (-> body
                 (#(e/forall' "ys2" listY (e/abstract1 % 9) :default))
                 (#(e/forall' "ys1" listY (e/abstract1 % 8) :default))
                 (#(e/forall' "xs" listX (e/abstract1 % 7) :default))
                 (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "X" "Y" "dec" "kf" "lf" "xs" "ys1" "ys2"])
        K' (gf ps "K") X' (gf ps "X") Y' (gf ps "Y") dec' (gf ps "dec") kf' (gf ps "kf") lf' (gf ps "lf")
        xs' (gf ps "xs") ys1' (gf ps "ys1") ys2' (gf ps "ys2")
        PXY' (prodT X' Y')
        mkF' (e/lam "y" Y' (mkP X' Y' (e/bvar 1) (e/bvar 0)) :default)
        matchF' (e/lam "y" Y' (beqK K' dec' (e/app kf' (e/bvar 1)) (e/app lf' (e/bvar 0))) :default)
        Fb' (fn [ys] (e/lam "x" X' (mapOf Y' PXY' mkF' (filterOf Y' matchF' ys)) :default))
        ps (simp/simp ps ['List.filter_append 'List.map_append])
        ps (basic/exact ps (e/app* (e/const' (nm "List.flatMap_append_distrib_perm") []) X' PXY' (Fb' ys1') (Fb' ys2') xs'))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-flatMap-cons-distrib []
  (let [Y (e/fvar 1) Z (e/fvar 2)
        cY (e/forall' "_" Y Z :default) gY (e/forall' "_" Y (listOf Z) :default)
        c (e/fvar 3) g (e/fvar 4)
        consfn (e/lam "y" Y (consOf Z (e/app c (e/bvar 0)) (e/app g (e/bvar 0))) :default)
        body (permOf Z (flatMap Y Z consfn (e/fvar 5)) (appendOf Z (mapOf Y Z c (e/fvar 5)) (flatMap Y Z g (e/fvar 5))))
        goal (-> body
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 5) :default))
                 (#(e/forall' "g" gY (e/abstract1 % 4) :default))
                 (#(e/forall' "c" cY (e/abstract1 % 3) :default))
                 (#(e/forall' "Z" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["Y" "Z" "c" "g" "ys"])
        ps (basic/induction ps (fvid ps "ys"))
        ps (reduce (fn [ps gid]
                     (let [psg (focus ps gid)
                           cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))
                           Y (gf psg "Y") Z (gf psg "Z") c (gf psg "c") g (gf psg "g")]
                       (if cons?
                         (let [ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                               b (gf psg "head") ys' (gf psg "tail")
                               cb (e/app c b) gb (e/app g b)
                               consfn (e/lam "y" Y (consOf Z (e/app c (e/bvar 0)) (e/app g (e/bvar 0))) :default)
                               M (flatMap Y Z consfn ys') mcy (mapOf Y Z c ys') Fg (flatMap Y Z g ys')
                               q (simp/simp psg ['List.flatMap_cons 'List.map_cons])
                               inner (p-trans Z (appendOf Z gb M) (appendOf Z gb (appendOf Z mcy Fg)) (appendOf Z mcy (appendOf Z gb Fg))
                                              (p-aleft Z M (appendOf Z mcy Fg) gb (e/fvar ihid))
                                              (p-caa Z gb mcy Fg))]
                           (basic/exact q (p-cons Z cb (appendOf Z gb M) (appendOf Z mcy (appendOf Z gb Fg)) inner)))
                         (let [q (simp/simp psg ['List.flatMap_nil 'List.map_nil 'List.append_nil 'List.nil_append])]
                           (basic/exact q (p-refl Z (nilOf Z)))))))
                   ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-flatMap-map-comm []
  (let [fX (e/fvar 1) fY (e/fvar 2) fZ (e/fvar 3)
        fTy (e/forall' "_" fX (e/forall' "_" fY fZ :default) :default)
        ff (e/fvar 4) fxs (e/fvar 5) fys (e/fvar 6)
        innerL (e/lam "x" fX (mapOf fY fZ (e/lam "y" fY (e/app* ff (e/bvar 1) (e/bvar 0)) :default) fys) :default)
        innerR (e/lam "y" fY (mapOf fX fZ (e/lam "x" fX (e/app* ff (e/bvar 0) (e/bvar 1)) :default) fxs) :default)
        body (permOf fZ (flatMap fX fZ innerL fxs) (flatMap fY fZ innerR fys))
        goal (-> body
                 (#(e/forall' "ys" (listOf fY) (e/abstract1 % 6) :default))
                 (#(e/forall' "xs" (listOf fX) (e/abstract1 % 5) :default))
                 (#(e/forall' "f" fTy (e/abstract1 % 4) :default))
                 (#(e/forall' "Z" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "Y" "Z" "f" "xs" "ys"])
        ps (basic/induction ps (fvid ps "xs"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))
                    X (gf psg "X") Y (gf psg "Y") Z (gf psg "Z") f (gf psg "f") ys (gf psg "ys")]
                (if cons?
                  (let [ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        a (gf psg "head") xs' (gf psg "tail")
                        gfn (e/lam "y" Y (e/app* f a (e/bvar 0)) :default)
                        A (mapOf Y Z gfn ys)
                        innerL' (e/lam "x" X (mapOf Y Z (e/lam "y" Y (e/app* f (e/bvar 1) (e/bvar 0)) :default) ys) :default)
                        LT (flatMap X Z innerL' xs')
                        gpY (e/lam "y" Y (mapOf X Z (e/lam "x" X (e/app* f (e/bvar 0) (e/bvar 1)) :default) xs') :default)
                        RT (flatMap Y Z gpY ys)
                        RHS' (flatMap Y Z (e/lam "y" Y (mapOf X Z (e/lam "x" X (e/app* f (e/bvar 0) (e/bvar 1)) :default)
                                                            (e/app* (e/const' (nm "List.cons") [z]) X a xs')) :default) ys)
                        q (simp/simp psg ['List.flatMap_cons 'List.map_cons])
                        h4p (e/app* (e/const' (nm "List.flatMap_cons_distrib_perm") []) Y Z gfn gpY ys)]
                    (basic/exact q (p-trans Z (appendOf Z A LT) (appendOf Z A RT) RHS'
                                            (p-aleft Z LT RT A (e/fvar ihid))
                                            (p-symm Z RHS' (appendOf Z A RT) h4p))))
                  (let [psg (basic/induction psg (fvid psg "ys"))]
                    (reduce (fn [pg gid2]
                              (let [pg2 (focus pg gid2)
                                    cons2? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal pg2)))]
                                (if cons2?
                                  (basic/exact pg2 (e/fvar (or (fvid pg2 "ih_tail'") (fvid pg2 "ih_tail") (fvid pg2 "ih"))))
                                  (basic/exact pg2 (p-refl Z (nilOf Z))))))
                            psg (vec (:goals psg)))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-foldflip-perm []
  (let [A (e/fvar 1) fl (e/fvar 2)
        flip (e/lam "acc" (listOf A) (e/lam "x" A (consOf A (e/bvar 0) (e/bvar 1)) :default) :default)
        accBody (permOf A (foldlOf A (e/fvar 3) fl flip) (appendOf A (e/fvar 3) fl))
        body (e/forall' "acc" (listOf A) (e/abstract1 accBody 3) :default)
        goal (-> body
                 (#(e/forall' "l" (listOf A) (e/abstract1 % 2) :default))
                 (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["A" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))
                    A (gf psg "A")
                    flip (e/lam "acc" (listOf A) (e/lam "x" A (consOf A (e/bvar 0) (e/bvar 1)) :default) :default)]
                (if cons?
                  (let [psg (basic/intros psg ["acc"])
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        b (gf psg "head") l' (gf psg "tail") acc (gf psg "acc")
                        x (foldlOf A acc (consOf A b l') flip)
                        y (appendOf A (consOf A b acc) l')
                        w (appendOf A acc (consOf A b l'))]
                    (basic/exact psg (p-trans A x y w (e/app (e/fvar ihid) (consOf A b acc))
                                              (p-caa A (singletonOf A b) acc l'))))
                  (let [psg (basic/intros psg ["acc"])
                        q (simp/simp psg ['List.foldl_nil 'List.append_nil])]
                    (basic/exact q (p-refl A (gf q "acc")))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; foldl over a PERMUTED list is unchanged when the step op is LEFT-COMMUTATIVE
;;   (∀ a u v, op (op a u) v = op (op a v) u).  This is the consumer half of grace-hash:
;; the block-partition law produces a PERMUTATION of the join result, and an aggregate that
;; commutes (sum/count/…) is invariant under it. Proved directly via List.Perm.rec (the induction
;; tactic builds a degenerate motive for multi-index Prop inductives), with the motive generalized
;; over the accumulator so the cons case can re-aim the IH at `op e0 x`. swap case = congrArg on the
;; left-comm hypothesis; trans case = Eq.trans of the two IHs.
(defn prove-foldl-perm-lcomm []
  (let [B (e/fvar 1) A (e/fvar 2) op (e/fvar 3) l1 (e/fvar 5) l2 (e/fvar 6)
        foldlG (fn [init l] (e/app* (e/const' (nm "List.foldl") [z z]) B A op init l))
        LA (listOf A) nilA (nilOf A)
        opTy (e/forall' "_" B (e/forall' "_" A B :default) :default)
        lcTy (e/forall' "a" B (e/forall' "x" A (e/forall' "y" A
                (e/app* (e/const' (nm "Eq") [L1]) B
                        (e/app* op (e/app* op (e/bvar 2) (e/bvar 1)) (e/bvar 0))
                        (e/app* op (e/app* op (e/bvar 2) (e/bvar 0)) (e/bvar 1)))
                :default) :default) :default)
        concl (e/forall' "e0" B (e/app* (e/const' (nm "Eq") [L1]) B
                                        (foldlG (e/bvar 0) l1) (foldlG (e/bvar 0) l2)) :default)
        goal (-> concl
                 (#(e/forall' "p" (permOf A l1 l2) % :default))
                 (#(e/forall' "l2" LA (e/abstract1 % 6) :default))
                 (#(e/forall' "l1" LA (e/abstract1 % 5) :default))
                 (#(e/forall' "lc" lcTy % :default))
                 (#(e/forall' "op" opTy (e/abstract1 % 3) :default))
                 (#(e/forall' "A" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "B" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["B" "A" "op" "lc" "l1" "l2" "p"])
        Bf (gf ps "B") Af (gf ps "A") opf (gf ps "op") lcf (gf ps "lc")
        l1f (gf ps "l1") l2f (gf ps "l2") pf (gf ps "p")
        fG (fn [init l] (e/app* (e/const' (nm "List.foldl") [z z]) Bf Af opf init l))
        eqB* (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) Bf x y))
        permA* (fn [x y] (permOf Af x y))
        ;; motive : λ (a b : List A)(h : Perm A a b). ∀ e0:B, foldl op e0 a = foldl op e0 b
        mEq (eqB* (fG (e/bvar 0) (e/bvar 3)) (fG (e/bvar 0) (e/bvar 2)))
        motive (e/lam "a" (listOf Af) (e/lam "b" (listOf Af)
                 (e/lam "h" (permA* (e/bvar 1) (e/bvar 0)) (e/forall' "e0" Bf mEq :default) :default) :default) :default)
        cnil (e/lam "e0" Bf (e/app* (e/const' (nm "Eq.refl") [L1]) Bf (fG (e/bvar 0) (nilOf Af))) :default)
        ihTy (e/forall' "e0" Bf (eqB* (fG (e/bvar 0) (e/bvar 3)) (fG (e/bvar 0) (e/bvar 2))) :default)
        ccons (e/lam "a" Af (e/lam "p1" (listOf Af) (e/lam "p2" (listOf Af)
                (e/lam "h" (permA* (e/bvar 1) (e/bvar 0)) (e/lam "ih" ihTy
                  (e/lam "e0" Bf (e/app (e/bvar 1) (e/app* opf (e/bvar 0) (e/bvar 5))) :default)
                  :default) :default) :default) :default) :default)
        ;; swap: Perm.swap x y l : Perm (y::x::l)(x::y::l) ⇒ foldl(y::x::l)=foldl(x::y::l)
        W1 (e/app* opf (e/app* opf (e/bvar 0) (e/bvar 2)) (e/bvar 3))
        W2 (e/app* opf (e/app* opf (e/bvar 0) (e/bvar 3)) (e/bvar 2))
        fW (e/lam "w" Bf (fG (e/bvar 0) (e/bvar 2)) :default)
        cswap (e/lam "x" Af (e/lam "y" Af (e/lam "l" (listOf Af)
                (e/lam "e0" Bf
                  (e/app* (e/const' (nm "congrArg") [L1 L1]) Bf Bf W1 W2 fW
                          (e/app* lcf (e/bvar 0) (e/bvar 2) (e/bvar 3))) :default)
                :default) :default) :default)
        ihpTy (e/forall' "e0" Bf (eqB* (fG (e/bvar 0) (e/bvar 5)) (fG (e/bvar 0) (e/bvar 4))) :default)
        ctrans (e/lam "l1" (listOf Af) (e/lam "l2" (listOf Af) (e/lam "l3" (listOf Af)
                 (e/lam "p" (permA* (e/bvar 2) (e/bvar 1)) (e/lam "q" (permA* (e/bvar 2) (e/bvar 1))
                   (e/lam "ihp" ihpTy (e/lam "ihq" ihpTy
                     (e/lam "e0" Bf
                       (e/app* (e/const' (nm "Eq.trans") [L1]) Bf
                               (fG (e/bvar 0) (e/bvar 7)) (fG (e/bvar 0) (e/bvar 6)) (fG (e/bvar 0) (e/bvar 5))
                               (e/app (e/bvar 2) (e/bvar 0)) (e/app (e/bvar 1) (e/bvar 0))) :default)
                     :default) :default) :default) :default) :default) :default) :default)
        recterm (e/app* (e/const' (nm "List.Perm.rec") [z]) Af motive cnil ccons cswap ctrans l1f l2f pf)
        ps (basic/exact ps recterm)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── §3 bucket ───────────────────────────────────────────────────────────────
(def ^:private fK (e/fvar 1)) (def ^:private fV (e/fvar 2)) (def ^:private fd (e/fvar 3))
(def ^:private ff (e/fvar 4)) (def ^:private fk (e/fvar 5)) (def ^:private fys (e/fvar 6)) (def ^:private fm (e/fvar 7))
(def ^:private beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd))
(def ^:private listV (e/app (e/const' (nm "List") [z]) fV))
(def ^:private mapKLV (e/app* (e/const' (nm "Map") [z z]) fK listV))
(def ^:private deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK))
(def ^:private vk (e/forall' "_" fV fK :default))
(def ^:private nilV (e/app (e/const' (nm "List.nil") [z]) fV))
(defn- mlook [key m] (e/app* (e/const' (nm "Map.lookup") []) fK listV fd key m))
(defn- getD [o] (e/app* (e/const' (nm "Option.getD") [z]) listV o nilV))
(defn- beqg [a b] (e/app* (e/const' (nm "BEq.beq") [z]) fK beqI a b))
(def ^:private gbstep
  (e/lam "m" mapKLV (e/lam "x" fV
    (let [x (e/bvar 0) m (e/bvar 1) fx (e/app ff x)
          bk (e/app* (e/const' (nm "List.cons") [z]) fV x (getD (mlook fx m)))]
      (e/app* (e/const' (nm "Map.insert") []) fK listV fd fx bk m)) :default) :default))
(defn- foldl-step [m l] (e/app* (e/const' (nm "List.foldl") [z z]) mapKLV fV gbstep m l))
(def ^:private filt-pred (e/lam "x" fV (beqg fk (e/app ff (e/bvar 0))) :default))
(defn- filt [l] (e/app* (e/const' (nm "List.filter") [z]) fV filt-pred l))
(def ^:private flipcons (e/lam "acc" listV (e/lam "x" fV (e/app* (e/const' (nm "List.cons") [z]) fV (e/bvar 0) (e/bvar 1)) :default) :default))
(defn- foldflip [acc l] (e/app* (e/const' (nm "List.foldl") [z z]) listV fV flipcons acc l))
(defn- close6 [b]
  (-> b (#(e/forall' "ys" listV (e/abstract1 % 6) :default)) (#(e/forall' "k" fK (e/abstract1 % 5) :default))
      (#(e/forall' "f" vk (e/abstract1 % 4) :default)) (#(e/forall' "dec" deceqK (e/abstract1 % 3) :default))
      (#(e/forall' "V" type0 (e/abstract1 % 2) :default)) (#(e/forall' "K" type0 (e/abstract1 % 1) :default))))
(defn- beqp [ps a b] (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) a b))
(def ^:private LEM ['List.foldl_nil 'List.foldl_cons 'List.filter_nil 'List.filter_cons_of_pos 'List.filter_cons_of_neg
                    'cond 'cond_true 'cond_false 'Option.getD 'Map.lookup_insert])

(defn prove-bucket-gen []
  (let [gen-goal (close6 (e/forall' "m" mapKLV
                           (e/abstract1 (e/app* (e/const' (nm "Eq") [L1]) listV
                                                (getD (mlook fk (foldl-step fm fys)))
                                                (foldflip (getD (mlook fk fm)) (filt fys))) 7) :default))
        [ps _] (proof/start-proof (a/env) gen-goal)
        ps (basic/intros ps ["K" "V" "dec" "f" "k" "ys"])
        ps (basic/induction ps (fvid ps "ys"))
        ps (reduce
             (fn [ps gid]
               (let [psg (focus ps gid)
                     cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))]
                 (if cons?
                   (let [psg (basic/intros psg ["m"])
                         hd (gf psg "head") mm (gf psg "m")
                         ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                         q (try (simp/simp psg ['List.foldl_cons]) (catch Throwable _ psg))
                         gK (gf psg "K") gd (gf psg "dec") gV (gf psg "V")
                         glistV (e/app (e/const' (nm "List") [z]) gV)
                         gmap (e/app* (e/const' (nm "Map") [z z]) gK glistV)
                         pstep (e/lam "m" gmap (e/lam "x" gV
                                 (let [x (e/bvar 0) m (e/bvar 1) fx (e/app (gf psg "f") x)
                                       bk (e/app* (e/const' (nm "List.cons") [z]) gV x (e/app* (e/const' (nm "Option.getD") [z]) glistV (e/app* (e/const' (nm "Map.lookup") []) gK glistV gd fx m) (e/app (e/const' (nm "List.nil") [z]) gV)))]
                                   (e/app* (e/const' (nm "Map.insert") []) gK glistV gd fx bk m)) :default) :default)
                         ih-at (e/app (e/fvar ihid) (e/app* pstep mm hd))
                         q (try (basic/rewrite q ih-at) (catch Throwable _ q))
                         br (basic/by-cases q (beqp q (gf q "k") (e/app (gf q "f") hd)))
                         bids (new-goals (:goals q) (:goals br))]
                     (reduce (fn [qq bid]
                               (let [qb (focus qq bid)
                                     hc (fvid qb "hc")
                                     removed? (= "Bool.true" (name/->string (e/const-name (nth (second (e/get-app-fn-args (:type (some (fn [[_ d]] (when (= "hc" (:name d)) d)) (:lctx (proof/current-goal qb)))))) 2))))
                                     r (try (basic/rewrite qb (e/fvar hc)) (catch Throwable _ qb))
                                     r (try (simp/simp-all r LEM) (catch Throwable _ r))
                                     r (if removed?
                                         (let [gK (gf r "K") gd (gf r "dec")
                                               lawfulP (e/app* (e/const' (nm "instLawfulBEqOfDecidableEq") []) gK gd)
                                               biff (e/app* (e/const' (nm "beq_iff_eq") [z]) gK (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) gK gd) lawfulP (gf r "k") (e/app (gf r "f") hd))
                                               hfeq (e/app* (e/const' (nm "Iff.mp") []) (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") []) (beqp r (gf r "k") (e/app (gf r "f") hd)) (e/const' (nm "Bool.true") [])) (e/app* (e/const' (nm "Eq") [L1]) gK (gf r "k") (e/app (gf r "f") hd)) biff (e/fvar hc))
                                               r2 (try (basic/rewrite r hfeq) (catch Throwable _ r))]
                                           (try (simp/simp-all r2 LEM) (catch Throwable _ r2)))
                                         (try (simp/simp-all r LEM) (catch Throwable _ r)))]
                                 (if (proof/solved? r) r (try (basic/rfl r) (catch Throwable _ r)))))
                             br bids))
                   (let [psg (basic/intros psg ["m"])
                         q (try (simp/simp-all psg LEM) (catch Throwable _ psg))]
                     (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))))
             ps (vec (:goals ps)))]
    [gen-goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-bucket-final []
  (let [empt (e/app* (e/const' (nm "Map.empty") []) fK listV)
        inline (close6 (e/app* (e/const' (nm "Eq") [L1]) listV (getD (mlook fk (foldl-step empt fys)))
                               (foldflip (getD (mlook fk empt)) (filt fys))))
        const-goal (close6 (e/app* (e/const' (nm "Eq") [L1]) listV
                                   (getD (mlook fk (e/app* (e/const' (nm "Map.group_by") []) fK fV fd ff fys)))
                                   (foldflip nilV (filt fys))))
        [ps _] (proof/start-proof (a/env) inline)
        ps (basic/intros ps ["K" "V" "dec" "f" "k" "ys"])
        gempt (e/app* (e/const' (nm "Map.empty") []) (gf ps "K") (e/app (e/const' (nm "List") [z]) (gf ps "V")))
        gen-app (e/app* (e/const' (nm "Map.bucket_content_gen") []) (gf ps "K") (gf ps "V") (gf ps "dec") (gf ps "f") (gf ps "k") (gf ps "ys") gempt)
        ps (basic/exact ps gen-app)]
    [const-goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── §4 join (commutativity capstone + Perm→Eq count bridge) ──────────────────
(defn- close-beqc-leaf [pl]
  (let [gf (fn [n] (e/fvar (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal pl)))))
        K (gf "K") dec (gf "dec") a (gf "a") b (gf "b")
        instB (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        lawful (e/app* (e/const' (nm "instLawfulBEqOfDecidableEq") []) K dec)
        beqg (fn [x y] (e/app* (e/const' (nm "BEq.beq") [z]) K instB x y))
        biff (fn [x y] (e/app* (e/const' (nm "beq_iff_eq") [z]) K instB lawful x y))
        ab-t (beqg a b) ba-t (beqg b a)
        hyps (filter (fn [[_ d]] (= :local (:tag d))) (:lctx (proof/current-goal pl)))
        find-hyp (fn [bt] (some (fn [[id d]] (let [[h ar] (e/get-app-fn-args (:type d))]
                                              (when (and (e/const? h) (= "Eq" (name/->string (e/const-name h)))
                                                         (= 3 (count ar)) (.equals (nth ar 1) bt))
                                                [id (nth ar 2)]))) hyps))
        [hc-id v1] (find-hyp ab-t)
        hc (e/fvar hc-id)
        Pt (eqB ab-t btrue) Pe (eqK K a b) Qt (eqB ba-t btrue) Qe (eqK K b a)
        q (if (.equals v1 btrue)
            (let [ab' (imp Pt Pe (biff a b) hc) ba' (sy K a b ab')]
              (impr Qt Qe (biff b a) ba'))
            (let [ht (e/fvar 990001)
                  ba' (imp Qt Qe (biff b a) ht) ab' (sy K b a ba')
                  at' (impr Pt Pe (biff a b) ab')
                  contra (tr boolT btrue ab-t bfalse (sy boolT ab-t btrue at') hc)
                  falsep (e/app* (e/const' (nm "Bool.false_ne_true") []) (sy boolT btrue bfalse contra))]
              (e/app* (e/const' (nm "Bool.of_not_eq_true") []) ba-t
                      (e/lam "ht" Qt (e/abstract1 falsep 990001) :default))))]
    (basic/exact pl (tr boolT ab-t v1 ba-t hc (sy boolT ba-t v1 q)))))

(defn prove-beq-comm []
  (let [fK (e/fvar 1) fd (e/fvar 2) fa (e/fvar 3) fb (e/fvar 4)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        instB0 (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        body (eqB (e/app* (e/const' (nm "BEq.beq") [z]) fK instB0 fa fb)
                  (e/app* (e/const' (nm "BEq.beq") [z]) fK instB0 fb fa))
        goal (-> body
                 (#(e/forall' "b" fK (e/abstract1 % 4) :default))
                 (#(e/forall' "a" fK (e/abstract1 % 3) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "dec" "a" "b"])
        gf (fn [ps n] (e/fvar (fvid ps n)))
        bg (fn [ps x y] (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K")
                                (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) x y))
        ps1 (basic/by-cases ps (bg ps (gf ps "a") (gf ps "b")))
        ps (reduce (fn [ps gid]
                     (let [pg (focus ps gid)
                           pg2 (basic/by-cases pg (bg pg (gf pg "b") (gf pg "a")))
                           leaves (new-goals (:goals pg) (:goals pg2))]
                       (reduce (fn [pg leaf] (close-beqc-leaf (focus pg leaf))) pg2 leaves)))
                   ps1 (vec (:goals ps1)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-bucket-perm []
  (let [fK (e/fvar 1) fV (e/fvar 2) fd (e/fvar 3) ff (e/fvar 4) fk (e/fvar 5) fys (e/fvar 6)
        listV (e/app (e/const' (nm "List") [z]) fV)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        vToK (e/forall' "_" fV fK :default)
        nilV (e/app (e/const' (nm "List.nil") [z]) fV)
        instB (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        grp (e/app* (e/const' (nm "Map.group_by") []) fK fV fd ff fys)
        lk (e/app* (e/const' (nm "Map.lookup") []) fK listV fd fk grp)
        bucket (e/app* (e/const' (nm "Option.getD") [z]) listV lk nilV)
        pred (e/lam "x" fV (e/app* (e/const' (nm "BEq.beq") [z]) fK instB fk (e/app ff (e/bvar 0))) :default)
        filt (e/app* (e/const' (nm "List.filter") [z]) fV pred fys)
        body (e/app* (e/const' (nm "List.Perm") [z]) fV bucket filt)
        goal (-> body
                 (#(e/forall' "ys" listV (e/abstract1 % 6) :default))
                 (#(e/forall' "k" fK (e/abstract1 % 5) :default))
                 (#(e/forall' "f" vToK (e/abstract1 % 4) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 3) :default))
                 (#(e/forall' "V" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "dec" "f" "k" "ys"])
        gf (fn [n] (e/fvar (fvid ps n)))
        K (gf "K") V (gf "V") dec (gf "dec") f (gf "f") k (gf "k") ys (gf "ys")
        gnil (e/app (e/const' (nm "List.nil") [z]) V)
        ginstB (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec)
        gpred (e/lam "x" V (e/app* (e/const' (nm "BEq.beq") [z]) K ginstB k (e/app f (e/bvar 0))) :default)
        gfilt (e/app* (e/const' (nm "List.filter") [z]) V gpred ys)
        ps (basic/rewrite ps (e/app* (e/const' (nm "Map.bucket_content") []) K V dec f k ys))
        ps (basic/exact ps (e/app* (e/const' (nm "List.foldl_cons_perm") []) V gfilt gnil))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn prove-claim-a []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys (e/fvar 8)
        PXY (prodT X Y) listY (listOf Y)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        bucket (fn [k'] (e/app* (e/const' (nm "Option.getD") [z]) listY
                                (e/app* (e/const' (nm "Map.lookup") []) K listY dec k'
                                        (e/app* (e/const' (nm "Map.group_by") []) K Y dec lf ys))
                                (nilOf Y)))
        mkF (e/lam "y" Y (e/app* (e/const' (nm "Prod.mk") [z z]) X Y (e/bvar 1) (e/bvar 0)) :default)
        matchF (e/lam "y" Y (beqK K dec (e/app kf (e/bvar 1)) (e/app lf (e/bvar 0))) :default)
        F (e/lam "x" X (mapOf Y PXY mkF (bucket (e/app kf (e/bvar 0)))) :default)
        G (e/lam "x" X (mapOf Y PXY mkF (filterOf Y matchF ys)) :default)
        H (e/lam "x" X
            (e/app* (e/const' (nm "List.Perm.map") [z z]) Y PXY mkF
                    (bucket (e/app kf (e/bvar 0))) (filterOf Y matchF ys)
                    (e/app* (e/const' (nm "Map.bucket_perm") []) K Y dec lf (e/app kf (e/bvar 0)) ys))
            :default)
        body (e/app* (e/const' (nm "List.flatMap_congr_perm") []) X PXY F G H xs)
        goal-body (e/app* (e/const' (nm "List.Perm") [z]) PXY (flatMapOf X PXY F xs) (flatMapOf X PXY G xs))
        wrap (fn [t lam?]
               (let [b (if lam? e/lam e/forall')]
                 (-> t
                     (#(b "ys" listY (e/abstract1 % 8) :default)) (#(b "xs" (listOf X) (e/abstract1 % 7) :default))
                     (#(b "lf" yToK (e/abstract1 % 6) :default)) (#(b "kf" xToK (e/abstract1 % 5) :default))
                     (#(b "dec" deceqK (e/abstract1 % 4) :default)) (#(b "Y" type0 (e/abstract1 % 3) :default))
                     (#(b "X" type0 (e/abstract1 % 2) :default)) (#(b "K" type0 (e/abstract1 % 1) :default)))))]
    [(wrap goal-body false) (wrap body true)]))

(defn prove-join-comm []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys (e/fvar 8)
        PXY (prodT X Y) YX (prodT Y X) listX (listOf X) listY (listOf Y) listP (listOf PXY)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        names ["K" "X" "Y" "dec" "kf" "lf" "xs" "ys"]
        mkF (e/lam "y" Y (mkP X Y (e/bvar 1) (e/bvar 0)) :default)
        mkG (e/lam "x" X (mkP X Y (e/bvar 0) (e/bvar 1)) :default)
        matchF (e/lam "y" Y (beqK K dec (e/app kf (e/bvar 1)) (e/app lf (e/bvar 0))) :default)
        matchG (e/lam "x" X (beqK K dec (e/app lf (e/bvar 1)) (e/app kf (e/bvar 0))) :default)
        Q1 (e/lam "p" PXY (beqK K dec (e/app kf (fstOf X Y (e/bvar 0))) (e/app lf (sndOf X Y (e/bvar 0)))) :default)
        Q2 (e/lam "p" PXY (beqK K dec (e/app lf (sndOf X Y (e/bvar 0))) (e/app kf (fstOf X Y (e/bvar 0)))) :default)
        MPa (flatMapOf X PXY (e/lam "x" X (mapOf Y PXY mkF (filterOf Y matchF ys)) :default) xs)
        MPb' (flatMapOf Y PXY (e/lam "y" Y (mapOf X PXY mkG (filterOf X matchG xs)) :default) ys)
        Prodxy (flatMapOf X PXY (e/lam "x" X (mapOf Y PXY mkF ys) :default) xs)
        Prodyx (flatMapOf Y PXY (e/lam "y" Y (mapOf X PXY mkG xs) :default) ys)
        wrapF (fn [t] (-> t
                          (#(e/forall' "ys" listY (e/abstract1 % 8) :default)) (#(e/forall' "xs" listX (e/abstract1 % 7) :default))
                          (#(e/forall' "lf" yToK (e/abstract1 % 6) :default)) (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                          (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default)) (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                          (#(e/forall' "X" type0 (e/abstract1 % 2) :default)) (#(e/forall' "K" type0 (e/abstract1 % 1) :default))))
        wrapL (fn [t] (-> t
                          (#(e/lam "ys" listY (e/abstract1 % 8) :default)) (#(e/lam "xs" listX (e/abstract1 % 7) :default))
                          (#(e/lam "lf" yToK (e/abstract1 % 6) :default)) (#(e/lam "kf" xToK (e/abstract1 % 5) :default))
                          (#(e/lam "dec" deceqK (e/abstract1 % 4) :default)) (#(e/lam "Y" type0 (e/abstract1 % 3) :default))
                          (#(e/lam "X" type0 (e/abstract1 % 2) :default)) (#(e/lam "K" type0 (e/abstract1 % 1) :default))))
        lems ['List.filter_flatMap 'List.filter_map 'Function.comp]
        pa (eq-via-simp (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPa (filterOf PXY Q1 Prodxy))) lems names)
        pb (eq-via-simp (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPb' (filterOf PXY Q2 Prodyx))) lems names)
        _ (reg-anon! "Map.pushout_a" (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPa (filterOf PXY Q1 Prodxy))) pa)
        _ (reg-anon! "Map.pushout_b" (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPb' (filterOf PXY Q2 Prodyx))) pb)
        qeq-goal (wrapF (e/app* (e/const' (nm "Eq") [(lvl/imax L1 L1)]) (e/forall' "_" PXY boolT :default) Q1 Q2))
        qeq-pf (wrapL (e/app* (e/const' (nm "funext") [L1 L1]) PXY (e/lam "_" PXY boolT :default) Q1 Q2
                             (e/lam "p" PXY (e/app* (e/const' (nm "BEq.beq_comm") []) K dec
                                                    (e/app kf (fstOf X Y (e/bvar 0))) (e/app lf (sndOf X Y (e/bvar 0)))) :default)))
        _ (reg-anon! "Map.qeq" qeq-goal qeq-pf)
        cgoal (wrapF (e/app* (e/const' (nm "List.Perm") [z]) PXY MPa MPb'))
        claimc (let [[ps _] (proof/start-proof (a/env) cgoal)
                     ps (basic/intros ps names)
                     gf (fn [n] (e/fvar (fvid ps n)))
                     gK (gf "K") gX (gf "X") gY (gf "Y") gd (gf "dec") gkf (gf "kf") glf (gf "lf") gxs (gf "xs") gys (gf "ys")
                     gP (prodT gX gY)
                     inst (fn [n] (e/app* (e/const' (nm n) []) gK gX gY gd gkf glf gxs gys))
                     gQ2 (e/lam "p" gP (beqK gK gd (e/app glf (sndOf gX gY (e/bvar 0))) (e/app gkf (fstOf gX gY (e/bvar 0)))) :default)
                     gmkF (e/lam "y" gY (mkP gX gY (e/bvar 1) (e/bvar 0)) :default)
                     gmkG (e/lam "x" gX (mkP gX gY (e/bvar 0) (e/bvar 1)) :default)
                     gPxy (flatMapOf gX gP (e/lam "x" gX (mapOf gY gP gmkF gys) :default) gxs)
                     gPyx (flatMapOf gY gP (e/lam "y" gY (mapOf gX gP gmkG gxs) :default) gys)
                     gh6 (e/app* (e/const' (nm "List.flatMap_map_comm") []) gX gY gP
                                 (e/lam "x" gX (e/lam "y" gY (mkP gX gY (e/bvar 1) (e/bvar 0)) :default) :default) gxs gys)
                     ps (basic/rewrite ps (inst "Map.pushout_a"))
                     ps (basic/rewrite ps (inst "Map.pushout_b"))
                     ps (basic/rewrite ps (inst "Map.qeq"))
                     ps (basic/exact ps (e/app* (e/const' (nm "List.Perm.filter") [z]) gP gQ2 gPxy gPyx gh6))]
                 (when (proof/solved? ps) (extract/extract ps)))
        _ (reg-anon! "Map.join_MPa_MPb" cgoal claimc)
        swapYX (e/lam "p" YX (e/app* (e/const' (nm "Prod.swap") [z z]) Y X (e/bvar 0)) :default)
        MPb (flatMapOf Y YX (e/lam "y" Y (mapOf X YX (e/lam "x" X (mkP Y X (e/bvar 1) (e/bvar 0)) :default) (filterOf X matchG xs)) :default) ys)
        ms2-goal (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPb' (mapOf YX PXY swapYX MPb)))
        ms2 (eq-via-simp ms2-goal ['List.map_flatMap 'List.map_map 'Function.comp 'Prod.swap] names)
        _ (reg-anon! "Map.msEq2" ms2-goal ms2)
        joinB (fn [Kc A B d af bf as_ bs]
                (let [listB (listOf B) PAB (prodT A B)
                      bk (e/app* (e/const' (nm "Option.getD") [z]) listB
                                 (e/app* (e/const' (nm "Map.lookup") []) Kc listB d (e/app af (e/bvar 0))
                                         (e/app* (e/const' (nm "Map.group_by") []) Kc B d bf bs))
                                 (e/app (e/const' (nm "List.nil") [z]) B))]
                  (flatMapOf A PAB (e/lam "a" A (mapOf B PAB (e/lam "b" B (mkP A B (e/bvar 1) (e/bvar 0)) :default) bk) :default) as_)))
        msp-goal (wrapF (e/app* (e/const' (nm "List.Perm") [z]) PXY (mapOf YX PXY swapYX (joinB K Y X dec lf kf ys xs)) MPb'))
        msp (let [[ps _] (proof/start-proof (a/env) msp-goal)
                  ps (basic/intros ps names)
                  gf (fn [n] (e/fvar (fvid ps n)))
                  gK (gf "K") gX (gf "X") gY (gf "Y") gd (gf "dec") gkf (gf "kf") glf (gf "lf") gxs (gf "xs") gys (gf "ys")
                  gP (prodT gX gY) gYX (prodT gY gX)
                  gswap (e/lam "p" gYX (e/app* (e/const' (nm "Prod.swap") [z z]) gY gX (e/bvar 0)) :default)
                  gjoinYX (joinB gK gY gX gd glf gkf gys gxs)
                  gmatchG (e/lam "x" gX (beqK gK gd (e/app glf (e/bvar 1)) (e/app gkf (e/bvar 0))) :default)
                  gMPb (flatMapOf gY gYX (e/lam "y" gY (mapOf gX gYX (e/lam "x" gX (mkP gY gX (e/bvar 1) (e/bvar 0)) :default) (filterOf gX gmatchG gxs)) :default) gys)
                  claimA-i (e/app* (e/const' (nm "Map.join_filtered_product") []) gK gY gX gd glf gkf gys gxs)
                  ms2-i (e/app* (e/const' (nm "Map.msEq2") []) gK gX gY gd gkf glf gxs gys)
                  ps (basic/rewrite ps ms2-i)
                  ps (basic/exact ps (e/app* (e/const' (nm "List.Perm.map") [z z]) gYX gP gswap gjoinYX gMPb claimA-i))]
              (when (proof/solved? ps) (extract/extract ps)))
        _ (reg-anon! "Map.join_mapswap" msp-goal msp)
        i8 (fn [n a b c d* e* f* g* h] (e/app* (e/const' (nm n) []) a b c d* e* f* g* h))
        claimA8 (i8 "Map.join_filtered_product" K X Y dec kf lf xs ys)
        claimC8 (i8 "Map.join_MPa_MPb" K X Y dec kf lf xs ys)
        msp8 (i8 "Map.join_mapswap" K X Y dec kf lf xs ys)
        swapYX2 (e/lam "p" YX (e/app* (e/const' (nm "Prod.swap") [z z]) Y X (e/bvar 0)) :default)
        mapswap (mapOf YX PXY swapYX2 (joinB K Y X dec lf kf ys xs))
        inner (e/app* (e/const' (nm "List.Perm.trans") [z]) PXY MPa MPb' mapswap claimC8
                      (e/app* (e/const' (nm "List.Perm.symm") [z]) PXY mapswap MPb' msp8))
        jc-body (e/app* (e/const' (nm "List.Perm.trans") [z]) PXY (joinB K X Y dec kf lf xs ys) MPa mapswap claimA8 inner)
        joinC (fn [A B af bf as_ bs] (e/app* (e/const' (nm "Map.join") []) K A B dec af bf as_ bs))
        jc-goal (wrapF (e/app* (e/const' (nm "List.Perm") [z]) PXY (joinC X Y kf lf xs ys)
                               (mapOf YX PXY swapYX2 (joinC Y X lf kf ys xs))))]
    [jc-goal (wrapL jc-body)]))

(defn prove-join-length-comm []
  (let [jc (kenv/lookup (a/env) (nm "Map.join_comm"))
        jct (.type jc)
        [params body] (loop [t jct ps []]
                        (if (e/forall? t)
                          (recur (e/forall-body t) (conj ps [(e/forall-name t) (e/forall-type t) (e/forall-info t)]))
                          [ps t]))
        nP (count params)
        [_ pa] (e/get-app-fn-args body)
        elemTy (nth pa 0) lhs (nth pa 1) rhs (nth pa 2)
        [_ ma] (e/get-app-fn-args rhs)
        srcTy (nth ma 0) dstTy (nth ma 1) swap (nth ma 2) join' (nth ma 3)
        natT (e/const' (nm "Nat") [])
        len (fn [ty l] (e/app* (e/const' (nm "List.length") [z]) ty l))
        jc-app (apply e/app* (e/const' (nm "Map.join_comm") []) (map e/bvar (range (dec nP) -1 -1)))
        perm-len (e/app* (e/const' (nm "List.Perm.length_eq") [z]) elemTy lhs rhs jc-app)
        len-map (e/app* (e/const' (nm "List.length_map") [z z]) srcTy dstTy join' swap)
        gbody (e/app* (e/const' (nm "Eq") [L1]) natT (len elemTy lhs) (len srcTy join'))
        pbody (e/app* (e/const' (nm "Eq.trans") [L1]) natT (len elemTy lhs) (len dstTy rhs) (len srcTy join') perm-len len-map)
        goal (reduce (fn [b [nm- ty bi]] (e/forall' nm- ty b bi)) gbody (reverse params))
        proof (reduce (fn [b [nm- ty _]] (e/lam nm- ty b :default)) pbody (reverse params))]
    [goal proof]))

;; ── §5 grace-hash (block-partitioned spill join) ──────────────────────────────
;; The certified algebra that lets `foldl op e (Map.join xs ys)` be evaluated in
;; budget-sized BLOCKS of the build side (O(budget) peak memory): partition ys, build a
;; group_by index per block, fold, combine. Correct because the block results are a
;; PERMUTATION of the whole join and a left-commutative aggregate (sum/count) is
;; permutation-invariant ([[List.foldl_perm_lcomm]]).  All Init + the verified Map foundation.
(defn- gh-joinOf [K X Y dec kf lf xs ys] (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys))
(defn- gh-flattenOf [a ls] (e/app* (e/const' (nm "List.flatten") [z]) a ls))
(defn- gh-foldlG [B A op init l] (e/app* (e/const' (nm "List.foldl") [z z]) B A op init l))
;; filt-form xs ys = flatMap (λx. map (λy.(x,y)) (filter (λy. kf x =· lf y) ys)) xs  (the per-row join)
(defn- gh-filt-form [K X Y dec kf lf xs ys]
  (let [PXY (prodT X Y)
        mF (e/lam "y" Y (mkP X Y (e/bvar 1) (e/bvar 0)) :default)
        mtch (e/lam "y" Y (beqK K dec (e/app kf (e/bvar 1)) (e/app lf (e/bvar 0))) :default)
        Fb (e/lam "x" X (mapOf Y PXY mF (filterOf Y mtch ys)) :default)]
    (flatMap X PXY Fb xs)))
;; eqToPerm: Eq a b → Perm a b  (Eq.subst with motive λw. Perm a w)
(defn- gh-eqToPerm [elem a b eqab]
  (let [la (listOf elem) motive (e/lam "w" la (permOf elem a (e/bvar 0)) :default)]
    (e/app* (e/const' (nm "Eq.subst") [L1]) la motive a b eqab (p-refl elem a))))
(defn- gh-convC [K X Y dec kf lf xs ys] (e/app* (e/const' (nm "Map.join_filter_form_perm") []) K X Y dec kf lf xs ys))

;; Map.join_filter_form_perm : Map.join xs ys ~ filt-form xs ys  (per-bucket reverse permutation)
(defn prove-join-filter-form-perm []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys (e/fvar 8)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        goal (-> (permOf (prodT X Y) (gh-joinOf K X Y dec kf lf xs ys) (gh-filt-form K X Y dec kf lf xs ys))
                 (#(e/forall' "ys" (listOf Y) (e/abstract1 % 8) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 7) :default))
                 (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "X" "Y" "dec" "kf" "lf" "xs" "ys"])
        ps (simp/simp ps ['Map.join.eq_unfold 'Map.bucket_content])
        K' (gf ps "K") X' (gf ps "X") Y' (gf ps "Y") dec' (gf ps "dec")
        kf' (gf ps "kf") lf' (gf ps "lf") xs' (gf ps "xs") ys' (gf ps "ys")
        PXY (prodT X' Y')
        flipcons (e/lam "acc" (listOf Y') (e/lam "x" Y' (consOf Y' (e/bvar 0) (e/bvar 1)) :default) :default)
        mkfn (e/app* (e/const' (nm "Prod.mk") [z z]) X' Y' (e/bvar 0))
        mtch (e/lam "y" Y' (beqK K' dec' (e/app kf' (e/bvar 1)) (e/app lf' (e/bvar 0))) :default)
        filt (filterOf Y' mtch ys')
        foldflip0 (e/app* (e/const' (nm "List.foldl") [z z]) (listOf Y') Y' flipcons (nilOf Y') filt)
        F1 (e/lam "x" X' (mapOf Y' PXY mkfn foldflip0) :default)
        F2 (e/lam "x" X' (mapOf Y' PXY mkfn filt) :default)
        innerperm (e/app* (e/const' (nm "List.foldl_cons_perm") []) Y' filt (nilOf Y'))
        hmap (e/app* (e/const' (nm "List.Perm.map") [z z]) Y' PXY mkfn foldflip0 filt innerperm)
        h (e/lam "x" X' hmap :default)
        pf (e/app* (e/const' (nm "List.flatMap_congr_perm") []) X' PXY F1 F2 h xs')
        ps (basic/exact ps pf)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.join_append_perm : join xs (ys1++ys2) ~ join xs ys1 ++ join xs ys2
(defn prove-join-append-perm []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys1 (e/fvar 8) ys2 (e/fvar 9)
        PXY (prodT X Y)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        J (fn [ys] (gh-joinOf K X Y dec kf lf xs ys)) FF (fn [ys] (gh-filt-form K X Y dec kf lf xs ys))
        ys12 (appendOf Y ys1 ys2)
        goal (-> (permOf PXY (J ys12) (appendOf PXY (J ys1) (J ys2)))
                 (#(e/forall' "ys2" (listOf Y) (e/abstract1 % 9) :default))
                 (#(e/forall' "ys1" (listOf Y) (e/abstract1 % 8) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 7) :default))
                 (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "X" "Y" "dec" "kf" "lf" "xs" "ys1" "ys2"])
        K' (gf ps "K") X' (gf ps "X") Y' (gf ps "Y") dec' (gf ps "dec")
        kf' (gf ps "kf") lf' (gf ps "lf") xs' (gf ps "xs") ys1' (gf ps "ys1") ys2' (gf ps "ys2")
        PXY' (prodT X' Y')
        J' (fn [ys] (gh-joinOf K' X' Y' dec' kf' lf' xs' ys)) FF' (fn [ys] (gh-filt-form K' X' Y' dec' kf' lf' xs' ys))
        ys12' (appendOf Y' ys1' ys2')
        c12 (gh-convC K' X' Y' dec' kf' lf' xs' ys12')
        tw  (e/app* (e/const' (nm "Map.join_filter_append_perm") []) K' X' Y' dec' kf' lf' xs' ys1' ys2')
        step1 (p-trans PXY' (J' ys12') (FF' ys12') (appendOf PXY' (FF' ys1') (FF' ys2')) c12 tw)
        ap (p-append PXY' (FF' ys1') (J' ys1') (FF' ys2') (J' ys2')
                     (p-symm PXY' (J' ys1') (FF' ys1') (gh-convC K' X' Y' dec' kf' lf' xs' ys1'))
                     (p-symm PXY' (J' ys2') (FF' ys2') (gh-convC K' X' Y' dec' kf' lf' xs' ys2')))
        result (p-trans PXY' (J' ys12') (appendOf PXY' (FF' ys1') (FF' ys2')) (appendOf PXY' (J' ys1') (J' ys2')) step1 ap)
        ps (basic/exact ps result)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.join_nil_right : join xs [] = []
(defn prove-join-nil-right []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7)
        PXY (prodT X Y)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) (listOf PXY) (gh-joinOf K X Y dec kf lf xs (nilOf Y)) (nilOf PXY))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 7) :default))
                 (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "X" "Y" "dec" "kf" "lf" "xs"])
        ps (simp/simp ps ['Map.join.eq_unfold 'Map.bucket_content 'List.filter_nil 'List.map_nil 'List.foldl_nil])
        X' (gf ps "X") Y' (gf ps "Y") PXY' (prodT X' Y')
        ;; leftover flatten(map(λx.nil)xs)=nil ≡ flatMap(λx.nil)xs=nil
        ps (if (proof/solved? ps) ps
             (basic/exact ps (e/app* (e/const' (nm "List.flatMap_const_nil") []) X' PXY' (gf ps "xs"))))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.join_blockfold_perm : join xs (flatten blocks) ~ flatten (map (λblk. join xs blk) blocks)
(defn prove-join-blockfold-perm []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) blocks (e/fvar 8)
        PXY (prodT X Y) LY (listOf Y) LP (listOf PXY)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        joinFn0 (e/lam "blk" LY (gh-joinOf K X Y dec kf lf xs (e/bvar 0)) :default)
        lhs (gh-joinOf K X Y dec kf lf xs (gh-flattenOf Y blocks))
        rhs (gh-flattenOf PXY (mapOf LY LP joinFn0 blocks))
        goal (-> (permOf PXY lhs rhs)
                 (#(e/forall' "blocks" (listOf LY) (e/abstract1 % 8) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 7) :default))
                 (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "X" "Y" "dec" "kf" "lf" "xs" "blocks"])
        K' (gf ps "K") X' (gf ps "X") Y' (gf ps "Y") dec' (gf ps "dec")
        kf' (gf ps "kf") lf' (gf ps "lf") xs' (gf ps "xs") blocks' (gf ps "blocks")
        PXY' (prodT X' Y') LY' (listOf Y') LP' (listOf PXY')
        J (fn [ys] (gh-joinOf K' X' Y' dec' kf' lf' xs' ys))
        joinFn (e/lam "blk" LY' (gh-joinOf K' X' Y' dec' kf' lf' xs' (e/bvar 0)) :default)
        body-of (fn [blE] (permOf PXY' (J (gh-flattenOf Y' blE)) (gh-flattenOf PXY' (mapOf LY' LP' joinFn blE))))
        motive (e/lam "bl" (listOf LY') (body-of (e/bvar 0)) :default)
        base (gh-eqToPerm PXY' (J (nilOf Y')) (nilOf PXY')
                          (e/app* (e/const' (nm "Map.join_nil_right") []) K' X' Y' dec' kf' lf' xs'))
        ihType (body-of (e/bvar 0))
        fR (gh-flattenOf Y' (e/bvar 1)) jmR (gh-flattenOf PXY' (mapOf LY' LP' joinFn (e/bvar 1)))
        jb (J (e/bvar 2)) jR (J fR)
        ap (e/app* (e/const' (nm "Map.join_append_perm") []) K' X' Y' dec' kf' lf' xs' (e/bvar 2) fR)
        pa (p-append PXY' jb jb jR jmR (p-refl PXY' jb) (e/bvar 0))
        result (p-trans PXY' (J (appendOf Y' (e/bvar 2) fR)) (appendOf PXY' jb jR) (appendOf PXY' jb jmR) ap pa)
        cons (e/lam "b" LY' (e/lam "rest" (listOf LY') (e/lam "ih" ihType result :default) :default) :default)
        recterm (e/app* (e/const' (nm "List.rec") [z z]) LY' motive base cons blocks')
        ps (basic/exact ps recterm)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.foldl_join_blockfold : for left-commutative op,
;;   foldl op e (join xs (flatten blocks)) = foldl (λacc blk. foldl op acc (join xs blk)) e blocks
;; THE law the optimizer applies: with blocks = chunk B ys (+ flatten_chunk) it spills the join in
;; budget-sized blocks. Assembly: foldl_perm_lcomm[blockfold] ∘ foldl_flatten ∘ foldl_map.
(defn prove-foldl-join-blockfold []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6)
        B (e/fvar 10) op (e/fvar 11) e0 (e/fvar 13) xs (e/fvar 14) blocks (e/fvar 15)
        PXY (prodT X Y) LY (listOf Y) LP (listOf PXY)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        opTy (e/forall' "_" B (e/forall' "_" PXY B :default) :default)
        lcTy (e/forall' "a" B (e/forall' "u" PXY (e/forall' "v" PXY
               (e/app* (e/const' (nm "Eq") [L1]) B
                       (e/app* op (e/app* op (e/bvar 2) (e/bvar 1)) (e/bvar 0))
                       (e/app* op (e/app* op (e/bvar 2) (e/bvar 0)) (e/bvar 1))) :default) :default) :default)
        J (fn [ys] (gh-joinOf K X Y dec kf lf xs ys))
        innerStep (e/lam "acc" B (e/lam "blk" LY (gh-foldlG B PXY op (e/bvar 1) (J (e/bvar 0))) :default) :default)
        lhs (gh-foldlG B PXY op e0 (J (gh-flattenOf Y blocks)))
        rhs (gh-foldlG B LY innerStep e0 blocks)
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) B lhs rhs)
                 (#(e/forall' "blocks" (listOf LY) (e/abstract1 % 15) :default))
                 (#(e/forall' "xs" (listOf X) (e/abstract1 % 14) :default))
                 (#(e/forall' "e" B (e/abstract1 % 13) :default))
                 (#(e/forall' "lc" lcTy % :default))
                 (#(e/forall' "op" opTy (e/abstract1 % 11) :default))
                 (#(e/forall' "B" type0 (e/abstract1 % 10) :default))
                 (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                 (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "X" "Y" "dec" "kf" "lf" "B" "op" "lc" "e" "xs" "blocks"])
        K' (gf ps "K") X' (gf ps "X") Y' (gf ps "Y") dec' (gf ps "dec") kf' (gf ps "kf") lf' (gf ps "lf")
        B' (gf ps "B") op' (gf ps "op") lc' (gf ps "lc") e' (gf ps "e") xs' (gf ps "xs") blocks' (gf ps "blocks")
        PXY' (prodT X' Y') LY' (listOf Y') LP' (listOf PXY')
        joinFn (e/lam "blk" LY' (gh-joinOf K' X' Y' dec' kf' lf' xs' (e/bvar 0)) :default)
        J' (fn [ys] (gh-joinOf K' X' Y' dec' kf' lf' xs' ys))
        mapJB (mapOf LY' LP' joinFn blocks')
        flatB (J' (gh-flattenOf Y' blocks')) flatMapJB (gh-flattenOf PXY' mapJB)
        bperm (e/app* (e/const' (nm "Map.join_blockfold_perm") []) K' X' Y' dec' kf' lf' xs' blocks')
        step1 (e/app* (e/const' (nm "List.foldl_perm_lcomm") []) B' PXY' op' lc' flatB flatMapJB bperm e')
        innerL (e/lam "acc" B' (e/lam "l" LP' (gh-foldlG B' PXY' op' (e/bvar 1) (e/bvar 0)) :default) :default)
        step2 (e/app* (e/const' (nm "List.foldl_flatten") [z z]) B' PXY' op' e' mapJB)
        mid2 (gh-foldlG B' LP' innerL e' mapJB)
        step3 (e/app* (e/const' (nm "List.foldl_map") [z z z]) LY' LP' B' joinFn innerL blocks' e')
        innerStep' (e/lam "acc" B' (e/lam "blk" LY' (gh-foldlG B' PXY' op' (e/bvar 1) (J' (e/bvar 0))) :default) :default)
        rhs' (gh-foldlG B' LY' innerStep' e' blocks')
        result (tr B' (gh-foldlG B' PXY' op' e' flatB) mid2 rhs'
                   (tr B' (gh-foldlG B' PXY' op' e' flatB) (gh-foldlG B' PXY' op' e' flatMapJB) mid2 step1 step2)
                   step3)
        ps (basic/exact ps result)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; List.chunk B l : List(List α) — block-partition l into pieces of size ≤ B, built from the right.
;; The runtime carrier for grace-hash spill (codegen → partition-all). Structural recursion on l.
;;   chunk B [] = [] ; chunk B (x::xs) = case chunk B xs of
;;     [] => [[x]] | blk::rest => if length blk < B then (x::blk)::rest else [x]::blk::rest
;; flatten (chunk B l) = l  (proof = the remaining final-mile lemma; helper-lemma + case-split).
(def ^:private natT (e/const' (nm "Nat") []))
(defn chunk-def-ci
  "The verified ConstantInfo for List.chunk (Init-only). Register in build-all via admit!."
  []
  (let [chunk-type (e/forall' "a" type0 (e/forall' "B" natT
                     (e/forall' "l" (listOf (e/bvar 1)) (listOf (listOf (e/bvar 2))) :default) :default) :default)
        motive (e/lam "_" (listOf (e/bvar 2)) (listOf (listOf (e/bvar 3))) :default)
        nilC (nilOf (listOf (e/bvar 2)))
        cnd (e/app* (e/const' (nm "Nat.blt") []) (e/app* (e/const' (nm "List.length") [z]) (e/bvar 7) (e/bvar 1)) (e/bvar 6))
        tcase (consOf (listOf (e/bvar 7)) (consOf (e/bvar 7) (e/bvar 4) (e/bvar 1)) (e/bvar 0))
        ecase (consOf (listOf (e/bvar 7)) (consOf (e/bvar 7) (e/bvar 4) (nilOf (e/bvar 7)))
                      (consOf (listOf (e/bvar 7)) (e/bvar 1) (e/bvar 0)))
        conssub (e/lam "blk" (listOf (e/bvar 5))
                  (e/lam "rest" (listOf (listOf (e/bvar 6)))
                    (e/app* (e/const' (nm "cond") [L1]) (listOf (listOf (e/bvar 7))) cnd tcase ecase) :default) :default)
        nilsub (consOf (listOf (e/bvar 5)) (consOf (e/bvar 5) (e/bvar 2) (nilOf (e/bvar 5))) (nilOf (listOf (e/bvar 5))))
        coMot (e/lam "_" (listOf (listOf (e/bvar 5))) (listOf (listOf (e/bvar 6))) :default)
        ihCases (e/app* (e/const' (nm "List.casesOn") [L1 z]) (listOf (e/bvar 5)) coMot (e/bvar 0) nilsub conssub)
        consC (e/lam "x" (e/bvar 2)
                (e/lam "xs" (listOf (e/bvar 3))
                  (e/lam "ih" (listOf (listOf (e/bvar 4))) ihCases :default) :default) :default)
        body (e/app* (e/const' (nm "List.rec") [L1 z]) (e/bvar 2) motive nilC consC (e/bvar 0))
        chunk-term (e/lam "a" type0 (e/lam "B" natT (e/lam "l" (listOf (e/bvar 1)) body :default) :default) :default)]
    (kenv/mk-def (nm "List.chunk") [] chunk-type chunk-term :hints :opaque)))

;; flatten (chunk B l) = l — certifies that block-partitioning the build side preserves the data.
;; Proved via manual recursors (the cases/induction tactic mis-abstracts motives that contain
;; `flatten <scrutinee>` over nested List — same gap noted for blockfold). KEY: in every leaf the
;; proof is `congrArg (cons x) h` — def-eq absorbs the casesOn/cond/flatten reductions.
(defn- gh-chunkOf [A B l] (e/app* (e/const' (nm "List.chunk") []) A B l))
(defn- gh-eqL [A x y] (e/app* (e/const' (nm "Eq") [L1]) (listOf A) x y))
(defn- gh-cases-term [A B x c]
  (let [LA (listOf A) LLA (listOf LA)
        coMot (e/lam "_" LLA LLA :default)
        nilsub (consOf LA (consOf A x (nilOf A)) (nilOf LA))
        cnd (e/app* (e/const' (nm "Nat.blt") []) (e/app* (e/const' (nm "List.length") [z]) A (e/bvar 1)) B)
        tcase (consOf LA (consOf A x (e/bvar 1)) (e/bvar 0))
        ecase (consOf LA (consOf A x (nilOf A)) (consOf LA (e/bvar 1) (e/bvar 0)))
        conssub (e/lam "blk" LA (e/lam "rest" LLA
                  (e/app* (e/const' (nm "cond") [L1]) LLA cnd tcase ecase) :default) :default)]
    (e/app* (e/const' (nm "List.casesOn") [L1 z]) LA coMot c nilsub conssub)))
(defn- gh-congrCons [A x a1 xs h]
  (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf A) (listOf A) a1 xs
          (e/app* (e/const' (nm "List.cons") [z]) A x) h))

;; List.flatten_chunk_step : ∀ a B x xs c, flatten c = xs →
;;   flatten (casesOn c [[x]] (λblk rest. cond (blt (length blk) B) ((x::blk)::rest) ([x]::blk::rest))) = x::xs
(defn prove-flatten-chunk-step []
  (let [A (e/fvar 1) B (e/fvar 2) x (e/fvar 3) xs (e/fvar 4) c (e/fvar 5)
        hyp (gh-eqL A (gh-flattenOf A c) xs)
        concl (gh-eqL A (gh-flattenOf A (gh-cases-term A B x c)) (consOf A x xs))
        goal (-> (e/forall' "h" hyp concl :default)
                 (#(e/forall' "c" (listOf (listOf A)) (e/abstract1 % 5) :default))
                 (#(e/forall' "xs" (listOf A) (e/abstract1 % 4) :default))
                 (#(e/forall' "x" A (e/abstract1 % 3) :default))
                 (#(e/forall' "B" natT (e/abstract1 % 2) :default))
                 (#(e/forall' "a" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["a" "B" "x" "xs" "c"])
        A' (gf ps "a") B' (gf ps "B") x' (gf ps "x") xs' (gf ps "xs") c' (gf ps "c")
        LA (listOf A') LLA (listOf LA)
        motiveH (e/lam "c'" LLA
                  (e/forall' "h" (gh-eqL A' (gh-flattenOf A' (e/bvar 0)) xs')
                             (gh-eqL A' (gh-flattenOf A' (gh-cases-term A' B' x' (e/bvar 1))) (consOf A' x' xs')) :default) :default)
        nilPf (e/lam "h" (gh-eqL A' (gh-flattenOf A' (nilOf LA)) xs')
                (gh-congrCons A' x' (gh-flattenOf A' (nilOf LA)) xs' (e/bvar 0)) :default)
        T (consOf LA (consOf A' x' (e/bvar 3)) (e/bvar 2))
        E (consOf LA (consOf A' x' (nilOf A')) (consOf LA (e/bvar 3) (e/bvar 2)))
        motive2 (e/lam "b" (e/const' (nm "Bool") [])
                  (gh-eqL A' (gh-flattenOf A' (e/app* (e/const' (nm "cond") [L1]) LLA (e/bvar 0) T E)) (consOf A' x' xs')) :default)
        scrut (e/app* (e/const' (nm "Nat.blt") []) (e/app* (e/const' (nm "List.length") [z]) A' (e/bvar 2)) B')
        pf2 (gh-congrCons A' x' (gh-flattenOf A' (consOf LA (e/bvar 2) (e/bvar 1))) xs' (e/bvar 0))
        boolcases (e/app* (e/const' (nm "Bool.casesOn") [z]) motive2 scrut pf2 pf2)
        consPf (e/lam "head" LA (e/lam "tail" LLA
                 (e/lam "h" (gh-eqL A' (gh-flattenOf A' (consOf LA (e/bvar 1) (e/bvar 0))) xs') boolcases :default) :default) :default)
        recterm (e/app* (e/const' (nm "List.casesOn") [z z]) LA motiveH c' nilPf consPf)
        ps (basic/exact ps recterm)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; List.flatten_chunk : flatten (chunk B l) = l   (manual List.rec; cons case = the step lemma)
(defn prove-flatten-chunk []
  (let [A (e/fvar 1) B (e/fvar 2) l (e/fvar 3)
        goal (-> (gh-eqL A (gh-flattenOf A (gh-chunkOf A B l)) l)
                 (#(e/forall' "l" (listOf A) (e/abstract1 % 3) :default))
                 (#(e/forall' "B" natT (e/abstract1 % 2) :default))
                 (#(e/forall' "a" type0 (e/abstract1 % 1) :default)))
        motiveFC (e/lam "l'" (listOf (e/bvar 2))
                   (gh-eqL (e/bvar 3) (gh-flattenOf (e/bvar 3) (gh-chunkOf (e/bvar 3) (e/bvar 2) (e/bvar 0))) (e/bvar 0)) :default)
        baseFC (e/app* (e/const' (nm "Eq.refl") [L1]) (listOf (e/bvar 2)) (nilOf (e/bvar 2)))
        ihType (gh-eqL (e/bvar 4) (gh-flattenOf (e/bvar 4) (gh-chunkOf (e/bvar 4) (e/bvar 3) (e/bvar 0))) (e/bvar 0))
        consBody (e/app* (e/const' (nm "List.flatten_chunk_step") [])
                         (e/bvar 5) (e/bvar 4) (e/bvar 2) (e/bvar 1)
                         (gh-chunkOf (e/bvar 5) (e/bvar 4) (e/bvar 1)) (e/bvar 0))
        consFC (e/lam "x'" (e/bvar 2) (e/lam "xs'" (listOf (e/bvar 3))
                 (e/lam "ih" ihType consBody :default) :default) :default)
        recl (e/app* (e/const' (nm "List.rec") [z z]) (e/bvar 2) motiveFC baseFC consFC (e/bvar 0))
        pf (e/lam "a" type0 (e/lam "B" natT (e/lam "l" (listOf (e/bvar 1)) recl :default) :default) :default)]
    [goal pf]))

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

(defn prove-foldl-add-init []
  (let [Y (e/fvar 1) g (e/fvar 2) l (e/fvar 3) stp (gh-stepfn Y g)
        goal (-> (e/forall' "acc" (gh-natT)
                   (e/app* (e/const' (nm "Eq") [L1]) (gh-natT)
                           (gh-foldlN Y stp (e/bvar 0) l)
                           (gh-addN (e/bvar 0) (gh-foldlN Y stp (gh-zeroN) l))) :default)
                 (#(e/forall' "l" (listOf Y) (e/abstract1 % 3) :default))
                 (#(e/forall' "g" (e/forall' "_" Y (gh-natT) :default) (e/abstract1 % 2) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["Y" "g" "l"])
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
                        g (gf psg "g") head (gf psg "head") acc (gf psg "acc")
                        Y (gf psg "Y") tail (gf psg "tail")
                        gh (e/app g head) stp (gh-stepfn Y g) F (gh-foldlN Y stp (gh-zeroN) tail)
                        q (simp/simp psg ['List.foldl_cons])
                        q (basic/rewrite q (e/app ih (gh-addN acc gh)))
                        q (basic/rewrite q (e/app ih (gh-addN (gh-zeroN) gh)))
                        cgf (fn [fexpr a1 a2 h] (e/app* (e/const' (nm "congrArg") [L1 L1]) (gh-natT) (gh-natT) a1 a2 fexpr h))
                        addAssoc (e/app* (e/const' (nm "Nat.add_assoc") []) acc gh F)
                        zaS (e/app* (e/const' (nm "Eq.symm") [L1]) (gh-natT) (gh-addN (gh-zeroN) gh) gh
                                    (e/app* (e/const' (nm "Nat.zero_add") []) gh))
                        plusF   (e/lam "w" (gh-natT) (gh-addN (e/bvar 0) F) :default)
                        accPlus (e/lam "w" (gh-natT) (gh-addN acc (e/bvar 0)) :default)
                        inner (cgf plusF gh (gh-addN (gh-zeroN) gh) zaS)
                        p2    (cgf accPlus (gh-addN gh F) (gh-addN (gh-addN (gh-zeroN) gh) F) inner)
                        result (e/app* (e/const' (nm "Eq.trans") [L1]) (gh-natT)
                                       (gh-addN (gh-addN acc gh) F) (gh-addN acc (gh-addN gh F))
                                       (gh-addN acc (gh-addN (gh-addN (gh-zeroN) gh) F)) addAssoc p2)]
                    (basic/exact q result))
                  (let [psg (basic/intros psg ["acc"])]
                    (simp/simp psg ['List.foldl_nil 'Nat.add_zero])))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

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

(defn- sf-f-outer [K X Y dec g kf lf e xs ys]
  (let [P (sf-parts K X Y dec g kf lf e xs ys)
        af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        BKT (sf-getD (:LY P) (e/app* (e/const' (nm "Map.lookup") []) K (:LY P) dec (e/app kf x) (:idx P)) (nilOf Y))
        innerStep (e/lam "a" (gh-natT) (e/lam "y" Y (e/app* (:op P) (e/bvar 1) (mkP X Y x (e/bvar 0))) :default) :default)
        body (gh-foldlN' (gh-natT) Y innerStep acc BKT)]
    (e/lam "acc" (gh-natT) (e/abstract1 (e/lam "x" X (e/abstract1 body xf) :default) af) :default)))

(defn- sf-hyp [K X Y dec g kf lf e xs ys]
  (let [P (sf-parts K X Y dec g kf lf e xs ys)
        LY (:LY P) af 101 xf 102 acc (e/fvar af) x (e/fvar xf)
        kfx (e/app kf x)
        BKT (sf-getD LY (e/app* (e/const' (nm "Map.lookup") []) K LY dec kfx (:idx P)) (nilOf Y))
        bsBKT (gh-foldlN' (gh-natT) Y (:stepAdd P) (gh-zeroN) BKT)
        addInitEq (e/app* (e/const' (nm "List.foldl_add_init") []) Y g BKT acc)
        Oprime (e/app* (e/const' (nm "List.lookup") [z z]) K LY (:beq P) kfx (:entries P))
        lmkv (e/app* (e/const' (nm "List.lookup_map_kv") []) K LY (gh-natT) (:beq P) (:bucketSumFn P) kfx (:entries P))
        optMapB (fn [o] (e/app* (e/const' (nm "Option.map") [z z]) LY (gh-natT) (:bucketSumFn P) o))
        lookPre ((:llookupNat P) kfx)
        optNat (e/app (e/const' (nm "Option") [z]) (gh-natT))
        getDNfn (e/lam "o" optNat (sf-getD (gh-natT) (e/bvar 0) (gh-zeroN)) :default)
        congGetD (e/app* (e/const' (nm "congrArg") [L1 L1]) optNat (gh-natT)
                         lookPre (optMapB Oprime) getDNfn lmkv)
        getdMap (e/app* (e/const' (nm "Option.getD_map") [z z]) LY (gh-natT) (:bucketSumFn P) (nilOf Y) Oprime)
        targetRHS (sf-getD (gh-natT) lookPre (gh-zeroN))
        presumQ (e/app* (e/const' (nm "Eq.trans") [L1]) (gh-natT)
                        targetRHS (sf-getD (gh-natT) (optMapB Oprime) (gh-zeroN)) bsBKT congGetD getdMap)
        symPresum (e/app* (e/const' (nm "Eq.symm") [L1]) (gh-natT) targetRHS bsBKT presumQ)
        addAccFn (e/lam "w" (gh-natT) (gh-addN acc (e/bvar 0)) :default)
        congAdd (e/app* (e/const' (nm "congrArg") [L1 L1]) (gh-natT) (gh-natT) bsBKT targetRHS addAccFn symPresum)
        proofBody (e/app* (e/const' (nm "Eq.trans") [L1]) (gh-natT)
                          (gh-foldlN' (gh-natT) Y (:stepAdd P) acc BKT)
                          (gh-addN acc bsBKT) (gh-addN acc targetRHS) addInitEq congAdd)]
    (e/lam "acc" (gh-natT) (e/abstract1 (e/lam "x" X (e/abstract1 proofBody xf) :default) af) :default)))

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
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "X" "Y" "dec" "g" "kf" "lf" "e" "xs" "ys"])
        K (gf ps "K") X (gf ps "X") Y (gf ps "Y") dec (gf ps "dec") g (gf ps "g")
        kf (gf ps "kf") lf (gf ps "lf") e (gf ps "e") xs (gf ps "xs") ys (gf ps "ys")
        P (sf-parts K X Y dec g kf lf e xs ys)
        f-outer (sf-f-outer K X Y dec g kf lf e xs ys)
        g-outer (sf-g-outer K X Y dec g kf lf e xs ys)
        hyp (sf-hyp K X Y dec g kf lf e xs ys)
        factorEq (e/app* (e/const' (nm "Map.foldl_join_factor") []) K X Y (gh-natT) dec (:op P) e kf lf xs ys)
        congrEq (e/app* (e/const' (nm "List.foldl_congr") []) (gh-natT) X f-outer g-outer xs e hyp)
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) (gh-natT) (:lhs P)
                      (gh-foldlN' (gh-natT) X f-outer e xs) (gh-foldlN' (gh-natT) X g-outer e xs)
                      factorEq congrEq)
        ps (basic/exact ps proof)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

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
