(ns wandler.clean.laws.grace-proofs
  "Relocated verified hand-built proof builders for the grace-hash Perm cluster (was the §2/§5
   files). Pure proof functions `(env assumed) → [goal proof|nil]`, organized by dependency layer:
     §2 perm    — List.Perm helpers (flatMap_congr_perm, flatMap_map_comm, foldl_cons_perm, …)
     §5 grace   — Map.join_{filter_form,filter_append,append,nil_right,blockfold}_perm,
                  List.foldl_perm_lcomm, Map.foldl_join_blockfold (block-partition spill).
   The §3 bucket / §4 join clusters are NOT here — the clean tree (clean.laws.{bucket,relational,
   reorder}) provides Map.bucket_content / Map.join / Map.join_length_comm. `wandler.clean.laws.grace`
   admits these on the clean foundation (Stage 2). Built on Init List.Perm + the clean Map foundation."
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
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))]
    ;; THIN (#146): the hand-built per-goal reduce collapses to `induction l <;> simp_all [...]`.
    ;; Differential-tested vs the legacy proof in test/wandler/list_perm_test.clj (same goal, both
    ;; kernel-check). Goal builder kept verbatim, so the registered law type is byte-identical.
    (a/prove-law ["X" "Z" "l"] goal
      '[(induction l)
        (all_goals (simp_all [List.flatMap_cons List.flatMap_nil List.nil_append]))])))

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

