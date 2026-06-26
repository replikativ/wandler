(ns wandler.join-comm-test
  "Verified Map.join COMMUTATIVITY (roadmap item A) — a List.Perm law, the one
   non-Eq proof shape. Map.join kf lf xs ys = xs.flatMap(λx. (getD(lookup(kf x)
   (group_by lf ys))[]).map(λy.(x,y))) is a hash-join; swapping which side is indexed
   vs probed gives a BAG-equal (permuted) result:

     join kf lf xs ys  ~  map Prod.swap (join lf kf ys xs)

   Built on the List.Perm substrate (list_perm_test) + the group_by bucket foundation.
   This file currently lands the join-specific bricks BEq.beq_comm and Map.bucket_perm;
   the final assembly (filter-product pushout + flatMap_map_comm transpose) lands next.
   Gated on Init."
  (:require [ansatz.core :as a]
            [wandler.kmap :as kmap]
            [wandler.kmap-lookup-test :as klt]
            [wandler.kmap-group-by-test :as gbt]
            [wandler.bucket-content-test :as bct]
            [wandler.list-perm-test :as lpt]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]
            [wandler.optimize :as opt]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- new-goals [before after] (vec (remove (set before) after)))
;; AUTHORITATIVE check: full kernel check-constant. The Java TypeChecker.inferType (and
;; the tactic engine's internal isDefEq) is a lenient inference that assumes well-typed
;; input and would silently accept a de-Bruijn-capture bug or a malformed funext.
(defn- checks? [p g]
  (try (kenv/check-constant (a/env) (kenv/mk-thm (nm "__chk__") [] g p)) true
       (catch Throwable _ false)))
(defn- reg! [n g p] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) [] g p))))

(defn setup! []
  (kmap/install!)
  (lpt/register-list-perm-helpers!)
  (binding [a/*verbose* false]
    (let [[g p] (#'klt/prove-lookup-filter-ne)] (reg! "List.lookup_filter_ne" g p))
    (let [[g p] (#'klt/prove-lookup-insert)] (reg! "List.lookup_insert" g p))
    (let [[g p] (#'gbt/prove-map-lookup-insert)] (reg! "Map.lookup_insert" g p))
    (let [[g p] (#'bct/prove-bucket-gen)] (reg! "Map.bucket_content_gen" g p))
    (let [[g p] (#'bct/prove-bucket-final)]
      (reset! a/ansatz-env (kenv/check-constant (a/env) (kenv/mk-thm (nm "Map.bucket_content") [] g p))))))

;; ---------- BEq.beq_comm : (a == b) = (b == a) for instBEqOfDecidableEq ----------
(def ^:private boolT (e/const' (nm "Bool") []))
(def ^:private btrue (e/const' (nm "Bool.true") []))
(def ^:private bfalse (e/const' (nm "Bool.false") []))
(defn- eqB [x y] (e/app* (e/const' (nm "Eq") [L1]) boolT x y))
(defn- eqK [K x y] (e/app* (e/const' (nm "Eq") [L1]) K x y))
(defn- tr [ty x y w h1 h2] (e/app* (e/const' (nm "Eq.trans") [L1]) ty x y w h1 h2))
(defn- sy [ty x y h] (e/app* (e/const' (nm "Eq.symm") [L1]) ty x y h))
(defn- imp [P Q h ha] (e/app* (e/const' (nm "Iff.mp") []) P Q h ha))
(defn- impr [P Q h hb] (e/app* (e/const' (nm "Iff.mpr") []) P Q h hb))

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

;; ---------- Map.bucket_perm : bucket ~ filter (fun x => k == f x) ys ----------
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

;; ---------- Claim A : join_inline ~ filtered product (MP) ----------
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- mapOf [aX aY f l] (e/app* (e/const' (nm "List.map") [z z]) aX aY f l))
(defn- flatMapOf [aX aY f l] (e/app* (e/const' (nm "List.flatMap") [z z]) aX aY f l))
(defn- filterOf [a p l] (e/app* (e/const' (nm "List.filter") [z]) a p l))
(defn- beqK [K dec x y] (e/app* (e/const' (nm "BEq.beq") [z]) K (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) K dec) x y))

(defn prove-claim-a []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys (e/fvar 8)
        PXY (prodT X Y) listY (listOf Y)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        bucket (fn [k'] (e/app* (e/const' (nm "Option.getD") [z]) listY
                                (e/app* (e/const' (nm "Map.lookup") []) K listY dec k'
                                        (e/app* (e/const' (nm "Map.group_by") []) K Y dec lf ys))
                                (nilOf Y)))
        ;; under a single λx binder: x = bvar1, y = bvar0  (explicit indices — no capture)
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

;; ---------- the capstone: Map.join_comm via the filtered-product transpose ----------
(defn- fstOf [X Y p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
(defn- sndOf [X Y p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
(defn- mkP [X Y x y] (e/app* (e/const' (nm "Prod.mk") [z z]) X Y x y))
(defn- reg-anon! [n g p] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) [] g p))))
(defn- eq-via-simp [goal lems names]
  (let [[ps _] (proof/start-proof (a/env) goal) ps (basic/intros ps names)
        ps (try (simp/simp ps lems) (catch Throwable _ ps))]
    (when (proof/solved? ps) (extract/extract ps))))

;; Proves + registers pushout_a/b, qeq, Map.join_MPa_MPb (Claim C), msEq2,
;; Map.join_mapswap, and returns the const-form Map.join_comm [goal proof].
;; Requires: helpers (incl. flatMap_map_comm), bucket foundation, beq_comm, bucket_perm,
;; Map.join_filtered_product (Claim A) already registered (see the deftest order).
(defn prove-join-comm []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys (e/fvar 8)
        PXY (prodT X Y) YX (prodT Y X) listX (listOf X) listY (listOf Y) listP (listOf PXY)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        names ["K" "X" "Y" "dec" "kf" "lf" "xs" "ys"]
        mkF (e/lam "y" Y (mkP X Y (e/bvar 1) (e/bvar 0)) :default)        ; under λx: (x,y)
        mkG (e/lam "x" X (mkP X Y (e/bvar 0) (e/bvar 1)) :default)        ; under λy: (x,y)
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
        ;; (1) filter-product pushouts
        pa (eq-via-simp (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPa (filterOf PXY Q1 Prodxy))) lems names)
        pb (eq-via-simp (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPb' (filterOf PXY Q2 Prodyx))) lems names)
        _ (reg-anon! "Map.pushout_a" (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPa (filterOf PXY Q1 Prodxy))) pa)
        _ (reg-anon! "Map.pushout_b" (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPb' (filterOf PXY Q2 Prodyx))) pb)
        ;; (2) qeq : Q1 = Q2 via funext of beq_comm
        qeq-goal (wrapF (e/app* (e/const' (nm "Eq") [(lvl/imax L1 L1)]) (e/forall' "_" PXY boolT :default) Q1 Q2))
        qeq-pf (wrapL (e/app* (e/const' (nm "funext") [L1 L1]) PXY (e/lam "_" PXY boolT :default) Q1 Q2
                             (e/lam "p" PXY (e/app* (e/const' (nm "BEq.beq_comm") []) K dec
                                                    (e/app kf (fstOf X Y (e/bvar 0))) (e/app lf (sndOf X Y (e/bvar 0)))) :default)))
        _ (reg-anon! "Map.qeq" qeq-goal qeq-pf)
        ;; (3) Claim C : MPa ~ MPb'  (pushout ×2 + Q1=Q2 + flatMap_map_comm transpose)
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
        ;; (4) msEq2 : MPb' = map swap MPb  (MPb = Claim A's RHS at lf kf ys xs, pairs (y,x))
        swapYX (e/lam "p" YX (e/app* (e/const' (nm "Prod.swap") [z z]) Y X (e/bvar 0)) :default)
        MPb (flatMapOf Y YX (e/lam "y" Y (mapOf X YX (e/lam "x" X (mkP Y X (e/bvar 1) (e/bvar 0)) :default) (filterOf X matchG xs)) :default) ys)
        ms2-goal (wrapF (e/app* (e/const' (nm "Eq") [L1]) listP MPb' (mapOf YX PXY swapYX MPb)))
        ms2 (eq-via-simp ms2-goal ['List.map_flatMap 'List.map_map 'Function.comp 'Prod.swap] names)
        _ (reg-anon! "Map.msEq2" ms2-goal ms2)
        ;; (5) mapswap-piece : map swap (join_inline lf kf ys xs) ~ MPb'
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
        ;; (6) Map.join_comm = trans (ClaimA) (trans (ClaimC) (symm mapswap))  on the OPAQUE const
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

;; ---------- the Perm→Eq BRIDGE: cardinality is join-order-invariant ----------
;; length (join kf lf xs ys) = length (join lf kf ys xs).
;; Map.join_comm is a List.Perm (bag) law — the one non-Eq shape. Here it yields a genuine
;; Eq at the order-invariant `length` boundary: a join reorder (which side is indexed vs
;; probed — the actual cost decision) is now soundly Eq-CERTIFIABLE for count/cardinality
;; queries, so the existing Eq-based optimizer gate can adopt it. Built generically from the
;; registered Map.join_comm const:  Eq.trans (Perm.length_eq join_comm) (length_map …).
(defn- prove-join-length-comm []
  (let [jc (kenv/lookup (a/env) (nm "Map.join_comm"))
        jct (.type jc)
        [params body] (loop [t jct ps []]
                        (if (e/forall? t)
                          (recur (e/forall-body t) (conj ps [(e/forall-name t) (e/forall-type t) (e/forall-info t)]))
                          [ps t]))
        nP (count params)
        [_ pa] (e/get-app-fn-args body)              ; @List.Perm elemTy LHS RHS
        elemTy (nth pa 0) lhs (nth pa 1) rhs (nth pa 2)
        [_ ma] (e/get-app-fn-args rhs)               ; @List.map srcTy dstTy swap join'
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

(deftest join-comm-bricks
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (setup!)
      (let [[g p] (prove-beq-comm)]
        (is (some? p) "beq_comm proved")
        (is (true? (checks? p g)) "BEq.beq_comm kernel-checks")
        (reg! "BEq.beq_comm" g p))
      (let [[g p] (prove-bucket-perm)]
        (is (some? p) "bucket_perm proved")
        (is (true? (checks? p g)) "Map.bucket_perm kernel-checks (bucket ~ filtered ys)")
        (reg! "Map.bucket_perm" g p))
      (let [[g p] (prove-claim-a)]
        (is (some? p) "claim A proved")
        (is (true? (checks? p g)) "Map.join_filtered_product kernel-checks (join ~ filtered product)")
        (reg! "Map.join_filtered_product" g p))
      ;; THE CAPSTONE: Map.join kf lf xs ys ~ map Prod.swap (Map.join lf kf ys xs)
      (let [[g p] (prove-join-comm)]
        (is (some? p) "join_comm proved")
        (is (true? (checks? p g))  ; check-constant against the OPAQUE Map.join const
            "Map.join_comm kernel-checks (commutativity — a List.Perm bag-equivalence)")
        (when p (reg! "Map.join_comm" g p)))
      ;; THE Perm→Eq BRIDGE: cardinality is join-order-invariant, so a reorder is
      ;; Eq-certifiable for count queries (length (join …) = length (join-reordered …)).
      (let [[g p] (prove-join-length-comm)]
        (is (some? p) "join_length_comm built")
        (is (true? (checks? p g))
            "Map.join_length_comm kernel-checks (length is join-order-invariant — Perm→Eq)")
        (when p (reg! "Map.join_length_comm" g p)))
      ;; THE PAYOFF: a cost-driven, kernel-CERTIFIED join reorder for a count query.
      ;; `length (join … (filter p xs) ys)` indexes the big ys; the optimizer reorders to
      ;; index the small filtered side, certified by the Map.join_length_comm bridge — but
      ;; ONLY when it lowers pipeline-cost (no spurious permutation when both sides are full).
      (let [d (fn [s] (e/const' (nm s) []))
            natT (d "Nat") n2n (e/forall' "_" natT natT :default)
            n2b (e/forall' "_" natT (d "Bool") :default)
            decT (e/app* (e/const' (nm "DecidableEq") [L1]) natT)
            listNat (e/app* (e/const' (nm "List") [z]) natT)
            prodNN (e/app* (e/const' (nm "Prod") [z z]) natT natT)
            [dec kf lf xs0 ys0 pr] (map e/fvar [5000 5001 5002 5003 5004 5005])
            lctx {5000 {:name "dec" :type decT} 5001 {:name "kf" :type n2n}
                  5002 {:name "lf" :type n2n} 5003 {:name "xs" :type listNat}
                  5004 {:name "ys" :type listNat} 5005 {:name "p" :type n2b}}
            filt (e/app* (e/const' (nm "List.filter") [z]) natT pr xs0)
            len  (fn [j] (e/app* (e/const' (nm "List.length") [z]) prodNN j))
            join (fn [a b] (e/app* (d "Map.join") natT natT natT dec kf lf a b))
            term  (len (join filt ys0))     ; index big ys, drive small filtered xs
            term2 (len (join xs0 ys0))      ; both sides full → no reorder win
            res  (opt/try-join-reorder (a/env) term :lctx lctx)
            res2 (opt/try-join-reorder (a/env) term2 :lctx lctx)]
        (is (some? res) "join reorder applies to a filtered count-join")
        (is (true? (:verified? res)) "the reorder is kernel-certified by Map.join_length_comm")
        (is (< (opt/pipeline-cost (:term res)) (opt/pipeline-cost term))
            "the reorder lowers pipeline-cost (indexes the smaller side)")
        (is (nil? res2) "no reorder when both sides are full (no cost win — no spurious permutation)")
        ;; AUTO-WIRED: optimize-cost itself adopts the reorder (+ composes with fusion),
        ;; certifying the composed proof against the ORIGINAL term.
        (let [oc (opt/optimize-cost (a/env) term :lctx lctx)]
          (is (true? (:verified? oc)) "optimize-cost composed proof certifies vs original term")
          (is (contains? (set (:rewrites oc)) :join-reorder) "optimize-cost adopts :join-reorder")
          (is (< (opt/pipeline-cost (:term oc)) (opt/pipeline-cost term))
              "optimize-cost lowers pipeline-cost via the reorder"))
        (let [oc2 (opt/optimize-cost (a/env) term2 :lctx lctx)]
          (is (not (contains? (set (:rewrites oc2)) :join-reorder))
              "optimize-cost does NOT reorder when both sides are full"))))
    (is true "SKIP join-comm-bricks: no Init env")))
