(ns wandler.list-perm-test
  "Verified List.Perm (bag-equivalence) helpers — the substrate for join reordering
   (roadmap item A). These are the generic combinators NOT in Init that the
   Map.join commutativity proof needs:

     flatMap_const_nil          flatMap (fun _ => []) l = []
     flatMap_congr_perm         (∀x, f x ~ g x) → flatMap f l ~ flatMap g l   (pointwise)
     flatMap_append_distrib_perm flatMap (fun a => f a ++ g a) l ~ flatMap f l ++ flatMap g l
     flatMap_cons_distrib_perm  flatMap (fun y => c y :: g y) ys ~ map c ys ++ flatMap g ys
     foldl_cons_perm            foldl (fun acc x => x::acc) acc l ~ acc ++ l
                                  (the bridge Map.bucket_content → bucket ~ filtered ys)
     flatMap_map_comm           flatMap (fun x => map (f x ·) ys) xs
                                  ~ flatMap (fun y => map (f · y) xs) ys  (product transpose / Fubini)

   All checks here use the AUTHORITATIVE check-constant (full kernel), not the lenient
   TypeChecker.inferType. (flatMap_map_comm inducts on a variable that occurs UNDER a
   binder; that path tripped a simp `:lam` funext bug — building a malformed funext that
   only check-constant caught — now fixed in simp.clj.) Why a Perm and not Eq: List.perm_iff_count is absent (only the forward
   Perm.count_eq), so the count characterization can't CONCLUDE Perm — these go by
   list surgery (induction + Perm.append/perm_append_comm_assoc). flatMap_map_comm
   is the combinatorial core (nested-loop transpose). Init-only; each kernel-checked."
  (:require [ansatz.core :as a]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]
            [ansatz.kernel.tc :as tc]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
;; AUTHORITATIVE check: full kernel check-constant (the path used for mathlib verification).
;; The Java TypeChecker.inferType alone is a lenient *inference* — it assumes well-typed
;; input and would silently accept a de-Bruijn-capture bug, as would the tactic engine's
;; internal isDefEq. check-constant re-checks everything.
(defn- checks? [p g]
  (try (kenv/check-constant (a/env) (kenv/mk-thm (nm "__chk__") [] g p)) true
       (catch Throwable _ false)))
(defn- reg! [n g p] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) [] g p))))

;; term builders
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- flatMap [aX aY f l] (e/app* (e/const' (nm "List.flatMap") [z z]) aX aY f l))
(defn- mapOf [aX aY f l] (e/app* (e/const' (nm "List.map") [z z]) aX aY f l))
(defn- appendOf [a l r] (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) (listOf a) (listOf a) (listOf a)
                                (e/app* (e/const' (nm "instHAppendOfAppend") [z]) (listOf a) (e/app (e/const' (nm "List.instAppend") [z]) a)) l r))
(defn- permOf [a l r] (e/app* (e/const' (nm "List.Perm") [z]) a l r))
(defn- singletonOf [a x] (e/app* (e/const' (nm "List.cons") [z]) a x (nilOf a)))
;; Perm combinators (arg orders pinned empirically)
(defn- p-refl [a l] (e/app* (e/const' (nm "List.Perm.refl") [z]) a l))
(defn- p-symm [a x y h] (e/app* (e/const' (nm "List.Perm.symm") [z]) a x y h))
(defn- p-trans [a x y w h1 h2] (e/app* (e/const' (nm "List.Perm.trans") [z]) a x y w h1 h2))
(defn- p-append [a l1 l2 r1 r2 h1 h2] (e/app* (e/const' (nm "List.Perm.append") [z]) a l1 l2 r1 r2 h1 h2))
(defn- p-aleft [a x y l h] (e/app* (e/const' (nm "List.Perm.append_left") [z]) a x y l h))
(defn- p-caa [a x y w] (e/app* (e/const' (nm "List.perm_append_comm_assoc") [z]) a x y w))
(defn- p-cons [a x l1 l2 h] (e/app* (e/const' (nm "List.Perm.cons") [z]) a x l1 l2 h))
(defn- consOf [a x l] (e/app* (e/const' (nm "List.cons") [z]) a x l))
(defn- foldlOf [a init l flip] (e/app* (e/const' (nm "List.foldl") [z z]) (listOf a) a flip init l))

;; ---------- flatMap_const_nil ----------
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

;; THIN migration (#146): identical goal builder; the ~18-line hand-built proof (start-proof + the
;; per-goal reduce with manual fvar/IH juggling) collapses to a 2-line tactic block via a/prove-law.
(defn prove-flatMap-const-nil-thin []
  (let [fX (e/fvar 1) fZ (e/fvar 2) fl (e/fvar 3)
        fn0 (e/lam "_" fX (nilOf fZ) :default)
        body (e/app* (e/const' (nm "Eq") [L1]) (listOf fZ) (flatMap fX fZ fn0 fl) (nilOf fZ))
        goal (-> body
                 (#(e/forall' "l" (listOf fX) (e/abstract1 % 3) :default))
                 (#(e/forall' "Z" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))]
    (a/prove-law ["X" "Z" "l"] goal
      '[(induction l)
        (all_goals (simp_all [List.flatMap_cons List.flatMap_nil List.nil_append]))])))

;; ---------- flatMap_congr_perm ----------
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

;; THIN migration (#146/#157): the hand-built cons case (simp + manual `p-append (h hd) ih`) and nil
;; case (`p-refl`) collapse to a tactic block. The cons goal `f hd ++ flatMap f tl ~ g hd ++ flatMap g tl`
;; is closed by `apply List.Perm.append` then the quantified hyp `h` (→ `h hd`) and the IH (assumption);
;; nil by `List.Perm.refl`. Exercises the univ-poly apply path (apply solves the Perm ctors' universe
;; mvars via meta-isDefEq) AND local-hyp-as-solve_by_elim-lemma (h shadows globals).
(defn prove-flatMap-congr-perm-thin []
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
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))]
    (a/prove-law ["X" "Y" "f" "g" "h" "l"] goal
      '[(induction l)
        (all_goals (simp [List.flatMap_cons List.flatMap_nil]))
        (all_goals (solve_by_elim [List.Perm.append List.Perm.refl List.Perm.nil h]))])))

;; ---------- flatMap_append_distrib_perm ----------
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

;; ---------- flatMap_cons_distrib_perm (H4') : the cons-split distribution ----------
;;   flatMap (fun y => c y :: g y) ys  ~  map c ys ++ flatMap g ys
;; Lets flatMap_map_comm's cons branch avoid a map_eq_flatMap rewrite (whose generated
;; funext was ill-typed — accepted by the lenient inferer but rejected by check-constant).
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

;; ---------- flatMap_map_comm (product transpose / Fubini) ----------
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
                        gfn (e/lam "y" Y (e/app* f a (e/bvar 0)) :default)        ; c = λy. f a y
                        A (mapOf Y Z gfn ys)
                        innerL' (e/lam "x" X (mapOf Y Z (e/lam "y" Y (e/app* f (e/bvar 1) (e/bvar 0)) :default) ys) :default)
                        LT (flatMap X Z innerL' xs')
                        gpY (e/lam "y" Y (mapOf X Z (e/lam "x" X (e/app* f (e/bvar 0) (e/bvar 1)) :default) xs') :default) ; g
                        RT (flatMap Y Z gpY ys)
                        RHS' (flatMap Y Z (e/lam "y" Y (mapOf X Z (e/lam "x" X (e/app* f (e/bvar 0) (e/bvar 1)) :default)
                                                            (e/app* (e/const' (nm "List.cons") [z]) X a xs')) :default) ys)
                        q (simp/simp psg ['List.flatMap_cons 'List.map_cons])
                        ;; H4' : RHS' ~ A ++ RT  (no rewrite — avoids the funext bug)
                        h4p (e/app* (e/const' (nm "List.flatMap_cons_distrib_perm") []) Y Z gfn gpY ys)]
                    (basic/exact q (p-trans Z (appendOf Z A LT) (appendOf Z A RT) RHS'
                                            (p-aleft Z LT RT A (e/fvar ihid))
                                            (p-symm Z RHS' (appendOf Z A RT) h4p))))
                  ;; xs = nil : sub-induct on ys, both sub-cases close by def-eq
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

;; ---------- foldl_cons_perm : foldl (fun acc x => x::acc) acc l ~ acc ++ l ----------
;; The bridge from Map.bucket_content (bucket = foldl-cons over the filtered list) to
;; bucket_perm (bucket ~ filtered list): the foldl-cons accumulator is a permutation
;; of its append. Generalizes the accumulator (acc innermost ∀) so induction goes through.
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

(defn register-list-perm-helpers!
  "Prove + register the four Perm helpers into the live env (idempotent enough for
   tests). Order matters: flatMap_map_comm uses const_nil + append_distrib."
  []
  (let [[g p] (prove-flatMap-const-nil)] (reg! "List.flatMap_const_nil" g p))
  (let [[g p] (prove-flatMap-congr-perm)] (reg! "List.flatMap_congr_perm" g p))
  (let [[g p] (prove-flatMap-append-distrib)] (reg! "List.flatMap_append_distrib_perm" g p))
  (let [[g p] (prove-flatMap-cons-distrib)] (reg! "List.flatMap_cons_distrib_perm" g p))
  (let [[g p] (prove-flatMap-map-comm)] (reg! "List.flatMap_map_comm" g p))
  (let [[g p] (prove-foldflip-perm)] (reg! "List.foldl_cons_perm" g p)))

(deftest list-perm-helpers
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [[g p] (prove-flatMap-const-nil)]
        (is (some? p) "flatMap_const_nil proved")
        (is (true? (checks? p g)) "flatMap_const_nil kernel-checks")
        (reg! "List.flatMap_const_nil" g p))
      (let [[g p] (prove-flatMap-congr-perm)]
        (is (some? p) "flatMap_congr_perm proved")
        (is (true? (checks? p g)) "flatMap_congr_perm kernel-checks")
        (reg! "List.flatMap_congr_perm" g p))
      (let [[g p] (prove-flatMap-append-distrib)]
        (is (some? p) "flatMap_append_distrib_perm proved")
        (is (true? (checks? p g)) "flatMap_append_distrib_perm kernel-checks")
        (reg! "List.flatMap_append_distrib_perm" g p))
      (let [[g p] (prove-flatMap-cons-distrib)]
        (is (some? p) "flatMap_cons_distrib_perm proved")
        (is (true? (checks? p g)) "flatMap_cons_distrib_perm kernel-checks")
        (reg! "List.flatMap_cons_distrib_perm" g p))
      (let [[g p] (prove-flatMap-map-comm)]
        (is (some? p) "flatMap_map_comm (product transpose / Fubini) proved")
        (is (true? (checks? p g)) "flatMap_map_comm kernel-checks (check-constant)")
        (reg! "List.flatMap_map_comm" g p))
      (let [[g p] (prove-foldflip-perm)]
        (is (some? p) "foldl_cons_perm proved")
        (is (true? (checks? p g)) "foldl_cons_perm kernel-checks")))
    (is true "SKIP list-perm-helpers: no Init env")))

;; #146 strangler pilot: the THIN proof must kernel-check the SAME goal the legacy hand-built proof
;; targets (differential). Old stays as the reference until the whole cluster is migrated.
(deftest flatmap-const-nil-thin-differential
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [[g-old _]      (prove-flatMap-const-nil)
            [g-new p-new]  (prove-flatMap-const-nil-thin)]
        (is (some? p-new) "thin proof produced")
        (is (true? (checks? p-new g-new)) "thin proof kernel-checks its own goal")
        (is (= (str g-old) (str g-new)) "thin goal is byte-identical to the legacy goal")
        (is (true? (checks? p-new g-old)) "thin proof ALSO proves the legacy goal (differential)")))
    (is true "SKIP: no Init env")))

;; #157 strangler: flatMap_congr_perm — the first PERM-constructor proof thinned. The thin script
;; `induction l; simp; solve_by_elim [Perm.append Perm.refl Perm.nil h]` replaces the hand-built
;; `p-append (h hd) ih` / `p-refl` term, and kernel-checks the SAME goal (differential).
(deftest flatmap-congr-perm-thin-differential
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [[g-old _]      (prove-flatMap-congr-perm)
            [g-new p-new]  (prove-flatMap-congr-perm-thin)]
        (is (some? p-new) "thin proof produced")
        (is (true? (checks? p-new g-new)) "thin proof kernel-checks its own goal")
        (is (= (str g-old) (str g-new)) "thin goal is byte-identical to the legacy goal")
        (is (true? (checks? p-new g-old)) "thin proof ALSO proves the legacy goal (differential)")))
    (is true "SKIP: no Init env")))
