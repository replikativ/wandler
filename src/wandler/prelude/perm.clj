(ns wandler.prelude.perm
  "Verified `List.Perm` (bag-equivalence) prelude — wandler's Batteries-tier owned library, mirroring
   Lean 4's `Init/Data/List/Perm.lean`. This is the substrate for join reordering / aggregation
   commutativity (the `Map.join_comm` capstone): a join materialized as a List of pairs is commutative
   only UP TO permutation, so the relational laws reason in `List.Perm`.

   ─ Tier 0 (FREE from Init — referenced by their exact Lean names, NOT re-proved) ──────────────────
   The whole `List.Perm` combinator family ships in Init (`Init/Data/List/Perm.lean`, public-imported
   by `Init/Data/List.lean`) and is present in the full Init store (`test-data/init.ndjson`):
     List.Perm                      (inductive; ctors nil/cons/swap/trans — Init/Data/List/Basic.lean)
     List.Perm.refl / .symm         (Perm.lean)
     List.Perm.trans / .cons        (Basic.lean ctors)
     List.Perm.append              l₁~l₂ → r₁~r₂ → (l₁++r₁) ~ (l₂++r₂)     (Perm.lean)
     List.Perm.append_left / _right                                          (Perm.lean)
     List.perm_append_comm          (l₁++l₂) ~ (l₂++l₁)                       (Perm.lean)
     List.perm_append_comm_assoc    (l₁++(l₂++l₃)) ~ (l₂++(l₁++l₃))           (Perm.lean)
     List.Perm.map / .filter / .filterMap / .flatMap_right                   (Perm.lean)
   The `p-*` builders below are thin aliases over these — exactly the terms Lean's tactics emit.

   ─ Tier 1 (COINED — proved here; absent from Init/Batteries) ──────────────────────────────────────
   Six combinators the `Map.join` proof needs that Lean/Batteries does not ship. Each is kernel-checked
   (authoritative `check-constant`, not the lenient inferer). The flagship is `flatMap_congr_perm`:
   Lean only has the *list-side* `List.Perm.flatMap_right` (permute the list); the *function-pointwise*
   congruence `(∀x, f x ~ g x) → flatMap f l ~ flatMap g l` has NO Lean counterpart.

     List.flatMap_const_nil          flatMap (fun _ => []) l = []
     List.flatMap_congr_perm         (∀x, f x ~ g x) → flatMap f l ~ flatMap g l        [flagship]
     List.flatMap_append_distrib_perm  flatMap (fun a => f a ++ g a) l ~ flatMap f l ++ flatMap g l
     List.flatMap_cons_distrib_perm  flatMap (fun y => c y :: g y) ys ~ map c ys ++ flatMap g ys
     List.flatMap_map_comm           nested-loop transpose / Fubini (product commutes up to perm)
     List.foldl_cons_perm            foldl (fun acc x => x::acc) acc l ~ acc ++ l

   Proof style mirrors Lean: `flatMap_const_nil` and the flagship `flatMap_congr_perm` are THIN
   (a/prove-law: `induction l; simp; solve_by_elim[...]`); the append/cons distribution + Fubini +
   foldl-cons bridges still build the term explicitly (their cons cases chain `Perm.trans` through a
   middle term that the surface `solve_by_elim` search does not yet pin — they read like Lean's manual
   `(p.append_left).trans (perm_append_comm_assoc …)`).

   `install!` proves + registers all six into the live env. Idempotent enough for repeated calls."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))

;; ── term builders ────────────────────────────────────────────────────────────
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- flatMap [aX aY f l] (e/app* (e/const' (nm "List.flatMap") [z z]) aX aY f l))
(defn- mapOf [aX aY f l] (e/app* (e/const' (nm "List.map") [z z]) aX aY f l))
(defn- appendOf [a l r] (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) (listOf a) (listOf a) (listOf a)
                                (e/app* (e/const' (nm "instHAppendOfAppend") [z]) (listOf a) (e/app (e/const' (nm "List.instAppend") [z]) a)) l r))
(defn- permOf [a l r] (e/app* (e/const' (nm "List.Perm") [z]) a l r))
(defn- singletonOf [a x] (e/app* (e/const' (nm "List.cons") [z]) a x (nilOf a)))
(defn- consOf [a x l] (e/app* (e/const' (nm "List.cons") [z]) a x l))
(defn- foldlOf [a init l flip] (e/app* (e/const' (nm "List.foldl") [z z]) (listOf a) a flip init l))

;; ── Tier 0: thin aliases over Init's `List.Perm` combinators (Lean's emitted terms) ──────────────
(defn p-refl [a l] (e/app* (e/const' (nm "List.Perm.refl") [z]) a l))
(defn p-symm [a x y h] (e/app* (e/const' (nm "List.Perm.symm") [z]) a x y h))
(defn p-trans [a x y w h1 h2] (e/app* (e/const' (nm "List.Perm.trans") [z]) a x y w h1 h2))
(defn p-append [a l1 l2 r1 r2 h1 h2] (e/app* (e/const' (nm "List.Perm.append") [z]) a l1 l2 r1 r2 h1 h2))
(defn p-aleft [a x y l h] (e/app* (e/const' (nm "List.Perm.append_left") [z]) a x y l h))
(defn p-caa [a x y w] (e/app* (e/const' (nm "List.perm_append_comm_assoc") [z]) a x y w))
(defn p-cons [a x l1 l2 h] (e/app* (e/const' (nm "List.Perm.cons") [z]) a x l1 l2 h))

;; ── Tier 1, #1: flatMap_const_nil — THIN ──────────────────────────────────────
(defn prove-flatMap-const-nil
  "flatMap (fun _ => []) l = []. Thin: `induction l; simp_all [flatMap_cons/_nil/nil_append]`."
  []
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

;; ── Tier 1, #2: flatMap_congr_perm — THIN, flagship (no Lean counterpart) ─────
(defn prove-flatMap-congr-perm
  "(∀ x, f x ~ g x) → flatMap f l ~ flatMap g l. Pointwise congruence — Lean only ships the list-side
   `List.Perm.flatMap_right`. Thin: cons = `Perm.append (h hd) ih`, nil = `Perm.refl`."
  []
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

;; ── Tier 1, #3: flatMap_append_distrib_perm — hand-built (trans-chain) ────────
(defn prove-flatMap-append-distrib
  "flatMap (fun a => f a ++ g a) l ~ flatMap f l ++ flatMap g l. cons case mirrors Lean's manual
   `(ih.append_left).trans (perm_append_comm_assoc …)` chain."
  []
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

;; ── Tier 1, #4: flatMap_cons_distrib_perm — hand-built (trans-chain) ──────────
(defn prove-flatMap-cons-distrib
  "flatMap (fun y => c y :: g y) ys ~ map c ys ++ flatMap g ys. Lets flatMap_map_comm's cons branch
   avoid a map_eq_flatMap rewrite (whose funext the lenient inferer accepts but check-constant rejects)."
  []
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

;; ── Tier 1, #5: flatMap_map_comm — hand-built (Fubini / product transpose) ────
(defn prove-flatMap-map-comm
  "flatMap (fun x => map (f x ·) ys) xs ~ flatMap (fun y => map (f · y) xs) ys. The nested-loop
   transpose; cons step uses flatMap_cons_distrib_perm to dodge the funext bug."
  []
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

;; ── Tier 1, #6: foldl_cons_perm — hand-built (accumulator-generalized) ────────
(defn prove-foldflip-perm
  "foldl (fun acc x => x::acc) acc l ~ acc ++ l. The bridge from Map.bucket_content to bucket_perm;
   generalizes the accumulator (acc innermost ∀) so induction goes through."
  []
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

(defn- reg! [n g p] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) [] g p))))

(defn install!
  "Prove + register all six Tier-1 `List.Perm` combinators into the live env, in dependency order
   (flatMap_map_comm uses flatMap_cons_distrib_perm). Idempotent enough for tests. Tier-0 names are
   resolved from Init directly and need no installation."
  []
  (let [[g p] (prove-flatMap-const-nil)]       (reg! "List.flatMap_const_nil" g p))
  (let [[g p] (prove-flatMap-congr-perm)]       (reg! "List.flatMap_congr_perm" g p))
  (let [[g p] (prove-flatMap-append-distrib)]   (reg! "List.flatMap_append_distrib_perm" g p))
  (let [[g p] (prove-flatMap-cons-distrib)]     (reg! "List.flatMap_cons_distrib_perm" g p))
  (let [[g p] (prove-flatMap-map-comm)]         (reg! "List.flatMap_map_comm" g p))
  (let [[g p] (prove-foldflip-perm)]            (reg! "List.foldl_cons_perm" g p)))
