(ns wandler.dbsp
  "Verified INCREMENTAL view maintenance (DBSP / differential dataflow), insert-only fragment — rung 4
   of the List → Stream → Incremental → Distributed ladder. A delta is an appended batch `dD` (bag
   union); incrementalizing a query Q means proving `Q(D ⊎ dD) = Q(D) ⊕ Q(dD)` so the running result
   is maintained by applying Q to the DELTA only, never recomputing over all of D. The whole theory,
   for the linear + aggregate fragment, IS the append-distribution / monoid-homomorphism laws:

     LINEAR    (map, filter): `count (filter p (D ++ dD)) = count (filter p D) + count (filter p dD)`
                               — `List.filter_count_incr`, from filter_append + length_append.
     BILINEAR  (join):        `count (join xs (ys ++ dys)) = count (join xs ys) + count (join xs dys)`
                               — `Map.join_count_incr`, from `Map.join_append_perm` (join linear in
                               the build side, up to Perm) + Perm.length_eq + length_append.

   The bilinear law is the DIFFERENTIAL JOIN — exactly semi-naive datalog's per-iteration increment
   (join the NEW build tuples `dys` against the fixed probe `xs`, accumulate). Insert-only (append)
   covers semi-naive (each fixpoint step only adds tuples); DELETIONS need a Z-set carrier (element →
   ℤ weight) so the bag becomes an abelian group — the next increment. See ../datahike (semi-naive),
   spindel's DeltaAlgebra (the delta runtime), and [[verified-monoid-parallel-fold]]."
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
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- fstOf [X Y p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
(defn- sndOf [X Y p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
(defn- natT [] (e/const' (nm "Nat") []))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- appendL [A l r] (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) (listOf A) (listOf A) (listOf A)
                               (e/app* (e/const' (nm "instHAppendOfAppend") [z]) (listOf A) (e/app (e/const' (nm "List.instAppend") [z]) A)) l r))
(defn- lengthL [A l] (e/app* (e/const' (nm "List.length") [z]) A l))
(defn- filterL [A p l] (e/app* (e/const' (nm "List.filter") [z]) A p l))
(defn- joinL [K X Y dec kf lf xs ys] (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys))
(defn- hadd [a b] (e/app* (e/const' (nm "HAdd.hAdd") [z z z]) (natT) (natT) (natT)
                          (e/app* (e/const' (nm "instHAdd") [z]) (natT) (e/const' (nm "instAddNat") [])) a b))
(defn- eqN [x y] (e/app* (e/const' (nm "Eq") [L1]) (natT) x y))
(defn- trN [x y w h1 h2] (e/app* (e/const' (nm "Eq.trans") [L1]) (natT) x y w h1 h2))
(defn- congrLen [A a1 a2 h]
  (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf A) (natT) a1 a2
          (e/lam "l" (listOf A) (lengthL A (e/bvar 0)) :default) h))

;; List.filter_count_incr : count (filter p (D ++ dD)) = count (filter p D) + count (filter p dD)
(defn prove-filter-count-incr []
  (let [A (e/fvar 1) p (e/fvar 2) D (e/fvar 3) dD (e/fvar 4)
        fa (e/app* (e/const' (nm "List.filter_append") [z]) A p D dD)
        c  (congrLen A (filterL A p (appendL A D dD)) (appendL A (filterL A p D) (filterL A p dD)) fa)
        la (e/app* (e/const' (nm "List.length_append") [z]) A (filterL A p D) (filterL A p dD))
        result (trN (lengthL A (filterL A p (appendL A D dD)))
                    (lengthL A (appendL A (filterL A p D) (filterL A p dD)))
                    (hadd (lengthL A (filterL A p D)) (lengthL A (filterL A p dD))) c la)
        concl (eqN (lengthL A (filterL A p (appendL A D dD)))
                   (hadd (lengthL A (filterL A p D)) (lengthL A (filterL A p dD))))
        boolP (e/forall' "_" A (e/const' (nm "Bool") []) :default)
        goal (-> concl
                 (#(e/forall' "dD" (listOf A) (e/abstract1 % 4) :default))
                 (#(e/forall' "D" (listOf A) (e/abstract1 % 3) :default))
                 (#(e/forall' "p" boolP (e/abstract1 % 2) :default))
                 (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        proof (-> result
                  (#(e/lam "dD" (listOf A) (e/abstract1 % 4) :default))
                  (#(e/lam "D" (listOf A) (e/abstract1 % 3) :default))
                  (#(e/lam "p" boolP (e/abstract1 % 2) :default))
                  (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    [goal proof]))

;; Map.join_count_incr : count (join xs (ys ++ dys)) = count (join xs ys) + count (join xs dys)
;; The DIFFERENTIAL JOIN (semi-naive): join the NEW build tuples dys against the fixed probe xs.
(defn prove-join-count-incr []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6)
        xs (e/fvar 7) ys (e/fvar 8) dys (e/fvar 9) XY (prodT X Y)
        jApp (e/app* (e/const' (nm "Map.join_append_perm") []) K X Y dec kf lf xs ys dys)
        jBig (joinL K X Y dec kf lf xs (appendL Y ys dys))
        jL (joinL K X Y dec kf lf xs ys) jR (joinL K X Y dec kf lf xs dys)
        lenEq (e/app* (e/const' (nm "List.Perm.length_eq") [z]) XY jBig (appendL XY jL jR) jApp)
        lenApp (e/app* (e/const' (nm "List.length_append") [z]) XY jL jR)
        result (trN (lengthL XY jBig) (lengthL XY (appendL XY jL jR)) (hadd (lengthL XY jL) (lengthL XY jR)) lenEq lenApp)
        concl (eqN (lengthL XY jBig) (hadd (lengthL XY jL) (lengthL XY jR)))
        XtoK (e/forall' "_" X K :default) YtoK (e/forall' "_" Y K :default)
        wrap (fn [build mk]
               (-> build
                   (#(mk "dys" (listOf Y) 9 %)) (#(mk "ys" (listOf Y) 8 %)) (#(mk "xs" (listOf X) 7 %))
                   (#(mk "lf" YtoK 6 %)) (#(mk "kf" XtoK 5 %))
                   (#(mk "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) 4 %))
                   (#(mk "Y" type0 3 %)) (#(mk "X" type0 2 %)) (#(mk "K" type0 1 %))))
        goal (wrap concl (fn [n t i b] (e/forall' n t (e/abstract1 b i) :default)))
        proof (wrap result (fn [n t i b] (e/lam n t (e/abstract1 b i) :default)))]
    [goal proof]))

;; helpers for the bilinear product rule
(defn- cgN [a1 a2 fexpr h] (e/app* (e/const' (nm "congrArg") [L1 L1]) (natT) (natT) a1 a2 fexpr h))
(defn- addCong [a1 a1' a2 a2' h1 h2]            ; h1:a1=a1', h2:a2=a2' → a1+a2 = a1'+a2'
  (trN (hadd a1 a2) (hadd a1' a2) (hadd a1' a2')
       (cgN a1 a1' (e/lam "w" (natT) (hadd (e/bvar 0) a2) :default) h1)
       (cgN a2 a2' (e/lam "w" (natT) (hadd a1' (e/bvar 0)) :default) h2)))
(defn- jlc [K X Y dec kf lf xs ys] (e/app* (e/const' (nm "Map.join_length_comm") []) K X Y dec kf lf xs ys))
(defn- jci [K X Y dec kf lf xs ys dys] (e/app* (e/const' (nm "Map.join_count_incr") []) K X Y dec kf lf xs ys dys))
(defn- jcil [K X Y dec kf lf xs dxs b] (e/app* (e/const' (nm "Map.join_count_incr_left") []) K X Y dec kf lf xs dxs b))

;; Map.join_count_incr_left : count(join (xs++dxs) b) = count(join xs b) + count(join dxs b).
;; Probe-side linearity (equi_join_bilinear conjunct 1), derived from the build-side law via
;; join_length_comm (count is join-commutative): swap → split on the build side → swap back.
(defn prove-join-count-incr-left []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6)
        xs (e/fvar 7) dxs (e/fvar 8) b (e/fvar 9) XY (prodT X Y) YX (prodT Y X)
        s1 (jlc K X Y dec kf lf (appendL X xs dxs) b)
        s2 (jci K Y X dec lf kf b xs dxs)
        s3a (jlc K Y X dec lf kf b xs) s3b (jlc K Y X dec lf kf b dxs)
        c-lhs (lengthL XY (joinL K X Y dec kf lf (appendL X xs dxs) b))
        mid1  (lengthL YX (joinL K Y X dec lf kf b (appendL X xs dxs)))
        a1 (lengthL YX (joinL K Y X dec lf kf b xs)) a2 (lengthL YX (joinL K Y X dec lf kf b dxs))
        a1' (lengthL XY (joinL K X Y dec kf lf xs b)) a2' (lengthL XY (joinL K X Y dec kf lf dxs b))
        step12 (trN c-lhs mid1 (hadd a1 a2) s1 s2)
        result (trN c-lhs (hadd a1 a2) (hadd a1' a2') step12 (addCong a1 a1' a2 a2' s3a s3b))
        concl (eqN c-lhs (hadd a1' a2'))
        XtoK (e/forall' "_" X K :default) YtoK (e/forall' "_" Y K :default)
        wrap (fn [t mk] (-> t (#(mk "b" (listOf Y) 9 %)) (#(mk "dxs" (listOf X) 8 %)) (#(mk "xs" (listOf X) 7 %))
                            (#(mk "lf" YtoK 6 %)) (#(mk "kf" XtoK 5 %))
                            (#(mk "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) 4 %))
                            (#(mk "Y" type0 3 %)) (#(mk "X" type0 2 %)) (#(mk "K" type0 1 %))))]
    [(wrap concl (fn [n t i bd] (e/forall' n t (e/abstract1 bd i) :default)))
     (wrap result (fn [n t i bd] (e/lam n t (e/abstract1 bd i) :default)))]))

;; Map.join_count_product : the BILINEAR product rule for count — BOTH relations change (insert).
;;   count(join (xs⊎dxs)(ys⊎dys)) = (count(join xs ys)+count(join dxs ys)) + (count(join xs dys)+count(join dxs dys))
;; The DBSP differential join (equi_join_bilinear): split the build side (join_count_incr), then the
;; probe side (join_count_incr_left) on each — the 4-term cross-product of old/new × old/new.
(defn prove-join-count-product []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6)
        xs (e/fvar 7) dxs (e/fvar 8) ys (e/fvar 9) dys (e/fvar 10)
        XY (prodT X Y) XD (appendL X xs dxs)
        jf (fn [p b] (lengthL XY (joinL K X Y dec kf lf p b)))
        B1 (jf XD ys) B2 (jf XD dys)
        L1a (jf xs ys) L1b (jf dxs ys) L2a (jf xs dys) L2b (jf dxs dys)
        s1 (jci K X Y dec kf lf XD ys dys)
        h1 (jcil K X Y dec kf lf xs dxs ys) h2 (jcil K X Y dec kf lf xs dxs dys)
        result (trN (jf XD (appendL Y ys dys)) (hadd B1 B2) (hadd (hadd L1a L1b) (hadd L2a L2b))
                    s1 (addCong B1 (hadd L1a L1b) B2 (hadd L2a L2b) h1 h2))
        concl (eqN (jf XD (appendL Y ys dys)) (hadd (hadd L1a L1b) (hadd L2a L2b)))
        XtoK (e/forall' "_" X K :default) YtoK (e/forall' "_" Y K :default)
        wrap (fn [t mk] (-> t (#(mk "dys" (listOf Y) 10 %)) (#(mk "ys" (listOf Y) 9 %))
                            (#(mk "dxs" (listOf X) 8 %)) (#(mk "xs" (listOf X) 7 %))
                            (#(mk "lf" YtoK 6 %)) (#(mk "kf" XtoK 5 %))
                            (#(mk "dec" (e/app (e/const' (nm "DecidableEq") [L1]) K) 4 %))
                            (#(mk "Y" type0 3 %)) (#(mk "X" type0 2 %)) (#(mk "K" type0 1 %))))]
    [(wrap concl (fn [n t i bd] (e/forall' n t (e/abstract1 bd i) :default)))
     (wrap result (fn [n t i bd] (e/lam n t (e/abstract1 bd i) :default)))]))

;; ── COMPOSITION: incrementalize a PIPELINE from its parts ((Q1∘Q2)^Δ = Q1^Δ∘Q2^Δ, Prop 5.2) ────
;; The modularity property: a composition of linear operators followed by a monoid-homomorphism
;; aggregate is itself incremental. Canonical instance — the SQL aggregate `SELECT sum(g(x)) WHERE p(x)`,
;; agg l = foldl (λa x. a + g x) 0 (filter p l): filter (linear) ∘ sum (homomorphism). Chains
;; filter_append → foldl_append → foldl_add_init. (The GENERAL composition theorem over arbitrary
;; linear operators lives in the stream-operator algebra — the next rung.)
(defn- addN [a b] (e/app* (e/const' (nm "Nat.add") []) a b))
(def ^:private zeroN (e/const' (nm "Nat.zero") []))
(defn- stepG [A g] (e/lam "a" (natT) (e/lam "x" A (addN (e/bvar 1) (e/app g (e/bvar 0))) :default) :default))
(defn- foldlN [A step init l] (e/app* (e/const' (nm "List.foldl") [z z]) (natT) A step init l))

(defn prove-sum-filter-incr []
  (let [A (e/fvar 1) g (e/fvar 2) p (e/fvar 3) D (e/fvar 4) dD (e/fvar 5)
        step (stepG A g) FpD (filterL A p D) FpdD (filterL A p dD)
        agg (fn [l] (foldlN A step zeroN (filterL A p l)))
        fa (e/app* (e/const' (nm "List.filter_append") [z]) A p D dD)
        c (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf A) (natT)
                  (filterL A p (appendL A D dD)) (appendL A FpD FpdD)
                  (e/lam "l" (listOf A) (foldlN A step zeroN (e/bvar 0)) :default) fa)
        fla (e/app* (e/const' (nm "List.foldl_append") [z z]) A (natT) step zeroN FpD FpdD)
        fai (e/app* (e/const' (nm "List.foldl_add_init") []) A g FpdD (foldlN A step zeroN FpD))
        result (trN (foldlN A step zeroN (filterL A p (appendL A D dD)))
                    (foldlN A step zeroN (appendL A FpD FpdD))
                    (addN (agg D) (agg dD))
                    c (trN (foldlN A step zeroN (appendL A FpD FpdD))
                           (foldlN A step (foldlN A step zeroN FpD) FpdD)
                           (addN (agg D) (agg dD)) fla fai))
        concl (eqN (agg (appendL A D dD)) (addN (agg D) (agg dD)))
        boolP (e/forall' "_" A (e/const' (nm "Bool") []) :default) gNat (e/forall' "_" A (natT) :default)
        wrap (fn [t mk] (-> t (#(mk "dD" (listOf A) 5 %)) (#(mk "D" (listOf A) 4 %))
                            (#(mk "p" boolP 3 %)) (#(mk "g" gNat 2 %)) (#(mk "A" type0 1 %))))]
    [(wrap concl (fn [n t i bd] (e/forall' n t (e/abstract1 bd i) :default)))
     (wrap result (fn [n t i bd] (e/lam n t (e/abstract1 bd i) :default)))]))

;; ── Z-SETS: deletions via a weighted carrier (element → ℤ), an abelian GROUP ────────────────────
;; A Z-set ℤ[A] (DBSP §4.1) is element→ℤ with finite support; the concrete carrier is List(A×Int),
;; where ++ is the group addition (pre-consolidation) and a NEGATIVE weight is a retraction. The
;; aggregate is `Zset.weight = Σ multiplicities` (DBSP |m| = Σ m[x]). Because ℤ is a group, the SAME
;; increment law handles INSERTIONS and DELETIONS uniformly — `weight` is a group homomorphism, so it
;; is LINEAR and its incremental version is itself (DBSP Theorem 5.4: linear ⇒ Q^Δ = Q). DBSP itself
;; is Lean-formalized; this is the CIC-kernel analogue.
(def ^:private intT (e/const' (nm "Int") []))
(defn- iAdd [a b] (e/app* (e/const' (nm "Int.add") []) a b))
(def ^:private iZero (e/app* (e/const' (nm "OfNat.ofNat") [z]) intT (e/lit-nat 0)
                             (e/app* (e/const' (nm "instOfNat") []) (e/lit-nat 0))))
(defn- stepfn [Y g] (e/lam "a" intT (e/lam "x" Y (iAdd (e/bvar 1) (e/app g (e/bvar 0))) :default) :default))
(defn- foldlIE [Y stp init l] (e/app* (e/const' (nm "List.foldl") [z z]) intT Y stp init l))
(defn- weightL [A l] (e/app* (e/const' (nm "Zset.weight") []) A l))

;; Zset.weight A l = Σ snd over entries (foldl (λa p. a + snd p) 0).
(defn weight-def []
  (let [A (e/fvar 1) E (prodT A intT)]
    (kenv/mk-def (nm "Zset.weight") []
      (-> intT
          (#(e/forall' "l" (listOf (prodT (e/fvar 1) intT)) % :default))
          (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
      (-> (foldlIE E (stepfn E (e/lam "p" E (sndOf A intT (e/bvar 0)) :default)) iZero (e/fvar 2))
          (#(e/lam "l" (listOf E) (e/abstract1 % 2) :default))
          (#(e/lam "A" type0 (e/abstract1 % 1) :default))))))

;; Zset.foldl_int_init : foldl (λa x. a + g x) acc l = acc + foldl (…) 0 l  (init-extraction over ℤ).
(defn prove-int-foldl-init []
  (let [Y (e/fvar 1) g (e/fvar 2) l (e/fvar 3) stp (stepfn Y g)
        goal (-> (e/forall' "acc" intT
                   (e/app* (e/const' (nm "Eq") [L1]) intT
                           (foldlIE Y stp (e/bvar 0) l) (iAdd (e/bvar 0) (foldlIE Y stp iZero l))) :default)
                 (#(e/forall' "l" (listOf Y) (e/abstract1 % 3) :default))
                 (#(e/forall' "g" (e/forall' "_" Y intT :default) (e/abstract1 % 2) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["Y" "g" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid) cg (proof/current-goal psg)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx cg))]
                (if cons?
                  (let [psg (basic/intros psg ["acc"])
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih")) ih (e/fvar ihid)
                        g (gf psg "g") head (gf psg "head") acc (gf psg "acc") Y (gf psg "Y") tail (gf psg "tail")
                        gh (e/app g head) stp (stepfn Y g) F (foldlIE Y stp iZero tail)
                        q (simp/simp psg ['List.foldl_cons])
                        q (basic/rewrite q (e/app ih (iAdd acc gh)))
                        q (basic/rewrite q (e/app ih (iAdd iZero gh)))
                        cgf (fn [fexpr a1 a2 h] (e/app* (e/const' (nm "congrArg") [L1 L1]) intT intT a1 a2 fexpr h))
                        addAssoc (e/app* (e/const' (nm "Int.add_assoc") []) acc gh F)
                        zaS (e/app* (e/const' (nm "Eq.symm") [L1]) intT (iAdd iZero gh) gh
                                    (e/app* (e/const' (nm "Int.zero_add") []) gh))
                        plusF (e/lam "w" intT (iAdd (e/bvar 0) F) :default)
                        accPlus (e/lam "w" intT (iAdd acc (e/bvar 0)) :default)
                        inner (cgf plusF gh (iAdd iZero gh) zaS)
                        p2 (cgf accPlus (iAdd gh F) (iAdd (iAdd iZero gh) F) inner)
                        result (e/app* (e/const' (nm "Eq.trans") [L1]) intT
                                       (iAdd (iAdd acc gh) F) (iAdd acc (iAdd gh F))
                                       (iAdd acc (iAdd (iAdd iZero gh) F)) addAssoc p2)]
                    (basic/exact q result))
                  (let [psg (basic/intros psg ["acc"]) acc (gf psg "acc")]
                    (basic/exact psg (e/app* (e/const' (nm "Eq.symm") [L1]) intT (iAdd acc iZero) acc
                                             (e/app* (e/const' (nm "Int.add_zero") []) acc)))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Zset.weight_append : weight (D ++ dD) = weight D + weight dD  — linearity of weight (Thm 5.4).
;; INSERTIONS and DELETIONS alike: dD may carry negative weights (retractions); ℤ is a group.
(defn prove-weight-append []
  (let [A (e/fvar 1) D (e/fvar 2) dD (e/fvar 3) E (prodT A intT)
        sndg (e/lam "p" E (sndOf A intT (e/bvar 0)) :default) stp (stepfn E sndg)
        e1 (e/app* (e/const' (nm "List.foldl_append") [z z]) E intT stp iZero D dD)
        e2 (e/app* (e/const' (nm "Zset.foldl_int_init") []) E sndg dD (foldlIE E stp iZero D))
        result (e/app* (e/const' (nm "Eq.trans") [L1]) intT
                       (foldlIE E stp iZero (appendL E D dD))
                       (foldlIE E stp (foldlIE E stp iZero D) dD)
                       (iAdd (weightL A D) (weightL A dD)) e1 e2)
        concl (e/app* (e/const' (nm "Eq") [L1]) intT (weightL A (appendL E D dD)) (iAdd (weightL A D) (weightL A dD)))
        goal (-> concl
                 (#(e/forall' "dD" (listOf E) (e/abstract1 % 3) :default))
                 (#(e/forall' "D" (listOf E) (e/abstract1 % 2) :default))
                 (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        proof (-> result
                  (#(e/lam "dD" (listOf E) (e/abstract1 % 3) :default))
                  (#(e/lam "D" (listOf E) (e/abstract1 % 2) :default))
                  (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    [goal proof]))

;; Zset.filter_weight_incr : weight (filter (p∘fst) (D++dD)) = weight(filter…D) + weight(filter…dD).
;; The DBSP linear operator σ_P (filtering preserves weights), incrementalized — with deletions.
(defn prove-filter-weight-incr []
  (let [A (e/fvar 1) p (e/fvar 2) D (e/fvar 3) dD (e/fvar 4) E (prodT A intT)
        pe (e/lam "e" E (e/app p (fstOf A intT (e/bvar 0))) :default)
        flt (fn [l] (e/app* (e/const' (nm "List.filter") [z]) E pe l))
        fa (e/app* (e/const' (nm "List.filter_append") [z]) E pe D dD)
        wfn (e/lam "l" (listOf E) (weightL A (e/bvar 0)) :default)
        c (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf E) intT
                  (flt (appendL E D dD)) (appendL E (flt D) (flt dD)) wfn fa)
        wa (e/app* (e/const' (nm "Zset.weight_append") []) A (flt D) (flt dD))
        result (e/app* (e/const' (nm "Eq.trans") [L1]) intT
                       (weightL A (flt (appendL E D dD)))
                       (weightL A (appendL E (flt D) (flt dD)))
                       (iAdd (weightL A (flt D)) (weightL A (flt dD))) c wa)
        concl (e/app* (e/const' (nm "Eq") [L1]) intT (weightL A (flt (appendL E D dD)))
                      (iAdd (weightL A (flt D)) (weightL A (flt dD))))
        boolP (e/forall' "_" A (e/const' (nm "Bool") []) :default)
        goal (-> concl
                 (#(e/forall' "dD" (listOf E) (e/abstract1 % 4) :default))
                 (#(e/forall' "D" (listOf E) (e/abstract1 % 3) :default))
                 (#(e/forall' "p" boolP (e/abstract1 % 2) :default))
                 (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        proof (-> result
                  (#(e/lam "dD" (listOf E) (e/abstract1 % 4) :default))
                  (#(e/lam "D" (listOf E) (e/abstract1 % 3) :default))
                  (#(e/lam "p" boolP (e/abstract1 % 2) :default))
                  (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    [goal proof]))

(defonce ^:private cache (atom nil))

(defn install!
  "Admit the insert-only IVM laws (`List.filter_count_incr`, `Map.join_count_incr`) into the global
   env (idempotent). After this, a windowed/streaming count over a filter or a join can be maintained
   incrementally with a kernel certificate that the incremental result equals the batch recomputation.
   Requires kmap/install! + rel-laws/install! (for Map.join_append_perm)."
  []
  (when-not (kenv/lookup (a/env) (nm "Zset.weight_append"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [thm (fn [n [g p]] (kenv/mk-thm (nm n) [] g p))
            cis [(thm "List.filter_count_incr" (prove-filter-count-incr))
                 (thm "Map.join_count_incr"      (prove-join-count-incr))
                 (thm "Map.join_count_incr_left" (prove-join-count-incr-left))  ; probe-side linearity
                 (thm "Map.join_count_product"   (prove-join-count-product))    ; bilinear product rule
                 (thm "List.sum_filter_incr"     (prove-sum-filter-incr))       ; composed aggregate pipeline
                 (weight-def)                                              ; Zset.weight (def)
                 (thm "Zset.foldl_int_init"    (prove-int-foldl-init))
                 (thm "Zset.weight_append"     (prove-weight-append))
                 (thm "Zset.filter_weight_incr" (prove-filter-weight-incr))]]
        (doseq [ci cis] (swap! a/ansatz-env kenv/check-constant ci))
        (reset! cache cis))))
  (a/env))

;; ── incremental runtime: maintain a running aggregate over a sequence of delta batches ──────────
(defn ivm
  "Incremental view maintenance over a SEQUENCE of delta batches. `q` is the per-batch query
   (batch → partial result), `combine`/`id` its result monoid. Returns the running result
   `(reduce combine id (map q deltas))` — applying `q` to each DELTA only. The registered increment
   law (filter_count_incr / join_count_incr) certifies this equals `q` over the concatenation of all
   batches, so IVM never recomputes the whole view. This is the semi-naive loop when `q` joins the
   new tuples against a fixed relation."
  [q combine id deltas]
  (reduce combine id (map q deltas)))

;; ── Z-set runtime (deletions): an entry is [element weight], weight∈ℤ (−1 = retraction) ──────────
(defn zweight
  "Total weight Σ multiplicities of a Z-set (the runtime of `Zset.weight`). With deletions present
   (negative weights) this is the NET cardinality, and it can go DOWN — impossible for an insert-only
   count. `Zset.weight_append` certifies it's a group homomorphism: weight(D⊎dD) = weight(D)+weight(dD)."
  [zset]
  (reduce + 0 (map second zset)))

(defn zfilter
  "Filter a Z-set by a predicate on the ELEMENT, preserving weights (DBSP σ_P, a linear operator)."
  [p zset]
  (filterv (fn [e] (p (first e))) zset))
