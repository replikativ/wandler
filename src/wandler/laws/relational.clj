(ns wandler.laws.relational
  "PACKAGED, INSTALLABLE relational-algebra laws — the proven rewrites the cost optimizer references
   by name (wandler.optimize/cost-rewrites). Each is an Init-only raw-term + tactic proof (previously
   living in test code); `install!` admits them into the env ONCE so the relational optimizations
   (filter→join pushdown, …) become available to a/defn pipelines and optimize-cost — the same jump
   the filterMap law already made via install-filtermap-fusion-law!.

   The proven [name goal proof] tuples are MEMOIZED (Init-only ⇒ env-independent), so re-installing
   after an env reset is cheap (just add-constant the cached theorems). Requires kmap/install!."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]
            [wandler.laws.proofs :as rp]    ; the perm/bucket/join_comm proof chain (clean src home)
            [wandler.laws.semiring :as sreg]    ; the carrier registry the optimizer's frame index reads
            [wandler.laws.proofs.frame :as rpf]))   ; the FAQ frame-rule + semiring-generic proof family

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ z))
(def ^:private type0 (e/sort' L1))
(defn- fv [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(def ^:private fvid fv)                                   ; the foundation proofs call it `fvid`
(defn- gf [ps n] (e/fvar (fv ps n)))                      ; fvar of a named local
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- new-goals [before after] (vec (remove (set before) after)))
(defn- beqg [ps x y]
  (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K")
          (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) x y))

;; stack driver: isolate each goal so per-goal solved? is meaningful
(defn- solve-all [ps step]
  (loop [ps ps n 0]
    (if (or (empty? (:goals ps)) (> n 100)) ps
        (let [g (:goals ps), gid (first g), rest-g (vec (rest g))
              ps2 (try (step (assoc ps :goals [gid])) (catch Throwable _ (assoc ps :goals [])))
              ps3 (assoc ps2 :goals (vec (concat (:goals ps2) rest-g)))]
          (recur ps3 (inc n))))))

(defn- beta-spine [f args]
  (loop [f f args args]
    (if (and (e/lam? f) (seq args))
      (recur (e/instantiate1 (e/lam-body f) (first args)) (rest args))
      (if (seq args) (apply e/app* f args) f))))

;; ── Lemma B : filter (p∘fst) (map (x,·) L) = cond (p x) (map (x,·) L) [] ──
(defn- prove-B []
  (let [z lvl/zero L1 (lvl/succ z) type0 (e/sort' L1)
        boolT (e/const' (nm "Bool") [])
        fX (e/fvar 64001) fY (e/fvar 64002) fp (e/fvar 64003) fx (e/fvar 64004) fL (e/fvar 64005)
        prodXY (e/app* (e/const' (nm "Prod") [z z]) fX fY)
        listP (e/app (e/const' (nm "List") [z]) prodXY)
        mk (e/lam "y" fY (e/app* (e/const' (nm "Prod.mk") [z z]) fX fY fx (e/bvar 0)) :default)
        fstpred (e/lam "pr" prodXY (e/app fp (e/app* (e/const' (nm "Prod.fst") [z z]) fX fY (e/bvar 0))) :default)
        mapmk (fn [l] (e/app* (e/const' (nm "List.map") [z z]) fY prodXY mk l))
        filt (fn [l] (e/app* (e/const' (nm "List.filter") [z]) prodXY fstpred l))
        condR (e/app* (e/const' (nm "cond") [L1]) listP (e/app fp fx) (mapmk fL) (e/app (e/const' (nm "List.nil") [z]) prodXY))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listP (filt (mapmk fL)) condR)
                 (#(e/forall' "L" (e/app (e/const' (nm "List") [z]) fY) (e/abstract1 % 64005) :default))
                 (#(e/forall' "x" fX (e/abstract1 % 64004) :default))
                 (#(e/forall' "p" (e/forall' "_" fX boolT :default) (e/abstract1 % 64003) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 64002) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 64001) :default)))
        LEM ['List.filter_nil 'cond_true 'cond_false 'cond 'List.map_cons 'List.map_nil
             'List.filter_cons_of_pos 'List.filter_cons_of_neg]
        step (fn [ps]
               (cond
                 (fv ps "hc")
                 (let [q1 (basic/rewrite ps (e/fvar (fv ps "hc")))
                       ihid (or (fv q1 "ih_tail'") (fv q1 "ih_tail"))
                       q2 (simp/simp-all q1 LEM)
                       q3 (if (and ihid (not (proof/solved? q2))) (basic/rewrite q2 (e/fvar ihid)) q2)
                       q4 (if (proof/solved? q3) q3 (simp/simp-all q3 LEM))]
                   (if (proof/solved? q4) q4 (basic/rfl q4)))
                 (fv ps "head")
                 (let [q0 (simp/simp ps ['List.map_cons])]
                   (basic/by-cases q0 (e/app (e/fvar (fv q0 "p")) (e/fvar (fv q0 "x")))))
                 :else
                 (let [q (simp/simp-all ps LEM)]
                   (if (proof/solved? q) q
                       (basic/by-cases q (e/app (e/fvar (fv q "p")) (e/fvar (fv q "x"))))))))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "Y" "p" "x" "L"])
        ps (basic/induction ps (fv ps "L"))
        ps (solve-all ps step)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── Lemma A : per-row premise ⇒ filter pushes through flatMap ──
(defn- prove-A []
  (let [z lvl/zero L1 (lvl/succ z) type0 (e/sort' L1)
        boolT (e/const' (nm "Bool") [])
        fa (e/fvar 63001) fb (e/fvar 63002) fg (e/fvar 63003) fq (e/fvar 63004) fp (e/fvar 63005) fxs (e/fvar 63006)
        listOf (fn [t] (e/app (e/const' (nm "List") [z]) t))
        listA (listOf fa) listB (listOf fb)
        flatmap (fn [g l] (e/app* (e/const' (nm "List.flatMap") [z z]) fa fb g l))
        filterB (fn [l] (e/app* (e/const' (nm "List.filter") [z]) fb fq l))
        filterA (fn [l] (e/app* (e/const' (nm "List.filter") [z]) fa fp l))
        condB (fn [px gx] (e/app* (e/const' (nm "cond") [L1]) listB px gx (e/app (e/const' (nm "List.nil") [z]) fb)))
        hyp (e/forall' "x" fa
                       (e/app* (e/const' (nm "Eq") [L1]) listB
                               (filterB (e/app fg (e/bvar 0)))
                               (condB (e/app fp (e/bvar 0)) (e/app fg (e/bvar 0)))) :default)
        concl (e/app* (e/const' (nm "Eq") [L1]) listB (filterB (flatmap fg fxs)) (flatmap fg (filterA fxs)))
        goal (-> (e/forall' "H" hyp concl :default)
                 (#(e/forall' "xs" listA (e/abstract1 % 63006) :default))
                 (#(e/forall' "p"  (e/forall' "_" fa boolT :default) (e/abstract1 % 63005) :default))
                 (#(e/forall' "q"  (e/forall' "_" fb boolT :default) (e/abstract1 % 63004) :default))
                 (#(e/forall' "g"  (e/forall' "_" fa listB :default) (e/abstract1 % 63003) :default))
                 (#(e/forall' "b"  type0 (e/abstract1 % 63002) :default))
                 (#(e/forall' "a"  type0 (e/abstract1 % 63001) :default)))
        LEM ['List.filter_cons_of_pos 'List.filter_cons_of_neg 'List.flatMap_cons 'List.flatMap_nil
             'List.filter_nil 'cond_true 'cond_false 'List.filter_append 'cond
             'List.append_nil 'List.nil_append 'List.append_eq 'List.cons_append
             'List.flatten_cons 'List.map_cons 'List.filter_cons 'List.flatMap_append]
        step (fn [ps]
               (cond
                 (fv ps "hc")
                 (let [hcid (fv ps "hc")
                       p2 (basic/rewrite ps (e/fvar hcid))
                       q (simp/simp-all p2 LEM)
                       ihid (or (fv q "ih_tail'") (fv q "ih_tail"))
                       q2 (if (and ihid (not (proof/solved? q))) (basic/rewrite q (e/fvar ihid)) q)
                       q3 (if (proof/solved? q2) q2 (simp/simp-all q2 LEM))
                       hc2 (fv q3 "hc")
                       q4 (if (and hc2 (not (proof/solved? q3))) (basic/rewrite q3 (e/fvar hc2)) q3)
                       q5 (if (proof/solved? q4) q4 (simp/simp-all q4 LEM))]
                   (if (proof/solved? q5) q5 (basic/rfl q5)))
                 (fv ps "head")
                 (let [hd (fv ps "head")
                       p0 (simp/simp ps ['List.flatMap_cons 'List.filter_append] {})
                       p1 (basic/rewrite p0 (e/app (e/fvar (fv p0 "H")) (e/fvar hd)))
                       ph (e/app (e/fvar (fv p1 "p")) (e/fvar hd))]
                   (basic/by-cases p1 ph))
                 :else
                 (let [q (simp/simp-all ps LEM)]
                   (if (proof/solved? q) q (basic/rfl q)))))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["a" "b" "g" "q" "p" "xs" "H"])
        ps (basic/induction ps (fv ps "xs"))
        ps (solve-all ps step)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── C : compose A with B as the per-row premise for Map.join ──
(defn- compose-C []
  (let [z lvl/zero L1 (lvl/succ z)
        nat (e/const' (nm "Nat") [])
        prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat)
        listN (e/app (e/const' (nm "List") [z]) nat)
        listNN (e/app (e/const' (nm "List") [z]) prodNN)
        deceq (e/const' (nm "instDecidableEqNat") [])
        boolT (e/const' (nm "Bool") [])
        n->n (e/forall' "_" nat nat :default) n->b (e/forall' "_" nat boolT :default)
        pp (e/fvar 62001) kf (e/fvar 62002) lf (e/fvar 62003) ys (e/fvar 62004) xs (e/fvar 62005)
        joinT (fn [xs'] (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq kf lf xs' ys))
        predPair (e/lam "pr" prodNN (e/app pp (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
        filterPair (fn [l] (e/app* (e/const' (nm "List.filter") [z]) prodNN predPair l))
        filterN (fn [l] (e/app* (e/const' (nm "List.filter") [z]) nat pp l))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listNN (filterPair (joinT xs)) (joinT (filterN xs)))
                 (#(e/forall' "xs" listN (e/abstract1 % 62005) :default))
                 (#(e/forall' "ys" listN (e/abstract1 % 62004) :default))
                 (#(e/forall' "lf" n->n (e/abstract1 % 62003) :default))
                 (#(e/forall' "kf" n->n (e/abstract1 % 62002) :default))
                 (#(e/forall' "p"  n->b (e/abstract1 % 62001) :default)))
        mj-val (.getValue (kenv/lookup (a/env) (nm "Map.join")))
        join-1 (beta-spine mj-val [nat nat nat deceq kf lf xs ys])
        g (nth (second (e/get-app-fn-args join-1)) 2)
        Bc (e/const' (nm "List.filter_map_pair_eq_cond") [])
        premise (e/lam "a" nat
                        (let [ga (e/instantiate1 (e/lam-body g) (e/bvar 0))
                              La (nth (second (e/get-app-fn-args ga)) 3)]
                          (e/app* Bc nat nat pp (e/bvar 0) La)) :default)
        Ac (e/const' (nm "List.filter_flatMap_cond") [])
        C (e/app* Ac nat prodNN g predPair pp xs premise)
        C-closed (-> C
                     (#(e/lam "xs" listN (e/abstract1 % 62005) :default))
                     (#(e/lam "ys" listN (e/abstract1 % 62004) :default))
                     (#(e/lam "lf" n->n (e/abstract1 % 62003) :default))
                     (#(e/lam "kf" n->n (e/abstract1 % 62002) :default))
                     (#(e/lam "p"  n->b (e/abstract1 % 62001) :default)))]
    [goal C-closed]))

;; ══ lookup / group_by FOUNDATION (the SEMIJOIN's stepping stones) ════════════
;; isSome (Map.lookup k (Map.group_by id xs)) = List.elem k xs — built bottom-up. (Moved from
;; kmap-lookup-test / kmap-group-by-test so it's installable; the hard piece is the foldl invariant
;; lookup_group_by_gen, by generalizing over the accumulator.)

;; List.lookup_filter_ne : k ≠ k' → lookup k (filter (·.fst ≠ k') l) = lookup k l
(defn- prove-lookup-filter-ne []
  (let [fK (e/fvar 80001) fV (e/fvar 80002) fd (e/fvar 80003)
        fk (e/fvar 80004) fk' (e/fvar 80005) fm (e/fvar 80006)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        prodKV (e/app* (e/const' (nm "Prod") [z z]) fK fV)
        listKV (e/app (e/const' (nm "List") [z]) prodKV)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        beq (fn [x y] (e/app* (e/const' (nm "BEq.beq") [z]) fK beqI x y))
        fstp (fn [p] (e/app* (e/const' (nm "Prod.fst") [z z]) fK fV p))
        pred (e/lam "p" prodKV (e/app (e/const' (nm "Bool.not") []) (beq (fstp (e/bvar 0)) fk')) :default)
        filt (fn [l] (e/app* (e/const' (nm "List.filter") [z]) prodKV pred l))
        lookup (fn [l] (e/app* (e/const' (nm "List.lookup") [z z]) fK fV beqI fk l))
        boolT (e/const' (nm "Bool") [])
        hyp (e/app* (e/const' (nm "Eq") [L1]) boolT (beq fk fk') (e/const' (nm "Bool.false") []))
        concl (e/app* (e/const' (nm "Eq") [L1]) (e/app (e/const' (nm "Option") [z]) fV) (lookup (filt fm)) (lookup fm))
        goal (-> (e/forall' "hne" hyp concl :default)
                 (#(e/forall' "m" listKV (e/abstract1 % 80006) :default))
                 (#(e/forall' "k'" fK (e/abstract1 % 80005) :default))
                 (#(e/forall' "k" fK (e/abstract1 % 80004) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 80003) :default))
                 (#(e/forall' "V" type0 (e/abstract1 % 80002) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 80001) :default)))
        LEM ['List.filter_nil 'List.filter_cons_of_pos 'List.filter_cons_of_neg
             'List.lookup_cons 'List.lookup_nil 'List.lookup_cons_self 'Bool.not_true 'Bool.not_false]
        ihid (fn [ps] (or (fv ps "ih_tail'") (fv ps "ih_tail") (fv ps "ih")))
        hc-removed? (fn [ps]
                      (let [ht (some (fn [[_ d]] (when (= "hc" (:name d)) (:type d))) (:lctx (proof/current-goal ps)))
                            [_ args] (e/get-app-fn-args ht)]
                        (= "Bool.true" (name/->string (e/const-name (nth args 2))))))
        solve-removed
        (fn [ps]
          (let [gK (gf ps "K") gfst (gf ps "fst")
                lawfulP (e/app* (e/const' (nm "instLawfulBEqOfDecidableEq") []) gK (gf ps "dec"))
                biff (e/app* (e/const' (nm "beq_iff_eq") [z]) gK
                             (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) gK (gf ps "dec"))
                             lawfulP gfst (gf ps "k'"))
                hfeq (e/app* (e/const' (nm "Iff.mp") [])
                             (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") []) (beqg ps gfst (gf ps "k'")) (e/const' (nm "Bool.true") []))
                             (e/app* (e/const' (nm "Eq") [L1]) gK gfst (gf ps "k'")) biff (gf ps "hc"))
                i (ihid ps)
                q (try (simp/simp-all ps LEM) (catch Throwable _ ps))
                q (if (and i (not (proof/solved? q))) (try (basic/rewrite q (e/fvar i)) (catch Throwable _ q)) q)
                q (if (proof/solved? q) q (try (basic/rewrite q hfeq) (catch Throwable _ q)))
                q (if (proof/solved? q) q (try (simp/simp-all q LEM) (catch Throwable _ q)))
                q (if (proof/solved? q) q (try (basic/rewrite q (e/fvar (fv q "hne"))) (catch Throwable _ q)))
                q (if (proof/solved? q) q (try (simp/simp-all q LEM) (catch Throwable _ q)))]
            (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))
        solve-kept
        (fn [ps]
          (let [i (ihid ps) ps (try (simp/simp-all ps LEM) (catch Throwable _ ps))]
            (if (proof/solved? ps) ps
                (let [before (:goals ps)
                      br (basic/by-cases ps (beqg ps (gf ps "k") (gf ps "fst")))
                      bids (new-goals before (:goals br))]
                  (reduce (fn [ps bid]
                            (let [psb (focus ps bid)
                                  q (try (simp/simp-all psb LEM) (catch Throwable _ psb))
                                  q (if (and i (not (proof/solved? q))) (try (basic/rewrite q (e/fvar i)) (catch Throwable _ q)) q)
                                  q (if (proof/solved? q) q (try (simp/simp-all q LEM) (catch Throwable _ q)))]
                              (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))
                          br bids)))))
        solve-cons
        (fn [ps]
          (let [ps (basic/induction ps (fv ps "head"))
                before (:goals ps)
                br (basic/by-cases ps (beqg ps (gf ps "fst") (gf ps "k'")))
                bids (new-goals before (:goals br))]
            (reduce (fn [ps bid]
                      (let [psb (focus ps bid)]
                        (if (hc-removed? psb) (solve-removed psb) (solve-kept psb))))
                    br bids)))
        solve-loop
        (fn [ps]
          (loop [ps ps n 0]
            (if (or (empty? (:goals ps)) (> n 30)) ps
                (let [g (:goals ps) gid (first g) rest-g (vec (rest g))
                      psf (focus ps gid)
                      ps2 (try (if (fv psf "head") (solve-cons psf)
                                   (let [q (try (simp/simp-all psf LEM) (catch Throwable _ psf))]
                                     (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))
                               (catch Throwable _ psf))
                      ps3 (assoc ps2 :goals (vec (concat (:goals ps2) rest-g)))]
                  (recur ps3 (inc n))))))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "dec" "k" "k'" "m" "hne"])
        ps (basic/induction ps (fv ps "m"))
        ps (solve-loop ps)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; List.lookup_insert
(defn- prove-lookup-insert []
  (let [fK (e/fvar 81001) fV (e/fvar 81002) fd (e/fvar 81003)
        fk (e/fvar 81004) fk' (e/fvar 81005) fvv (e/fvar 81006) fl (e/fvar 81007)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        prodKV (e/app* (e/const' (nm "Prod") [z z]) fK fV)
        listKV (e/app (e/const' (nm "List") [z]) prodKV)
        optV (e/app (e/const' (nm "Option") [z]) fV)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        beq (fn [x y] (e/app* (e/const' (nm "BEq.beq") [z]) fK beqI x y))
        fstp (fn [p] (e/app* (e/const' (nm "Prod.fst") [z z]) fK fV p))
        pred (e/lam "p" prodKV (e/app (e/const' (nm "Bool.not") []) (beq (fstp (e/bvar 0)) fk')) :default)
        filt (e/app* (e/const' (nm "List.filter") [z]) prodKV pred fl)
        headp (e/app* (e/const' (nm "Prod.mk") [z z]) fK fV fk' fvv)
        insl (e/app* (e/const' (nm "List.cons") [z]) prodKV headp filt)
        lookup (fn [l] (e/app* (e/const' (nm "List.lookup") [z z]) fK fV beqI fk l))
        rhs (e/app* (e/const' (nm "cond") [L1]) optV (beq fk fk')
                    (e/app* (e/const' (nm "Option.some") [z]) fV fvv) (lookup fl))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) optV (lookup insl) rhs)
                 (#(e/forall' "l" listKV (e/abstract1 % 81007) :default))
                 (#(e/forall' "v" fV (e/abstract1 % 81006) :default))
                 (#(e/forall' "k'" fK (e/abstract1 % 81005) :default))
                 (#(e/forall' "k" fK (e/abstract1 % 81004) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 81003) :default))
                 (#(e/forall' "V" type0 (e/abstract1 % 81002) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 81001) :default)))
        LEM ['List.lookup_cons 'cond_true 'cond_false 'cond 'List.lookup_cons_self 'List.lookup_nil]
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "dec" "k" "k'" "v" "l"])
        lfn-app (fn [ps hcid]
                  (e/app* (e/const' (nm "List.lookup_filter_ne") [])
                          (gf ps "K") (gf ps "V") (gf ps "dec") (gf ps "k") (gf ps "k'") (gf ps "l") (e/fvar hcid)))
        before (:goals ps)
        br (basic/by-cases ps (beqg ps (gf ps "k") (gf ps "k'")))
        bids (new-goals before (:goals br))
        ps (reduce (fn [ps bid]
                     (let [psb (focus ps bid)
                           hc (fv psb "hc")
                           removed? (= "Bool.true" (name/->string (e/const-name (nth (second (e/get-app-fn-args (:type (some (fn [[_ d]] (when (= "hc" (:name d)) d)) (:lctx (proof/current-goal psb)))))) 2))))
                           q (try (simp/simp psb ['List.lookup_cons]) (catch Throwable _ psb))
                           q (try (basic/rewrite q (e/fvar hc)) (catch Throwable _ q))
                           q (try (simp/simp-all q LEM) (catch Throwable _ q))
                           q (if removed? q (try (basic/rewrite q (lfn-app q hc)) (catch Throwable _ q)))
                           q (try (simp/simp-all q LEM) (catch Throwable _ q))]
                       (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))
                   br bids)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.gbStepId : the group_by id fold step (an opaque def, not a theorem)
(defn- gbstepid-ci []
  (let [fK (e/fvar 84001) fd (e/fvar 84003)
        listK (e/app (e/const' (nm "List") [z]) fK)
        mapKLK (e/app* (e/const' (nm "Map") [z z]) fK listK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        x (e/bvar 0) m (e/bvar 1)
        bucket (e/app* (e/const' (nm "List.cons") [z]) fK x (e/app* (e/const' (nm "Option.getD") [z]) listK (e/app* (e/const' (nm "Map.lookup") []) fK listK fd x m) (e/app (e/const' (nm "List.nil") [z]) fK)))
        inner (e/app* (e/const' (nm "Map.insert") []) fK listK fd x bucket m)
        val (-> inner (#(e/lam "x" fK % :default)) (#(e/lam "m" mapKLK % :default))
                (#(e/lam "dec" deceqK (e/abstract1 % 84003) :default)) (#(e/lam "K" type0 (e/abstract1 % 84001) :default)))
        ty (-> (e/forall' "m" mapKLK (e/forall' "x" fK mapKLK :default) :default)
               (#(e/forall' "dec" deceqK (e/abstract1 % 84003) :default)) (#(e/forall' "K" type0 (e/abstract1 % 84001) :default)))]
    (kenv/mk-def (nm "Map.gbStepId") [] ty val :hints :opaque)))

;; Map.lookup_insert
(defn- prove-map-lookup-insert []
  (let [fK (e/fvar 82001) fV (e/fvar 82002) fd (e/fvar 82003) fk (e/fvar 82004) fk' (e/fvar 82005) fv2 (e/fvar 82006) fm (e/fvar 82007)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        prodKV (e/app* (e/const' (nm "Prod") [z z]) fK fV)
        ndk (e/app* (e/const' (nm "Map.NodupKeys") [z z]) fK fV)
        mapKV (e/app* (e/const' (nm "Map") [z z]) fK fV)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        optV (e/app (e/const' (nm "Option") [z]) fV)
        beq (fn [x y] (e/app* (e/const' (nm "BEq.beq") [z]) fK beqI x y))
        mlook (fn [mm] (e/app* (e/const' (nm "Map.lookup") []) fK fV fd fk mm))
        lhs (mlook (e/app* (e/const' (nm "Map.insert") []) fK fV fd fk' fv2 fm))
        rhs (e/app* (e/const' (nm "cond") [L1]) optV (beq fk fk') (e/app* (e/const' (nm "Option.some") [z]) fV fv2) (mlook fm))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) optV lhs rhs)
                 (#(e/forall' "m" mapKV (e/abstract1 % 82007) :default)) (#(e/forall' "v" fV (e/abstract1 % 82006) :default))
                 (#(e/forall' "k'" fK (e/abstract1 % 82005) :default)) (#(e/forall' "k" fK (e/abstract1 % 82004) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 82003) :default)) (#(e/forall' "V" type0 (e/abstract1 % 82002) :default)) (#(e/forall' "K" type0 (e/abstract1 % 82001) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "dec" "k" "k'" "v" "m"])
        vm (e/app* (e/const' (nm "Subtype.val") [L1]) (e/app (e/const' (nm "List") [z]) (e/app* (e/const' (nm "Prod") [z z]) (gf ps "K") (gf ps "V"))) (e/app* (e/const' (nm "Map.NodupKeys") [z z]) (gf ps "K") (gf ps "V")) (gf ps "m"))
        li-app (e/app* (e/const' (nm "List.lookup_insert") []) (gf ps "K") (gf ps "V") (gf ps "dec") (gf ps "k") (gf ps "k'") (gf ps "v") vm)
        ps (basic/exact ps li-app)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.isSome_lookup_insert
(defn- prove-issome-lookup-insert []
  (let [fK (e/fvar 82001) fV (e/fvar 82002) fd (e/fvar 82003) fk (e/fvar 82004) fk' (e/fvar 82005) fv2 (e/fvar 82006) fm (e/fvar 82007)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        mapKV (e/app* (e/const' (nm "Map") [z z]) fK fV)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        beq (fn [x y] (e/app* (e/const' (nm "BEq.beq") [z]) fK beqI x y))
        isS (fn [o] (e/app* (e/const' (nm "Option.isSome") [z]) fV o))
        mlook (fn [mm] (e/app* (e/const' (nm "Map.lookup") []) fK fV fd fk mm))
        lhs (isS (mlook (e/app* (e/const' (nm "Map.insert") []) fK fV fd fk' fv2 fm)))
        rhs (e/app* (e/const' (nm "Bool.or") []) (beq fk fk') (isS (mlook fm)))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") []) lhs rhs)
                 (#(e/forall' "m" mapKV (e/abstract1 % 82007) :default)) (#(e/forall' "v" fV (e/abstract1 % 82006) :default))
                 (#(e/forall' "k'" fK (e/abstract1 % 82005) :default)) (#(e/forall' "k" fK (e/abstract1 % 82004) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 82003) :default)) (#(e/forall' "V" type0 (e/abstract1 % 82002) :default)) (#(e/forall' "K" type0 (e/abstract1 % 82001) :default)))
        beqg2 (fn [ps x y] (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) x y))
        LEM ['cond 'cond_true 'cond_false 'Option.isSome 'Bool.true_or 'Bool.false_or 'Bool.or_true 'Bool.or_false]
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "dec" "k" "k'" "v" "m"])
        mli (e/app* (e/const' (nm "Map.lookup_insert") []) (gf ps "K") (gf ps "V") (gf ps "dec") (gf ps "k") (gf ps "k'") (gf ps "v") (gf ps "m"))
        ps (basic/rewrite ps mli)
        br (basic/by-cases ps (beqg2 ps (gf ps "k") (gf ps "k'")))
        ps (reduce (fn [ps bid] (let [psb (focus ps bid)
                                      q (try (basic/rewrite psb (e/fvar (fv psb "hc"))) (catch Throwable _ psb))
                                      q (try (simp/simp-all q LEM) (catch Throwable _ q))]
                                  (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))
                   br (new-goals (:goals ps) (:goals br)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.lookup_group_by_gen — the foldl-of-inserts invariant (generalized over the accumulator)
(defn- prove-gen []
  (let [fK (e/fvar 85001) fd (e/fvar 85003) fk (e/fvar 85004) fxs (e/fvar 85005) fm (e/fvar 85007)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        listK (e/app (e/const' (nm "List") [z]) fK)
        mapKLK (e/app* (e/const' (nm "Map") [z z]) fK listK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        mlook (fn [mm] (e/app* (e/const' (nm "Map.lookup") []) fK listK fd fk mm))
        isS (fn [o] (e/app* (e/const' (nm "Option.isSome") [z]) listK o))
        gbStep (e/app* (e/const' (nm "Map.gbStepId") []) fK fd)
        foldl-step (fn [mm l] (e/app* (e/const' (nm "List.foldl") [z z]) mapKLK fK gbStep mm l))
        elemk (fn [l] (e/app* (e/const' (nm "List.elem") [z]) fK beqI fk l))
        body (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") [])
                     (isS (mlook (foldl-step fm fxs)))
                     (e/app* (e/const' (nm "Bool.or") []) (elemk fxs) (isS (mlook fm))))
        goal (-> body
                 (#(e/forall' "m" mapKLK (e/abstract1 % 85007) :default)) (#(e/forall' "xs" listK (e/abstract1 % 85005) :default))
                 (#(e/forall' "k" fK (e/abstract1 % 85004) :default)) (#(e/forall' "dec" deceqK (e/abstract1 % 85003) :default)) (#(e/forall' "K" type0 (e/abstract1 % 85001) :default)))
        gbStep-p (fn [ps] (e/app* (e/const' (nm "Map.gbStepId") []) (gf ps "K") (gf ps "dec")))
        beqg2 (fn [ps x y] (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) x y))
        LEM ['List.foldl_nil 'List.foldl_cons 'List.elem_nil 'List.elem_cons 'Bool.false_or 'Bool.or_false 'Bool.or_assoc 'Bool.or_comm]
        isli-app (fn [ps yfv mfv]
                   (let [gK (gf ps "K") gd (gf ps "dec") lK (e/app (e/const' (nm "List") [z]) gK)
                         bucket (e/app* (e/const' (nm "List.cons") [z]) gK yfv (e/app* (e/const' (nm "Option.getD") [z]) lK (e/app* (e/const' (nm "Map.lookup") []) gK lK gd yfv mfv) (e/app (e/const' (nm "List.nil") [z]) gK)))]
                     (e/app* (e/const' (nm "Map.isSome_lookup_insert") []) gK lK gd (gf ps "k") yfv bucket mfv)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "dec" "k" "xs"])
        ps (basic/induction ps (fvid ps "xs"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))]
                (if cons?
                  (let [psg (basic/intros psg ["m"])
                        hd (gf psg "head") mm (gf psg "m")
                        ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                        q (try (simp/simp psg ['List.foldl_cons]) (catch Throwable _ psg))
                        ih-at (e/app (e/fvar ihid) (e/app* (gbStep-p psg) mm hd))
                        q (try (basic/rewrite q ih-at) (catch Throwable _ q))
                        q (try (basic/unfold-in-goal q "Map.gbStepId") (catch Throwable _ q))
                        q (try (basic/rewrite q (isli-app q hd mm)) (catch Throwable _ q))
                        elemtail (e/app* (e/const' (nm "List.elem") [z]) (gf q "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf q "K") (gf q "dec")) (gf q "k") (gf q "tail"))
                        close-leaf (fn [qq] (let [hc (fvid qq "hc")
                                                  r (if hc (try (basic/rewrite qq (e/fvar hc)) (catch Throwable _ qq)) qq)
                                                  r (try (simp/simp-all r LEM) (catch Throwable _ r))]
                                              (if (proof/solved? r) r (try (basic/rfl r) (catch Throwable _ r)))))
                        brB (basic/by-cases q (beqg2 q (gf q "k") hd))
                        bidsB (new-goals (:goals q) (:goals brB))]
                    (reduce (fn [qq bidB]
                              (let [qb (focus qq bidB)
                                    hcB (fvid qb "hc")
                                    qb (try (basic/rewrite qb (e/fvar hcB)) (catch Throwable _ qb))
                                    qb (try (simp/simp-all qb LEM) (catch Throwable _ qb))]
                                (if (proof/solved? qb) qb
                                    (let [brA (basic/by-cases qb elemtail) aids (new-goals (:goals qb) (:goals brA))]
                                      (reduce (fn [q2 bidA] (close-leaf (focus q2 bidA))) brA aids)))))
                            brB bidsB))
                  (let [psg (basic/intros psg ["m"])
                        q (try (simp/simp-all psg LEM) (catch Throwable _ psg))]
                    (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.lookup_group_by (foldl form); the same proof inhabits the group_by goal by def-eq
(defn- prove-foldl-final []
  (let [fK (e/fvar 85001) fd (e/fvar 85003) fk (e/fvar 85004) fxs (e/fvar 85005)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        listK (e/app (e/const' (nm "List") [z]) fK)
        mapKLK (e/app* (e/const' (nm "Map") [z z]) fK listK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        gbStep (e/app* (e/const' (nm "Map.gbStepId") []) fK fd)
        empt0 (e/app* (e/const' (nm "Map.empty") []) fK listK)
        foldl0 (e/app* (e/const' (nm "List.foldl") [z z]) mapKLK fK gbStep empt0 fxs)
        body (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") [])
                     (e/app* (e/const' (nm "Option.isSome") [z]) listK (e/app* (e/const' (nm "Map.lookup") []) fK listK fd fk foldl0))
                     (e/app* (e/const' (nm "List.elem") [z]) fK beqI fk fxs))
        goal (-> body
                 (#(e/forall' "xs" listK (e/abstract1 % 85005) :default)) (#(e/forall' "k" fK (e/abstract1 % 85004) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 85003) :default)) (#(e/forall' "K" type0 (e/abstract1 % 85001) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "dec" "k" "xs"])
        empt (e/app* (e/const' (nm "Map.empty") []) (gf ps "K") (e/app (e/const' (nm "List") [z]) (gf ps "K")))
        gen-app (e/app* (e/const' (nm "Map.lookup_group_by_gen") []) (gf ps "K") (gf ps "dec") (gf ps "k") (gf ps "xs") empt)
        ps (basic/rewrite ps gen-app)
        elemkxs (e/app* (e/const' (nm "List.elem") [z]) (gf ps "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) (gf ps "k") (gf ps "xs"))
        ps (basic/exact ps (e/app* (e/const' (nm "Bool.or_false") []) elemkxs))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn- group-by-goal []
  (let [fK (e/fvar 85001) fd (e/fvar 85003) fk (e/fvar 85004) fxs (e/fvar 85005)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        listK (e/app (e/const' (nm "List") [z]) fK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        gbid (e/app* (e/const' (nm "Map.group_by") []) fK fK fd (e/lam "x" fK (e/bvar 0) :default) fxs)
        body (e/app* (e/const' (nm "Eq") [L1]) (e/const' (nm "Bool") [])
                     (e/app* (e/const' (nm "Option.isSome") [z]) listK (e/app* (e/const' (nm "Map.lookup") []) fK listK fd fk gbid))
                     (e/app* (e/const' (nm "List.elem") [z]) fK beqI fk fxs))]
    (-> body
        (#(e/forall' "xs" listK (e/abstract1 % 85005) :default)) (#(e/forall' "k" fK (e/abstract1 % 85004) :default))
        (#(e/forall' "dec" deceqK (e/abstract1 % 85003) :default)) (#(e/forall' "K" type0 (e/abstract1 % 85001) :default)))))

;; ══ SEMIJOIN / ANTI-JOIN (member→index probe) ════════════════════════════════
(defn- prove-semijoin []
  (let [fK (e/fvar 87001) fd (e/fvar 87003) fxs (e/fvar 87005) fys (e/fvar 87007)
        listK (e/app (e/const' (nm "List") [z]) fK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        idf (e/lam "x" fK (e/bvar 0) :default)
        gbys (e/app* (e/const' (nm "Map.group_by") []) fK fK fd idf fys)
        pf (e/lam "x" fK (e/app* (e/const' (nm "List.elem") [z]) fK beqI (e/bvar 0) fys) :default)
        qf (e/lam "x" fK (e/app* (e/const' (nm "Option.isSome") [z]) listK
                                 (e/app* (e/const' (nm "Map.lookup") []) fK listK fd (e/bvar 0) gbys)) :default)
        filt (fn [f l] (e/app* (e/const' (nm "List.filter") [z]) fK f l))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listK (filt pf fxs) (filt qf fxs))
                 (#(e/forall' "ys" listK (e/abstract1 % 87007) :default))
                 (#(e/forall' "xs" listK (e/abstract1 % 87005) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 87003) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 87001) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "dec" "xs" "ys"])
        gK (gf ps "K") gd (gf ps "dec") gxs (gf ps "xs") gys (gf ps "ys")
        glistK (e/app (e/const' (nm "List") [z]) gK)
        gbeqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) gK gd)
        gp (e/lam "x" gK (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 0) gys) :default)
        ggbys (e/app* (e/const' (nm "Map.group_by") []) gK gK gd (e/lam "x" gK (e/bvar 0) :default) gys)
        gq (e/lam "x" gK (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                                 (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 0) ggbys)) :default)
        memty (e/app* (e/const' (nm "Membership.mem") [z z]) gK glistK
                      (e/app (e/const' (nm "List.instMembership") [z]) gK) gxs (e/bvar 0))
        isS-x (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                      (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 1) ggbys))
        elem-x (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 1) gys)
        lgb (e/app* (e/const' (nm "Map.lookup_group_by") []) gK gd (e/bvar 1) gys)
        hterm (e/lam "x" gK (e/lam "hx" memty
                                   (e/app* (e/const' (nm "Eq.symm") [L1]) (e/const' (nm "Bool") []) isS-x elem-x lgb) :default) :default)
        pf-term (e/app* (e/const' (nm "List.filter_congr") [z]) gK gp gq gxs hterm)
        ps (basic/exact ps pf-term)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn- prove-anti-join []
  (let [fK (e/fvar 87001) fd (e/fvar 87003) fxs (e/fvar 87005) fys (e/fvar 87007)
        listK (e/app (e/const' (nm "List") [z]) fK)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        gbys (e/app* (e/const' (nm "Map.group_by") []) fK fK fd (e/lam "x" fK (e/bvar 0) :default) fys)
        notb (fn [b] (e/app (e/const' (nm "Bool.not") []) b))
        pf (e/lam "x" fK (notb (e/app* (e/const' (nm "List.elem") [z]) fK beqI (e/bvar 0) fys)) :default)
        qf (e/lam "x" fK (notb (e/app* (e/const' (nm "Option.isSome") [z]) listK
                                       (e/app* (e/const' (nm "Map.lookup") []) fK listK fd (e/bvar 0) gbys))) :default)
        filt (fn [f l] (e/app* (e/const' (nm "List.filter") [z]) fK f l))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listK (filt pf fxs) (filt qf fxs))
                 (#(e/forall' "ys" listK (e/abstract1 % 87007) :default))
                 (#(e/forall' "xs" listK (e/abstract1 % 87005) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 87003) :default))
                 (#(e/forall' "K" type0 (e/abstract1 % 87001) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "dec" "xs" "ys"])
        gK (gf ps "K") gd (gf ps "dec") gxs (gf ps "xs") gys (gf ps "ys")
        glistK (e/app (e/const' (nm "List") [z]) gK)
        gbeqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) gK gd)
        ggbys (e/app* (e/const' (nm "Map.group_by") []) gK gK gd (e/lam "x" gK (e/bvar 0) :default) gys)
        gp (e/lam "x" gK (notb (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 0) gys)) :default)
        gq (e/lam "x" gK (notb (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                                       (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 0) ggbys))) :default)
        memty (e/app* (e/const' (nm "Membership.mem") [z z]) gK glistK
                      (e/app (e/const' (nm "List.instMembership") [z]) gK) gxs (e/bvar 0))
        isS-x (e/app* (e/const' (nm "Option.isSome") [z]) glistK
                      (e/app* (e/const' (nm "Map.lookup") []) gK glistK gd (e/bvar 1) ggbys))
        elem-x (e/app* (e/const' (nm "List.elem") [z]) gK gbeqI (e/bvar 1) gys)
        lgb (e/app* (e/const' (nm "Map.lookup_group_by") []) gK gd (e/bvar 1) gys)
        sym (e/app* (e/const' (nm "Eq.symm") [L1]) (e/const' (nm "Bool") []) isS-x elem-x lgb)
        ca (e/app* (e/const' (nm "congrArg") [L1 L1]) (e/const' (nm "Bool") []) (e/const' (nm "Bool") [])
                   elem-x isS-x (e/const' (nm "Bool.not") []) sym)
        hterm (e/lam "x" gK (e/lam "hx" memty ca :default) :default)
        pf-term (e/app* (e/const' (nm "List.filter_congr") [z]) gK gp gq gxs hterm)
        ps (basic/exact ps pf-term)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── installer ────────────────────────────────────────────────────────────────
(def ^:private cache (atom nil))   ; ordered ConstantInfos — Init-only, env-independent

;; ══ AGGREGATION-THROUGH-JOIN factorization (general — count/sum/max all instances) ═══════════════
;; foldl op e (Map.join kf lf xs ys) = foldl (λacc x. foldl (λacc' y. op acc' (x,y)) acc (bucket x)) e xs
;; — aggregate each x's matching ys BEFORE the cross product, NEVER materialize the |xs|·|ys| pairs.
;; Needs NO monoid axioms (the accumulator just threads): unfold Map.join, then List.foldl_flatMap +
;; List.foldl_map. count (op = λacc _. succ acc) and sum (op = λacc p. acc + w (snd p)) are instances.
(defn- prove-foldl-join-factor []
  (let [K (e/fvar 93001) X (e/fvar 93002) Y (e/fvar 93003) S (e/fvar 93004) dec (e/fvar 93005)
        op (e/fvar 93006) ini (e/fvar 93007) kf (e/fvar 93008) lf (e/fvar 93009) xs (e/fvar 93010) ys (e/fvar 93011)
        listX (e/app (e/const' (nm "List") [z]) X) listY (e/app (e/const' (nm "List") [z]) Y)
        PXY (e/app* (e/const' (nm "Prod") [z z]) X Y)
        deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
        xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
        opTy (e/forall' "_" S (e/forall' "_" PXY S :default) :default)
        join (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys)
        lhs (e/app* (e/const' (nm "List.foldl") [z z]) S PXY op ini join)
        bucket (fn [k'] (e/app* (e/const' (nm "Option.getD") [z]) listY
                                (e/app* (e/const' (nm "Map.lookup") []) K listY dec k'
                                        (e/app* (e/const' (nm "Map.group_by") []) K Y dec lf ys))
                                (e/app (e/const' (nm "List.nil") [z]) Y)))
        innerStep (e/lam "acc'" S (e/lam "y" Y
                    (e/app* op (e/bvar 1) (e/app* (e/const' (nm "Prod.mk") [z z]) X Y (e/bvar 2) (e/bvar 0))) :default) :default)
        outerStep (e/lam "acc" S (e/lam "x" X
                    (e/app* (e/const' (nm "List.foldl") [z z]) S Y innerStep (e/bvar 1)
                            (bucket (e/app kf (e/bvar 0)))) :default) :default)
        rhs (e/app* (e/const' (nm "List.foldl") [z z]) S X outerStep ini xs)
        eqn (e/app* (e/const' (nm "Eq") [L1]) S lhs rhs)
        wrap (fn [t] (-> t (#(e/forall' "ys" listY (e/abstract1 % 93011) :default)) (#(e/forall' "xs" listX (e/abstract1 % 93010) :default))
                         (#(e/forall' "lf" yToK (e/abstract1 % 93009) :default)) (#(e/forall' "kf" xToK (e/abstract1 % 93008) :default))
                         (#(e/forall' "e" S (e/abstract1 % 93007) :default)) (#(e/forall' "op" opTy (e/abstract1 % 93006) :default))
                         (#(e/forall' "dec" deceqK (e/abstract1 % 93005) :default)) (#(e/forall' "S" type0 (e/abstract1 % 93004) :default))
                         (#(e/forall' "Y" type0 (e/abstract1 % 93003) :default)) (#(e/forall' "X" type0 (e/abstract1 % 93002) :default))
                         (#(e/forall' "K" type0 (e/abstract1 % 93001) :default))))
        goal (wrap eqn)
        ps0 (basic/intros (first (proof/start-proof (a/env) goal)) ["K" "X" "Y" "S" "dec" "op" "e" "kf" "lf" "xs" "ys"])
        hv (fn [n] (gf ps0 n))
        ps1 (basic/rewrite ps0 (e/app* (e/const' (nm "Map.join.eq_unfold") [])
                                       (hv "K") (hv "X") (hv "Y") (hv "dec") (hv "kf") (hv "lf") (hv "xs") (hv "ys")))
        ps (simp/simp-all ps1 ['List.foldl_flatMap 'List.foldl_map])]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── COUNT factorization (Map.count_join_factor) — ported from count_factor_test so the
;; optimizer path try-count-factor has its law INSTALLED (it was test-only: a coherence bug).
(def ^:private cf-z lvl/zero)
(def ^:private cf-L1 (lvl/succ cf-z))
(def ^:private cf-type0 (e/sort' cf-L1))

(defn- cf-jvars []
  (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4)
        kf (e/fvar 5) lf (e/fvar 6) xs (e/fvar 7) ys (e/fvar 8)]
    {:K K :X X :Y Y :dec dec :kf kf :lf lf :xs xs :ys ys
     :PXY (e/app* (e/const' (nm "Prod") [cf-z cf-z]) X Y)
     :listX (e/app (e/const' (nm "List") [cf-z]) X)
     :listY (e/app (e/const' (nm "List") [cf-z]) Y)
     :deceqK (e/app (e/const' (nm "DecidableEq") [cf-L1]) K)
     :xToK (e/forall' "_" X K :default) :yToK (e/forall' "_" Y K :default)}))

(defn- prove-count-join-factor
  "Prove Map.count_join_factor on the Map.join form (length of the join = sum of per-key
   bucket lengths — count WITHOUT materializing the product). Returns [goal proof]."
  []
  (let [{:keys [K X Y dec kf lf xs ys PXY listX listY deceqK xToK yToK]} (cf-jvars)
        NatT (e/const' (nm "Nat") [])
        lhs (e/app* (e/const' (nm "List.length") [cf-z]) PXY
                    (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys))
        bucket (fn [k'] (e/app* (e/const' (nm "Option.getD") [cf-z]) listY
                                (e/app* (e/const' (nm "Map.lookup") []) K listY dec k'
                                        (e/app* (e/const' (nm "Map.group_by") []) K Y dec lf ys))
                                (e/app (e/const' (nm "List.nil") [cf-z]) Y)))
        lenFn (e/lam "x" X (e/app* (e/const' (nm "List.length") [cf-z]) Y (bucket (e/app kf (e/bvar 0)))) :default)
        mapped (e/app* (e/const' (nm "List.map") [cf-z cf-z]) X NatT lenFn xs)
        zeroNat (e/app* (e/const' (nm "Zero.ofOfNat0") [cf-z]) NatT
                        (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 0)))
        rhs (e/app* (e/const' (nm "List.sum") [cf-z]) NatT (e/const' (nm "instAddNat") []) zeroNat mapped)
        eqn (e/app* (e/const' (nm "Eq") [cf-L1]) NatT lhs rhs)
        wrap (fn [t]
               (-> t (#(e/forall' "ys" listY (e/abstract1 % 8) :default))
                   (#(e/forall' "xs" listX (e/abstract1 % 7) :default))
                   (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                   (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                   (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                   (#(e/forall' "Y" cf-type0 (e/abstract1 % 3) :default))
                   (#(e/forall' "X" cf-type0 (e/abstract1 % 2) :default))
                   (#(e/forall' "K" cf-type0 (e/abstract1 % 1) :default))))
        goal (wrap eqn)
        ps0 (basic/intros (first (proof/start-proof (a/env) goal)) ["K" "X" "Y" "dec" "kf" "lf" "xs" "ys"])
        fvid (fn [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
        hv (fn [n] (e/fvar (fvid ps0 n)))
        ps1 (basic/rewrite ps0 (e/app* (e/const' (nm "Map.join.eq_unfold") [])
                                       (hv "K") (hv "X") (hv "Y") (hv "dec")
                                       (hv "kf") (hv "lf") (hv "xs") (hv "ys")))
        ps (simp/simp-all ps1 ['List.length_flatMap 'List.length_map])]
    (when-not (proof/solved? ps)
      (throw (ex-info "Map.count_join_factor proof did not close" {})))
    [goal (extract/extract ps)]))

(defn- build-all
  "Build + admit ALL relational laws in dependency order (each proof references earlier laws), and
   cache the ConstantInfos. Each is independently check-constant'd (kernel-verified) as it lands.
   Requires kmap/install!. Returns the ordered CIs."
  []
  (or @cache
      (binding [a/*verbose* false
                ;; intermediates admitted inside rp/ proofs land in the SAME ordered cache,
                ;; so replay carries the full dependency closure (strict re-check works)
                rp/*admit-sink* (atom nil)]
        (let [acc (atom [])
              _ (set! rp/*admit-sink* acc)
              admit! (fn [ci] (swap! a/ansatz-env kenv/check-constant ci) (swap! acc conj ci))
              thm! (fn [name [goal proof]] (admit! (kenv/mk-thm (nm name) [] goal proof)))]
          ;; lookup / group_by foundation
          (thm! "List.lookup_filter_ne" (prove-lookup-filter-ne))
          (thm! "List.lookup_insert"    (prove-lookup-insert))
          (admit! (gbstepid-ci))
          (thm! "Map.lookup_insert"        (prove-map-lookup-insert))
          (thm! "Map.isSome_lookup_insert" (prove-issome-lookup-insert))
          (thm! "Map.lookup_group_by_gen"  (prove-gen))
          (admit! (kenv/mk-thm (nm "Map.lookup_group_by") [] (group-by-goal) (second (prove-foldl-final))))
          ;; filter→join pushdown (B, A, C)
          (thm! "List.filter_map_pair_eq_cond" (prove-B))
          (thm! "List.filter_flatMap_cond"     (prove-A))
          (thm! "Map.filter_join_pushdown"     (compose-C))
          ;; semijoin / anti-join (member→index probe)
          (thm! "List.elem_filter_eq_index_probe"     (prove-semijoin))
          (thm! "List.elem_not_filter_eq_index_probe" (prove-anti-join))
          ;; aggregation-through-join factorization (general; needs the Map.join unfold equation)
          (admit! ((requiring-resolve 'wandler.optimize/unfold-eqn-ci) (a/env) "Map.join"))
          (thm! "Map.foldl_join_factor" (prove-foldl-join-factor))
          (thm! "Map.count_join_factor" (prove-count-join-factor))
          ;; JOIN COMMUTATIVITY chain (perm → bucket → join_comm → Perm→Eq count bridge), the
          ;; drive-direction reorder: try-join-reorder consumes Map.join_length_comm. From the clean
          ;; src home ansatz.relational.proofs. prove-join-comm admits its intermediates (pushout/qeq/
          ;; claimC/msEq2/mapswap) as side effects — needed at its check-constant, inert on replay.
          (thm! "List.flatMap_const_nil"           (rp/prove-flatMap-const-nil))
          (thm! "List.flatMap_congr_perm"          (rp/prove-flatMap-congr-perm))
          (thm! "List.flatMap_append_distrib_perm" (rp/prove-flatMap-append-distrib))
          (thm! "List.flatMap_cons_distrib_perm"   (rp/prove-flatMap-cons-distrib))
          (thm! "List.flatMap_map_comm"            (rp/prove-flatMap-map-comm))
          (thm! "List.foldl_cons_perm"             (rp/prove-foldflip-perm))
          (thm! "Map.bucket_content_gen"           (rp/prove-bucket-gen))
          (thm! "Map.bucket_content"               (rp/prove-bucket-final))
          (thm! "BEq.beq_comm"                     (rp/prove-beq-comm))
          (thm! "Map.bucket_perm"                  (rp/prove-bucket-perm))
          (thm! "Map.join_filtered_product"        (rp/prove-claim-a))
          (thm! "Map.join_comm"                    (rp/prove-join-comm))
          (thm! "Map.join_length_comm"             (rp/prove-join-length-comm))
          ;; GRACE-HASH partition lemma: the join's build side distributes over append (filter form),
          ;; so it can be processed in budget-sized BLOCKS — the certified core of the spill strategy.
          (thm! "Map.join_filter_append_perm"      (rp/prove-join-filter-append-perm))
          ;; consumer half: a left-commutative aggregate (sum/count) is invariant under the block
          ;; partition's permutation — Perm l1 l2 → foldl op e l1 = foldl op e l2 for lcomm op.
          (thm! "List.foldl_perm_lcomm"            (rp/prove-foldl-perm-lcomm))
          ;; GRACE-HASH certified algebra: Map.join distributes over the build side as a permutation,
          ;; so the join can be evaluated in budget-sized BLOCKS (O(budget) peak memory). The surface
          ;; law Map.foldl_join_blockfold is what the optimizer applies.
          (thm! "Map.join_filter_form_perm"        (rp/prove-join-filter-form-perm))
          (thm! "Map.join_append_perm"             (rp/prove-join-append-perm))
          (thm! "Map.join_nil_right"               (rp/prove-join-nil-right))
          (thm! "Map.join_blockfold_perm"          (rp/prove-join-blockfold-perm))
          (thm! "Map.foldl_join_blockfold"         (rp/prove-foldl-join-blockfold))
          ;; runtime carrier for the spill: block-partition the build side (codegen → partition-all),
          ;; with flatten (chunk B l) = l certifying it preserves the data.
          (admit! (rp/chunk-def-ci))
          (thm! "List.flatten_chunk_step" (rp/prove-flatten-chunk-step))
          (thm! "List.flatten_chunk"      (rp/prove-flatten-chunk))
          ;; pre-aggregated index (FAQ) foundation: init-extraction for additive folds (#77)
          (thm! "List.foldl_add_init_generic" (rpf/prove-foldl-add-init-generic))
          (thm! "List.foldl_add_init"     (rpf/prove-foldl-add-init))
          ;; the crux: probing a key/value-mapped assoc list = mapping the value-fn over the probe.
          (thm! "List.lookup_map_kv"      (rpf/prove-lookup-map-kv))
          ;; pointwise foldl congruence (lifts the per-bucket identity to the whole outer fold).
          (thm! "List.foldl_congr"        (rpf/prove-foldl-congr))
          ;; THE pre-aggregated (FAQ) join index for separable SUM aggregates — O(distinct keys).
          (thm! "Map.foldl_join_sum_factor_generic" (rpf/prove-foldl-join-sum-factor-generic))
          (thm! "Map.foldl_join_sum_factor" (rpf/prove-foldl-join-sum-factor))
          ;; element-polymorphic foldl-form const-factor pull (the FAQ frame rule needs it: a bucket is
          ;; List Y with weight g:Y→Nat, where the Nat-only sum_map_const_mul does not apply).
          ;; SEMIRING-GENERIC version first: the product-pull holds for ANY (S,+,·,0) with left-distrib
          ;; + right-annihilator (passed as hypotheses) — no Nat. The Nat law is its instantiation.
          (thm! "List.foldl_const_mul_pull_generic" (rpf/prove-foldl-const-mul-pull-generic))
          (thm! "List.foldl_const_mul_pull" (rpf/prove-foldl-const-mul-pull))
          ;; THE FAQ FRAME RULE: separable two-sided weight f(x)·g(y) over a join factorizes through the
          ;; SAME pre-aggregated index — Σ_{x⋈y} f(x)·g(y) = Σ_x f(x)·(Σ bucket g). Generalizes
          ;; foldl_join_sum_factor (its f≡1 instance); the SPN/FAQ product node over Map.join.
          (thm! "Map.foldl_join_frame_generic" (rpf/prove-foldl-join-frame-generic))
          (thm! "Map.foldl_join_frame"      (rpf/prove-foldl-join-frame))
          ;; CONDITIONAL SEPARATION (the dependent-types win): a separable conjunctive guard P(x)∧Q(y)
          ;; factors a weighted product — cond(a&&b)(u·v)0 = (cond a u 0)·(cond b v 0) — so once split
          ;; f'=[P]·f, g'=[Q]·g are closed and the frame rule fires.
          (thm! "Nat.cond_and_mul_split_generic" (rpf/prove-cond-and-mul-split-generic))
          (thm! "Nat.cond_and_mul_split"    (rpf/prove-cond-and-mul-split))
          ;; FD SCOPE QUOTIENT foundation: on a group_by bucket (= the keyed filter), every element has
          ;; lf y = k, so substituting the join key k for (lf y) is sound. A key-dependent build-side
          ;; factor can therefore float to whichever side is cheaper (e.g. into the per-key index).
          (thm! "Map.bucket_key_subst"      (rpf/prove-bucket-key-subst))
          ;; FD factor-pull: a key-dependent build-side factor w(lf y) is constant on the bucket, so it
          ;; pulls OUT of the per-bucket sum (computed once per key). The certificate for floating a
          ;; key-factor into the per-key pre-aggregated index. Assembly: bucket_key_subst ∘ foldl_map ∘
          ;; foldl_const_mul_pull.
          (thm! "Map.bucket_factor_pull_generic" (rpf/prove-bucket-factor-pull-generic))
          (thm! "Map.bucket_factor_pull"    (rpf/prove-bucket-factor-pull))
          ;; FD float-into-index: a key-factor w(kf x) multiplying a per-key index lookup can be BAKED
          ;; into the index (each entry reweighted by w of its key), since the lookup key is k so
          ;; w(fst entry)=w(k). Lets the optimizer float a key-factor off the per-row x-side into the
          ;; O(distinct-keys) index — the Phase-5 cost win when ndv ≪ |xs|.
          (thm! "List.lookup_reweight_generic" (rpf/prove-lookup-reweight-generic))
          (thm! "List.lookup_reweight"      (rpf/prove-lookup-reweight))
          ;; the optimizer-facing float law: a key-factor w(kf x) over a per-key index lookup floats INTO
          ;; the index, over an ARBITRARY index — composes directly with the frame's output (idx := the
          ;; pre-aggregated index). foldl_congr ∘ lookup_reweight.
          (thm! "Map.foldl_keyfactor_float_generic" (rpf/prove-keyfactor-float-generic))
          (thm! "Map.foldl_keyfactor_float" (rpf/prove-keyfactor-float))
          ;; loop-invariant distributive law (1-variable elimination): a multiplicative x-free factor
          ;; distributes out of the sum — the certificate for hoisting an invariant fold out of a map.
          (thm! "List.sum_map_mul_const"  (rpf/prove-sum-map-mul-const))
          ;; left-invariant mirror (c * f x): the optimizer matches both multiplication orders.
          (thm! "List.sum_map_const_mul"  (rpf/prove-sum-map-const-mul))
          ;; sum-semiring LINEARITY: the additive structure for FAQ elimination (∑ distributes over +,
          ;; ∑ of zeros = 0, fold init extracts). The e-graph composes these for sum-product rewriting.
          (thm! "List.sum_map_add_distrib" (rpf/prove-sum-map-add-distrib))
          (thm! "List.sum_map_zero"        (rpf/prove-sum-map-zero))
          (thm! "List.foldl_add_pull"      (rpf/prove-foldl-add-pull))
          (reset! cache @acc)))))

(defn install!
  "Admit the proven relational laws into the global env (idempotent): the lookup/group_by
   foundation, the filter→join pushdown, and the semijoin / anti-join. After this the cost optimizer
   (optimize-cost / a/defn) auto-adopts them. Requires kmap/install!. The first call proves
   everything (~1s); later calls (after an env reset) replay the memoized, already-verified CIs."
  []
  (when-not (kenv/lookup (a/env) (nm "Map.join_length_comm"))
    (if @cache
      ;; replay through the same strict gate as the first build — the cache is
      ;; env-independent (Init-only proofs), but symmetry costs little and the
      ;; kernel re-check catches any drift
      (doseq [ci @cache] (swap! a/ansatz-env kenv/check-constant ci))
      (build-all)))
  ;; register the two Init carriers the frame index can certify (counting/SUM and boolean provenance) —
  ;; idempotent; each row's named consts are admitted by build-all above (Nat) / Init (Bool).
  (sreg/register! "Nat"  {:add "Nat.add" :mul "Nat.mul" :zero "Nat.zero"
                          :hAA "Nat.add_assoc" :hZA "Nat.zero_add" :hAZ "Nat.add_zero"
                          :hMA "Nat.mul_add" :hMZ "Nat.mul_zero" :hZM "Nat.zero_mul"})
  (sreg/register! "Bool" {:add "Bool.or" :mul "Bool.and" :zero "Bool.false"
                          :hAA "Bool.or_assoc" :hZA "Bool.false_or" :hAZ "Bool.or_false"
                          :hMA "Bool.and_or_distrib_left" :hMZ "Bool.and_false" :hZM "Bool.false_and"})
  (a/env))
