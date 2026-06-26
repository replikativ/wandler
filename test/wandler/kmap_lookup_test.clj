(ns wandler.kmap-lookup-test
  "Verified Map lookup foundation (generic over any DecidableEq key):
     List.lookup_filter_ne : k ≠ k' → lookup k (filter (·.fst ≠ k') l) = lookup k l
     List.lookup_insert     : lookup k ((k',v)::filter (·.fst ≠ k') l)
                                = cond (k==k') (some v) (lookup k l)
   These are the stepping stones to `Map.lookup_group_by` (and thence the relational
   semijoin / right-side filter pushdown). They exercise the LawfulBEq-from-
   DecidableEq instance and the simp instance-implicit-binding fix. Gated on Init."
  (:require [ansatz.core :as a]
            [wandler.kmap :as kmap]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ z))
(def ^:private type0 (e/sort' L1))
(defn- fv [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fv ps n)))
(defn- beqg [ps x y]
  (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K")
          (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) x y))
;; Authoritative check-constant (full kernel re-check), not lenient inferType.
(defn- checks? [term goal] (kenv/verifies? (a/env) goal term))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- new-goals [before after] (vec (remove (set before) after)))

;; ── List.lookup_filter_ne ──────────────────────────────────────────────────
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
        solve-all
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
        ps (solve-all ps)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── List.lookup_insert ─────────────────────────────────────────────────────
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

(deftest map-lookup-foundation
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (binding [a/*verbose* false]
        (let [[fg fp] (prove-lookup-filter-ne)]
          (is (some? fp) "lookup_filter_ne proved")
          (is (true? (checks? fp fg)) "lookup_filter_ne kernel-checks")
          (reset! a/ansatz-env (kenv/add-constant (a/env)
                                 (kenv/mk-thm (nm "List.lookup_filter_ne") [] fg fp))))
        (let [[ig ip] (prove-lookup-insert)]
          (is (some? ip) "lookup_insert proved")
          (is (true? (checks? ip ig)) "lookup_insert kernel-checks"))))
    (is true "SKIP map-lookup-foundation: no Init env")))
