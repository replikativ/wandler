(ns ansatz.aggregate-test
  "Verified SEMIRING-PARAMETERIZED group-by aggregation. The single invariant

     getD (lookup k (aggregate_by f g op e xs)) e
       = foldl op e (map g (filter (fun x => k == f x) xs))

   where  aggregate_by f g op e xs
            = foldl (fun m x => insert (f x) (op (getD (lookup (f x) m) e) (g x)) m) ∅ xs

   says: the one-pass fold-into-Map computes, for each key k, exactly the `op`/`e`
   reduction of the `g`-images of the elements with that key. Crucially it needs NO
   monoid axioms (foldl just threads `op`), so it instantiates to EVERY aggregate —
   count (ℕ,+,0,λ_.1), sum (ℕ,+,0,value), max/min (tropical), exists (Bool,∨,false,…),
   product, … — each inheriting the kernel proof (Green–Tannen provenance-semiring /
   FAQ style). Built on the verified Map foundation. Gated on Init."
  (:require [ansatz.core :as a]
            [ansatz.kmap :as kmap]
            [ansatz.kmap-lookup-test :as klt]
            [ansatz.kmap-group-by-test :as gbt]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.kernel.tc]
            [ansatz.tactic.extract :as extract]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- new-goals [before after] (vec (remove (set before) after)))
;; AUTHORITATIVE: full kernel check-constant, not the lenient TypeChecker.inferType.
(defn- checks? [term goal] (kenv/verifies? (a/env) goal term))
(defn- reg! [n g p] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) [] g p))))

(defn- register-foundation! []
  (binding [a/*verbose* false]
    (let [[g p] (#'klt/prove-lookup-filter-ne)] (reg! "List.lookup_filter_ne" g p))
    (let [[g p] (#'klt/prove-lookup-insert)] (reg! "List.lookup_insert" g p))
    (let [[g p] (#'gbt/prove-map-lookup-insert)] (reg! "Map.lookup_insert" g p))))

;; shared term builders over fixed construction fvars
(def ^:private fK (e/fvar 86001)) (def ^:private fV (e/fvar 86002)) (def ^:private fS (e/fvar 86003))
(def ^:private fd (e/fvar 86004)) (def ^:private ff (e/fvar 86005)) (def ^:private fg (e/fvar 86006))
(def ^:private fop (e/fvar 86007)) (def ^:private fe (e/fvar 86008)) (def ^:private fk (e/fvar 86009))
(def ^:private fxs (e/fvar 86010)) (def ^:private fm (e/fvar 86011))
(def ^:private beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd))
(def ^:private mapKS (e/app* (e/const' (nm "Map") [z z]) fK fS))
(def ^:private listV (e/app (e/const' (nm "List") [z]) fV))
(def ^:private deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK))
(def ^:private opty (e/forall' "_" fS (e/forall' "_" fS fS :default) :default))
(defn- mlook [key m] (e/app* (e/const' (nm "Map.lookup") []) fK fS fd key m))
(defn- getD [o] (e/app* (e/const' (nm "Option.getD") [z]) fS o fe))
(defn- beqg [a b] (e/app* (e/const' (nm "BEq.beq") [z]) fK beqI a b))
(def ^:private step
  (e/lam "m" mapKS (e/lam "x" fV
    (let [x (e/bvar 0) m (e/bvar 1) fx (e/app ff x)
          cur (getD (e/app* (e/const' (nm "Map.lookup") []) fK fS fd fx m))
          newv (e/app* fop cur (e/app fg x))]
      (e/app* (e/const' (nm "Map.insert") []) fK fS fd fx newv m)) :default) :default))
(defn- foldl-step [m l] (e/app* (e/const' (nm "List.foldl") [z z]) mapKS fV step m l))
(def ^:private filt-pred (e/lam "x" fV (beqg fk (e/app ff (e/bvar 0))) :default))
(defn- filt [l] (e/app* (e/const' (nm "List.filter") [z]) fV filt-pred l))
(defn- mapg [l] (e/app* (e/const' (nm "List.map") [z z]) fV fS fg l))
(defn- foldlop [acc l] (e/app* (e/const' (nm "List.foldl") [z z]) fS fS fop acc l))
(defn- close-params [body]
  (-> body
      (#(e/forall' "xs" listV (e/abstract1 % 86010) :default)) (#(e/forall' "k" fK (e/abstract1 % 86009) :default))
      (#(e/forall' "e" fS (e/abstract1 % 86008) :default)) (#(e/forall' "op" opty (e/abstract1 % 86007) :default))
      (#(e/forall' "g" (e/forall' "_" fV fS :default) (e/abstract1 % 86006) :default))
      (#(e/forall' "f" (e/forall' "_" fV fK :default) (e/abstract1 % 86005) :default))
      (#(e/forall' "dec" deceqK (e/abstract1 % 86004) :default)) (#(e/forall' "S" type0 (e/abstract1 % 86003) :default))
      (#(e/forall' "V" type0 (e/abstract1 % 86002) :default)) (#(e/forall' "K" type0 (e/abstract1 % 86001) :default))))

(def ^:private LEM ['List.foldl_nil 'List.foldl_cons 'List.filter_nil 'List.filter_cons_of_pos 'List.filter_cons_of_neg
                    'List.map_nil 'List.map_cons 'cond 'cond_true 'cond_false 'Option.getD 'Map.lookup_insert])
(defn- beqp [ps a b] (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) a b))

(defn- prove-agg-gen []
  (let [eqbody (e/app* (e/const' (nm "Eq") [L1]) fS
                       (getD (mlook fk (foldl-step fm fxs)))
                       (foldlop (getD (mlook fk fm)) (mapg (filt fxs))))
        ;; m is the INNERMOST binder (right inside ∀xs) so the ∀m motive survives induction
        gen-goal (close-params (e/forall' "m" mapKS (e/abstract1 eqbody 86011) :default))
        [ps _] (proof/start-proof (a/env) gen-goal)
        ps (basic/intros ps ["K" "V" "S" "dec" "f" "g" "op" "e" "k" "xs"])
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
                         gK (gf psg "K") gd (gf psg "dec") gS (gf psg "S")
                         gmapKS (e/app* (e/const' (nm "Map") [z z]) gK gS)
                         pstep (e/lam "m" gmapKS (e/lam "x" (gf psg "V")
                                 (let [x (e/bvar 0) m (e/bvar 1) fx (e/app (gf psg "f") x)
                                       cur (e/app* (e/const' (nm "Option.getD") [z]) gS (e/app* (e/const' (nm "Map.lookup") []) gK gS gd fx m) (gf psg "e"))
                                       newv (e/app* (gf psg "op") cur (e/app (gf psg "g") x))]
                                   (e/app* (e/const' (nm "Map.insert") []) gK gS gd fx newv m)) :default) :default)
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

(defn- prove-agg-final []
  ;; getD (lookup k (aggregate_by f g op e xs)) e = foldl op e (map g (filter (k==f·) xs))
  (let [empt (e/app* (e/const' (nm "Map.empty") []) fK fS)
        fin-goal (close-params (e/app* (e/const' (nm "Eq") [L1]) fS
                                       (getD (mlook fk (foldl-step empt fxs)))
                                       (foldlop fe (mapg (filt fxs)))))
        [ps _] (proof/start-proof (a/env) fin-goal)
        ps (basic/intros ps ["K" "V" "S" "dec" "f" "g" "op" "e" "k" "xs"])
        gempt (e/app* (e/const' (nm "Map.empty") []) (gf ps "K") (gf ps "S"))
        gen-app (e/app* (e/const' (nm "Map.getD_lookup_aggregate_gen") []) (gf ps "K") (gf ps "V") (gf ps "S")
                        (gf ps "dec") (gf ps "f") (gf ps "g") (gf ps "op") (gf ps "e") (gf ps "k") (gf ps "xs") gempt)
        ps (basic/exact ps gen-app)]
    [fin-goal (when (proof/solved? ps) (extract/extract ps))]))

;; Map.aggregate_by as a NAMED const (so the cost model can see the index build) and the
;; indexed-aggregate REWRITE law  foldl op e (map g (filter (k==f·) xs)) = getD (lookup k
;; (aggregate_by … xs)) e  — the per-key scan-aggregate equals an O(1) index probe (index
;; built once when aggregating over many keys), exactly paralleling the semijoin.
(defn- register-aggregate-by-const! []
  (let [agg-val (e/lam "xs" listV (e/app* (e/const' (nm "List.foldl") [z z]) mapKS fV step
                                          (e/app* (e/const' (nm "Map.empty") []) fK fS) (e/bvar 0)) :default)
        params [[86001 "K" type0] [86002 "V" type0] [86003 "S" type0] [86004 "dec" deceqK]
                [86005 "f" (e/forall' "_" fV fK :default)] [86006 "g" (e/forall' "_" fV fS :default)]
                [86007 "op" opty] [86008 "e" fS]]
        full-val (reduce (fn [acc [id nme ty]] (e/lam nme ty (e/abstract1 acc id) :default)) agg-val (reverse params))
        full-ty (reduce (fn [acc [id nme ty]] (e/forall' nme ty (e/abstract1 acc id) :default))
                        (e/forall' "xs" listV mapKS :default) (reverse params))]
    (reset! a/ansatz-env (kenv/check-constant (a/env) (kenv/mk-def (nm "Map.aggregate_by") [] full-ty full-val :hints :opaque)))))

(defn- prove-aggregate-indexed []
  (let [fk2 (e/fvar 86009) fxs2 (e/fvar 86010)
        fp (e/lam "x" fV (beqg fk2 (e/app ff (e/bvar 0))) :default)
        lhs (e/app* (e/const' (nm "List.foldl") [z z]) fS fS fop fe
                    (e/app* (e/const' (nm "List.map") [z z]) fV fS fg (e/app* (e/const' (nm "List.filter") [z]) fV fp fxs2)))
        getd-of (fn [agg] (e/app* (e/const' (nm "Option.getD") [z]) fS (e/app* (e/const' (nm "Map.lookup") []) fK fS fd fk2 agg) fe))
        pwrap (fn [b] (close-params b))
        aggc (e/app* (e/const' (nm "Map.aggregate_by") []) fK fV fS fd ff fg fop fe fxs2)
        inline-agg (e/app* (e/const' (nm "List.foldl") [z z]) mapKS fV step (e/app* (e/const' (nm "Map.empty") []) fK fS) fxs2)
        idx-goal   (pwrap (e/app* (e/const' (nm "Eq") [L1]) fS lhs (getd-of aggc)))
        idx-inline (pwrap (e/app* (e/const' (nm "Eq") [L1]) fS lhs (getd-of inline-agg)))
        [ps _] (proof/start-proof (a/env) idx-inline)
        ps (basic/intros ps ["K" "V" "S" "dec" "f" "g" "op" "e" "k" "xs"])
        fin (e/app* (e/const' (nm "Map.getD_lookup_aggregate") []) (gf ps "K") (gf ps "V") (gf ps "S") (gf ps "dec")
                    (gf ps "f") (gf ps "g") (gf ps "op") (gf ps "e") (gf ps "k") (gf ps "xs"))
        st (ansatz.kernel.tc/attach-lctx (ansatz.kernel.tc/mk-tc-state (a/env)) (:lctx (proof/current-goal ps)))
        [_ args] (e/get-app-fn-args (ansatz.kernel.tc/infer-type st fin))
        symm (e/app* (e/const' (nm "Eq.symm") [L1]) (gf ps "S") (nth args 1) (nth args 2) fin)
        ps (basic/exact ps symm)]
    ;; idx-goal (const form) is def-eq to the proved inline form — check-constant admits it
    [idx-goal (when (proof/solved? ps) (extract/extract ps))]))

;; an aggregate instance: pass concrete (S, g, op, e) to the final lemma; its type is the
;; specialized characterization — kernel-derived, no new proof.
(defn- instance-type [S g op e]
  (let [tc (doto (TypeChecker. (a/env)) (.setFuel 50000000))
        lctx {86001 {:name "K" :type type0} 86002 {:name "V" :type type0} 86004 {:name "dec" :type deceqK}
              86005 {:name "f" :type (e/forall' "_" fV fK :default)} 86009 {:name "k" :type fK} 86010 {:name "xs" :type listV}}
        _ (doseq [[id d] lctx] (.addLocal tc (long id) (str (:name d)) (:type d)))
        inst (e/app* (e/const' (nm "Map.getD_lookup_aggregate") []) fK fV S fd ff g op e fk fxs)]
    (try (.inferType tc inst) (catch Throwable _ nil))))

(deftest aggregate-by
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (register-foundation!)
      (let [[gg gp] (prove-agg-gen)]
        (is (some? gp) "aggregate_by invariant proved (the foldl invariant)")
        (is (true? (checks? gp gg)) "aggregate_by invariant kernel-checks")
        (reg! "Map.getD_lookup_aggregate_gen" gg gp))
      (let [[fg fp] (prove-agg-final)]
        (is (some? fp) "aggregate_by final (m=∅) proved")
        (is (true? (checks? fp fg)) "aggregate_by final kernel-checks")
        (reg! "Map.getD_lookup_aggregate" fg fp))
      ;; the named const + the indexed-aggregate rewrite (per-key scan = index probe)
      (register-aggregate-by-const!)
      (let [[ig ip] (prove-aggregate-indexed)]
        (is (some? ip) "aggregate_indexed (scan→probe) proved")
        (is (true? (let [tc (doto (TypeChecker. (a/env)) (.setFuel 50000000))]   ; const ≡ inline foldl, kernel def-eq
                     (.isDefEq tc (.inferType tc ip) ig)))
            "foldl op e (map g (filter (k==f·) xs)) = getD (lookup k (aggregate_by … xs)) e — kernel-checks"))
      ;; every aggregate is now a kernel-derived instance of the one lemma:
      (let [natT (e/const' (nm "Nat") [])
            one  (e/app* (e/const' (nm "OfNat.ofNat") [z]) natT (e/lit-nat 1) (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 1)))
            count-inst (instance-type natT (e/lam "_" fV one :default) (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []))
            exists-inst (instance-type (e/const' (nm "Bool") [])
                                       (e/lam "_" fV (e/const' (nm "Bool.true") []) :default)
                                       (e/const' (nm "Bool.or") []) (e/const' (nm "Bool.false") []))]
        (is (some? count-inst) "COUNT instance (ℕ,+,0,λ_.1) is kernel-derived")
        (is (some? exists-inst) "EXISTS instance (Bool,∨,false,λ_.true) is kernel-derived")))
    (is true "SKIP aggregate-by: no Init env")))
