(ns ansatz.kmap-group-by-test
  "Verified `Map.lookup_group_by` (membership over a group_by index):

     isSome (Map.lookup k (Map.group_by id xs)) = List.elem k xs

   the foundation for the relational SEMIJOIN / hash-join (a nested-loop membership
   filter rewrites to a built-once index probe). The hard piece is the foldl-of-
   inserts invariant `lookup_group_by_gen`, proved by generalizing over the
   accumulator. Builds on List.lookup_filter_ne / List.lookup_insert
   (ansatz.kmap-lookup-test), the LawfulBEq instance, and the simp instance-binding
   fix. Gated on Init."
  (:require [ansatz.core :as a]
            [ansatz.kmap :as kmap]
            [ansatz.kmap-lookup-test :as klt]
            [ansatz.test-env :as test-env]
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
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- new-goals [before after] (vec (remove (set before) after)))
;; Authoritative check-constant (full kernel re-check), not lenient inferType.
(defn- checks? [term goal] (kenv/verifies? (a/env) goal term))
(defn- register! [n levels goal proof] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) levels goal proof))))

;; ── register the prerequisites (proved in ansatz.kmap-lookup-test) ──
(defn- register-prereqs! []
  (let [[fg fp] (#'klt/prove-lookup-filter-ne)] (register! "List.lookup_filter_ne" [] fg fp))
  (let [[ig ip] (#'klt/prove-lookup-insert)]     (register! "List.lookup_insert" [] ig ip)))

;; ── gbStepId : ∀ K [dec], Map K (List K) → K → Map K (List K)  (group_by id's fold step)
(defn- register-gbstepid! []
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
    (reset! a/ansatz-env (kenv/check-constant (a/env) (kenv/mk-def (nm "Map.gbStepId") [] ty val :hints :opaque)))))

;; ── Map.lookup_insert : Map.lookup k (Map.insert k' v m) = cond (k==k') (some v) (Map.lookup k m)
(defn- prove-map-lookup-insert []
  (let [fK (e/fvar 82001) fV (e/fvar 82002) fd (e/fvar 82003) fk (e/fvar 82004) fk' (e/fvar 82005) fv2 (e/fvar 82006) fm (e/fvar 82007)
        beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd)
        prodKV (e/app* (e/const' (nm "Prod") [z z]) fK fV)
        listKV (e/app (e/const' (nm "List") [z]) prodKV)
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

;; ── Map.isSome_lookup_insert : isSome(lookup k (insert k' v m)) = (k==k') || isSome(lookup k m)
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
        beqg (fn [ps x y] (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) x y))
        LEM ['cond 'cond_true 'cond_false 'Option.isSome 'Bool.true_or 'Bool.false_or 'Bool.or_true 'Bool.or_false]
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "dec" "k" "k'" "v" "m"])
        mli (e/app* (e/const' (nm "Map.lookup_insert") []) (gf ps "K") (gf ps "V") (gf ps "dec") (gf ps "k") (gf ps "k'") (gf ps "v") (gf ps "m"))
        ps (basic/rewrite ps mli)
        br (basic/by-cases ps (beqg ps (gf ps "k") (gf ps "k'")))
        ps (reduce (fn [ps bid] (let [psb (focus ps bid)
                                      q (try (basic/rewrite psb (e/fvar (fvid psb "hc"))) (catch Throwable _ psb))
                                      q (try (simp/simp-all q LEM) (catch Throwable _ q))]
                                  (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))
                   br (new-goals (:goals ps) (:goals br)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; ── lookup_group_by_gen : ∀ m, isSome(lookup k (foldl gbStepId m xs)) = elem k xs || isSome(lookup k m)
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
        beqg (fn [ps x y] (e/app* (e/const' (nm "BEq.beq") [z]) (gf ps "K") (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) (gf ps "K") (gf ps "dec")) x y))
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
                         brB (basic/by-cases q (beqg q (gf q "k") hd))
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

;; ── lookup_group_by (foldl form) : isSome(lookup k (foldl gbStepId empty xs)) = elem k xs
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

;; ── group_by form (the usable result): isSome(lookup k (group_by id xs)) = elem k xs
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

(deftest map-lookup-group-by
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (binding [a/*verbose* false]
        (register-prereqs!)
        (register-gbstepid!)
        (let [[mg mp] (prove-map-lookup-insert)]
          (is (true? (checks? mp mg)) "Map.lookup_insert kernel-checks")
          (register! "Map.lookup_insert" [] mg mp))
        (let [[ig ip] (prove-issome-lookup-insert)]
          (is (true? (checks? ip ig)) "Map.isSome_lookup_insert kernel-checks")
          (register! "Map.isSome_lookup_insert" [] ig ip))
        (let [[gg gp] (prove-gen)]
          (is (some? gp) "lookup_group_by_gen proved (the foldl invariant)")
          (is (true? (checks? gp gg)) "lookup_group_by_gen kernel-checks")
          (register! "Map.lookup_group_by_gen" [] gg gp))
        (let [[fg fp] (prove-foldl-final)]
          (is (true? (checks? fp fg)) "lookup_group_by (foldl form) kernel-checks")
          ;; the same proof term inhabits the group_by form (def-eq); kernel re-checks it
          (let [gbg (group-by-goal)]
            (is (true? (checks? fp gbg))
                "isSome(lookup k (group_by id xs)) = elem k xs — kernel-checks")))))
    (is true "SKIP map-lookup-group-by: no Init env")))
