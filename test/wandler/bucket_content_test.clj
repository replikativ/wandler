(ns wandler.bucket-content-test
  "Verified BUCKET CONTENT of group_by — the full characterization (the membership
   lemma Map.lookup_group_by was the isSome shadow of this):

     getD (lookup k (Map.group_by f ys)) []  =  foldl (fun acc x => x :: acc) [] (filter (fun x => k == f x) ys)

   i.e. the bucket for key k is exactly the key-k elements of ys, accumulated by the
   group_by fold (a prepend, = reverse of the filtered sub-list). This is the right-side
   filter-pushdown's foundation: filter p (join xs ys) = join xs (filter p ys) reduces
   (via filter_flatMap + filter-map-snd) to a group_by-filter COMMUTATION, which rests on
   this bucket content. Same foldl-invariant template as the aggregation; gated on Init."
  (:require [ansatz.core :as a]
            [wandler.kmap :as kmap]
            [wandler.kmap-lookup-test :as klt]
            [wandler.kmap-group-by-test :as gbt]
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
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- new-goals [before after] (vec (remove (set before) after)))
;; Authoritative check: env/verifies? runs check-constant (the kernel's full re-check),
;; NOT the lenient TypeChecker.inferType (which assumes well-typed input). See
;; lenient-check-audit-findings: inferType silently accepted ill-typed proofs.
(defn- checks? [term goal] (kenv/verifies? (a/env) goal term))
(defn- reg! [n g p] (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm n) [] g p))))
(defn- register-foundation! []
  (binding [a/*verbose* false]
    (let [[g p] (#'klt/prove-lookup-filter-ne)] (reg! "List.lookup_filter_ne" g p))
    (let [[g p] (#'klt/prove-lookup-insert)] (reg! "List.lookup_insert" g p))
    (let [[g p] (#'gbt/prove-map-lookup-insert)] (reg! "Map.lookup_insert" g p))))

(def ^:private fK (e/fvar 1)) (def ^:private fV (e/fvar 2)) (def ^:private fd (e/fvar 3))
(def ^:private ff (e/fvar 4)) (def ^:private fk (e/fvar 5)) (def ^:private fys (e/fvar 6)) (def ^:private fm (e/fvar 7))
(def ^:private beqI (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) fK fd))
(def ^:private listV (e/app (e/const' (nm "List") [z]) fV))
(def ^:private mapKLV (e/app* (e/const' (nm "Map") [z z]) fK listV))
(def ^:private deceqK (e/app (e/const' (nm "DecidableEq") [L1]) fK))
(def ^:private vk (e/forall' "_" fV fK :default))
(def ^:private nilV (e/app (e/const' (nm "List.nil") [z]) fV))
(def ^:private boolT (e/const' (nm "Bool") []))
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

(defn- prove-bucket-gen []
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

(defn- prove-bucket-final []
  ;; gen at m=∅ (RHS acc matched to getD(lookup k ∅) so exact is syntactic); const form via check-constant
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

;; filter_foldflip: filter p (foldl (·::·) acc l) = foldl (·::·) (filter p acc) (filter p l)
(defn- prove-filter-foldflip []
  (let [V (e/fvar 1) p (e/fvar 2) l (e/fvar 3) acc (e/fvar 4)
        lV (e/app (e/const' (nm "List") [z]) V)
        flip (e/lam "acc" lV (e/lam "x" V (e/app* (e/const' (nm "List.cons") [z]) V (e/bvar 0) (e/bvar 1)) :default) :default)
        ff (fn [a ll] (e/app* (e/const' (nm "List.foldl") [z z]) lV V flip a ll))
        ft (fn [ll] (e/app* (e/const' (nm "List.filter") [z]) V p ll))
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) lV (ft (ff acc l)) (ff (ft acc) (ft l)))
                 (#(e/forall' "acc" lV (e/abstract1 % 4) :default)) (#(e/forall' "l" lV (e/abstract1 % 3) :default))
                 (#(e/forall' "p" (e/forall' "_" V boolT :default) (e/abstract1 % 2) :default)) (#(e/forall' "V" type0 (e/abstract1 % 1) :default)))
        LEMff ['List.foldl_nil 'List.foldl_cons 'List.filter_nil 'List.filter_cons_of_pos 'List.filter_cons_of_neg]
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["V" "p" "l"])
        ps (basic/induction ps (fvid ps "l"))
        ps (reduce (fn [ps gid]
                     (let [psg (focus ps gid)
                           cons? (some (fn [[_ d]] (= "head" (:name d))) (:lctx (proof/current-goal psg)))]
                       (if cons?
                         (let [psg (basic/intros psg ["acc"]) hd (gf psg "head") ac (gf psg "acc")
                               ihid (or (fvid psg "ih_tail'") (fvid psg "ih_tail") (fvid psg "ih"))
                               q (try (simp/simp psg ['List.foldl_cons]) (catch Throwable _ psg))
                               q (try (basic/rewrite q (e/app (e/fvar ihid) (e/app* (e/const' (nm "List.cons") [z]) (gf psg "V") hd ac))) (catch Throwable _ q))
                               br (basic/by-cases q (e/app (gf q "p") hd))]
                           (reduce (fn [qq bid] (let [qb (focus qq bid)
                                                      r (try (basic/rewrite qb (e/fvar (fvid qb "hc"))) (catch Throwable _ qb))
                                                      r (try (simp/simp-all r LEMff) (catch Throwable _ r))]
                                                  (if (proof/solved? r) r (try (basic/rfl r) (catch Throwable _ r)))))
                                   br (new-goals (:goals q) (:goals br))))
                         (let [psg (basic/intros psg ["acc"]) q (try (simp/simp-all psg LEMff) (catch Throwable _ psg))]
                           (if (proof/solved? q) q (try (basic/rfl q) (catch Throwable _ q)))))))
                   ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; group_by-filter commutation: filter p (getD (lookup k (group_by f ys)) []) = getD (lookup k (group_by f (filter p ys))) []
(defn- prove-bucket-filter-commute []
  (let [fp (e/fvar 8)
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) listV
                         (e/app* (e/const' (nm "List.filter") [z]) fV fp (getD (mlook fk (e/app* (e/const' (nm "Map.group_by") []) fK fV fd ff fys))))
                         (getD (mlook fk (e/app* (e/const' (nm "Map.group_by") []) fK fV fd ff (e/app* (e/const' (nm "List.filter") [z]) fV fp fys)))))
                 (#(e/forall' "ys" listV (e/abstract1 % 6) :default)) (#(e/forall' "k" fK (e/abstract1 % 5) :default))
                 (#(e/forall' "p" (e/forall' "_" fV boolT :default) (e/abstract1 % 8) :default)) (#(e/forall' "f" vk (e/abstract1 % 4) :default))
                 (#(e/forall' "dec" deceqK (e/abstract1 % 3) :default)) (#(e/forall' "V" type0 (e/abstract1 % 2) :default)) (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["K" "V" "dec" "f" "p" "k" "ys"])
        gK (gf ps "K") gV (gf ps "V") gd (gf ps "dec") gf' (gf ps "f") gp (gf ps "p") gk (gf ps "k") gys (gf ps "ys")
        glistV (e/app (e/const' (nm "List") [z]) gV)
        gfiltp (fn [l] (e/app* (e/const' (nm "List.filter") [z]) gV gp l))
        bc (fn [ys] (e/app* (e/const' (nm "Map.bucket_content") []) gK gV gd gf' gk ys))
        ps (basic/rewrite ps (bc gys))
        ps (basic/rewrite ps (bc (gfiltp gys)))
        ps (simp/simp-all ps ['List.filter_foldflip 'List.filter_nil 'List.filter_filter])
        beqp (fn [a b] (e/app* (e/const' (nm "BEq.beq") [z]) gK (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) gK gd) a b))
        andb (fn [a b] (e/app* (e/const' (nm "Bool.and") []) a b))
        pred1 (e/lam "x" gV (andb (e/app gp (e/bvar 0)) (beqp gk (e/app gf' (e/bvar 0)))) :default)
        pred2 (e/lam "x" gV (andb (beqp gk (e/app gf' (e/bvar 0))) (e/app gp (e/bvar 0))) :default)
        memty (e/app* (e/const' (nm "Membership.mem") [z z]) gV glistV (e/app (e/const' (nm "List.instMembership") [z]) gV) gys (e/bvar 0))
        hterm (e/lam "a" gV (e/lam "ha" memty (e/app* (e/const' (nm "Bool.and_comm") []) (e/app gp (e/bvar 1)) (beqp gk (e/app gf' (e/bvar 1)))) :default) :default)
        fc (e/app* (e/const' (nm "List.filter_congr") [z]) gV pred1 pred2 gys hterm)
        ps (basic/rfl (basic/rewrite ps fc))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; right-side filter pushdown (on the flatMap form that Map.join unfolds to):
;;   filter (p∘snd) (flatMap (λx. map (x,·) (bucket ys x)) xs) = flatMap (λx. map (x,·) (bucket (filter p ys) x)) xs
;; proved by simp: filter_flatMap + filter_map (the p∘snd∘mk predicate reduces via Prod.snd) + bucket_filter_commute.
(defn- prove-right-pushdown []
  (let [natT (e/const' (nm "Nat") []) listN (e/app (e/const' (nm "List") [z]) natT)
        decN (e/const' (nm "instDecidableEqNat") []) idf (e/lam "x" natT (e/bvar 0) :default)
        prodNN (e/app* (e/const' (nm "Prod") [z z]) natT natT) nilN (e/app (e/const' (nm "List.nil") [z]) natT)
        fp (e/fvar 100) fxs (e/fvar 101) fys (e/fvar 102)
        psnd (e/lam "pr" prodNN (e/app fp (e/app* (e/const' (nm "Prod.snd") [z z]) natT natT (e/bvar 0))) :default)
        bucket (fn [zs] (e/app* (e/const' (nm "Option.getD") [z]) listN
                                (e/app* (e/const' (nm "Map.lookup") []) natT listN decN (e/app idf (e/bvar 0))
                                        (e/app* (e/const' (nm "Map.group_by") []) natT natT decN idf zs)) nilN))
        innermap (fn [zs] (e/app* (e/const' (nm "List.map") [z z]) natT prodNN
                                  (e/lam "y" natT (e/app* (e/const' (nm "Prod.mk") [z z]) natT natT (e/bvar 1) (e/bvar 0)) :default) (bucket zs)))
        flatform (fn [zs] (e/app* (e/const' (nm "List.flatMap") [z z]) natT prodNN (e/lam "x" natT (innermap zs) :default) fxs))
        filtPys (e/app* (e/const' (nm "List.filter") [z]) natT fp fys)
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) (e/app (e/const' (nm "List") [z]) prodNN)
                         (e/app* (e/const' (nm "List.filter") [z]) prodNN psnd (flatform fys)) (flatform filtPys))
                 (#(e/forall' "ys" listN (e/abstract1 % 102) :default)) (#(e/forall' "xs" listN (e/abstract1 % 101) :default))
                 (#(e/forall' "p" (e/forall' "_" natT boolT :default) (e/abstract1 % 100) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["p" "xs" "ys"])
        ps (simp/simp-all ps ['List.filter_flatMap 'List.filter_map 'Function.comp 'Prod.snd 'Map.bucket_filter_commute])]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(deftest bucket-content
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (register-foundation!)
      (let [[gg gp] (prove-bucket-gen)]
        (is (some? gp) "bucket_content invariant proved")
        (is (true? (checks? gp gg)) "bucket_content gen kernel-checks")
        (reg! "Map.bucket_content_gen" gg gp))
      (let [[cg cp] (prove-bucket-final)]
        (is (some? cp) "bucket_content (m=∅, inline) proved")
        ;; const form is def-eq (group_by ≡ foldl gbstep ∅, getD(lookup k ∅)≡[]); kernel admits it
        (is (true? (checks? cp cg))
            "getD (lookup k (group_by f ys)) [] = foldl (·::·) [] (filter (k==f·) ys) — kernel-checks")
        (reset! a/ansatz-env (kenv/check-constant (a/env) (kenv/mk-thm (nm "Map.bucket_content") [] cg cp))))
      ;; right-side-pushdown lemmas: filter distributes through the bucket fold, and
      ;; group_by commutes with a filter (the heart of filter(p∘snd)(join)=join(·,filter p)).
      (let [[fg fp] (prove-filter-foldflip)]
        (is (some? fp) "filter_foldflip proved")
        (is (true? (checks? fp fg)) "filter_foldflip kernel-checks")
        (reg! "List.filter_foldflip" fg fp))
      (let [[cg cp] (prove-bucket-filter-commute)]
        (is (some? cp) "group_by-filter commutation proved")
        (is (true? (checks? cp cg))
            "filter p (bucket(group_by ys)) = bucket(group_by (filter p ys)) — kernel-checks")
        (reg! "Map.bucket_filter_commute" cg cp))
      ;; the full right-side pushdown (on the flatMap form Map.join unfolds to)
      (let [[rg rp] (prove-right-pushdown)]
        (is (some? rp) "right-side filter pushdown proved")
        (is (true? (checks? rp rg))
            "filter (p∘snd) (join xs ys) = join xs (filter p ys) [flatMap form] — kernel-checks")))
    (is true "SKIP bucket-content: no Init env")))
