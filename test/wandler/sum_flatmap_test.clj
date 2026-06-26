(ns wandler.sum-flatmap-test
  "Item D — List.sum_flatMap, the missing monoid-hom law that unlocks the WEIGHTED SUM
   aggregation-through-join factorization:
       sum (flatMap g xs) = sum (map (λx. sum (g x)) xs)
   (sum is a monoid hom over ++). ABSENT in Init; proven here by induction on xs, on top
   of a Nat-specific `sum_append_nat` (also proven by induction — sidesteps Init's
   `List.sum_append`, which demands Std.Associative/Std.LawfulLeftIdentity instances that
   the tactic engine can't synthesize). Both kernel-checked with the AUTHORITATIVE
   env/verifies?. See [[semiring-sum-product-planner]].

   Proof gotchas that mattered: (1) simp eagerly unfolds List.sum→foldr and the zero is
   `Zero.zero …` (not `OfNat 0`), defeating sum-level + zero lemmas — so we drive it with
   explicit `basic/rewrite` (which matches up to def-eq, fixing the zero-rep mismatch).
   (2) Goal handling: rfl the nil goal in NATURAL order (focus-then-prove drops a rewrite
   side-goal → unassigned metavar)."
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
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(def ^:private NatT (e/const' (nm "Nat") []))
(def ^:private listN (e/app (e/const' (nm "List") [z]) NatT))
(def ^:private instAddNat (e/const' (nm "instAddNat") []))
(def ^:private zeroN (e/app* (e/const' (nm "Zero.ofOfNat0") [z]) NatT
                             (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 0))))
(defn- summ [l] (e/app* (e/const' (nm "List.sum") [z]) NatT instAddNat zeroN l))
(defn- appnd [l1 l2] (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) listN listN listN
                             (e/app* (e/const' (nm "instHAppendOfAppend") [z]) listN
                                     (e/app (e/const' (nm "List.instAppend") [z]) NatT)) l1 l2))
(defn- addN [x y] (e/app* (e/const' (nm "HAdd.hAdd") [z z z]) NatT NatT NatT
                          (e/app* (e/const' (nm "instHAdd") [z]) NatT instAddNat) x y))
(defn- gid [g n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx g)))
(defn- sumcons [a l] (e/app* (e/const' (nm "List.sum_cons") [z]) NatT instAddNat zeroN a l))
(defn- consapp [a l1 l2] (e/app* (e/const' (nm "List.cons_append") [z]) NatT a l1 l2))
(defn- zeroadd [a] (e/app (e/const' (nm "Nat.zero_add") []) a))
(defn- addassoc [a b c] (e/app* (e/const' (nm "Nat.add_assoc") []) a b c))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- close [ps] (if (proof/current-goal ps) (basic/rfl ps) ps))
(defn- flatMap [g l] (e/app* (e/const' (nm "List.flatMap") [z z]) NatT NatT g l))
(defn- mapf [f l] (e/app* (e/const' (nm "List.map") [z z]) NatT NatT f l))
(def ^:private PNN (e/app* (e/const' (nm "Prod") [z z]) NatT NatT))
(defn- mapPN [f l] (e/app* (e/const' (nm "List.map") [z z]) PNN NatT f l))
(defn- mapNP [f l] (e/app* (e/const' (nm "List.map") [z z]) NatT PNN f l))
(defn- flatMapNP [g l] (e/app* (e/const' (nm "List.flatMap") [z z]) NatT PNN g l))
(def ^:private pairfn (e/lam "y" NatT (e/app* (e/const' (nm "Prod.mk") [z z]) NatT NatT (e/bvar 1) (e/bvar 0)) :default))
(defn- sndN [p] (e/app* (e/const' (nm "Prod.snd") [z z]) NatT NatT p))
(defn- sumappnat [l1 l2] (e/app* (e/const' (nm "List.sum_append_nat") []) l1 l2))
(defn- flatmapcons [a l g] (e/app* (e/const' (nm "List.flatMap_cons") [z z]) NatT NatT a l g))
(defn- mapcons [f a l] (e/app* (e/const' (nm "List.map_cons") [z z]) NatT NatT f a l))

(defn- prove-sum-append-nat
  "∀ l1 l2 : List Nat, (l1 ++ l2).sum = l1.sum + l2.sum. Returns [goal proof|nil]."
  []
  (let [fl1 (e/fvar 200) fl2 (e/fvar 201)
        eqn (e/app* (e/const' (nm "Eq") [L1]) NatT (summ (appnd fl1 fl2)) (addN (summ fl1) (summ fl2)))
        goal (-> eqn (#(e/forall' "l2" listN (e/abstract1 % 201) :default))
                     (#(e/forall' "l1" listN (e/abstract1 % 200) :default)))
        ps0 (basic/intros (first (proof/start-proof (a/env) goal)) ["l1" "l2"])
        ps1 (basic/induction ps0 (gid (proof/current-goal ps0) "l1"))
        gs (proof/goals ps1)
        nilg (first (filter #(= 1 (count (:lctx %))) gs))
        consg (first (filter #(> (count (:lctx %)) 1) gs))
        psn (close (basic/rewrite (focus ps1 (:id nilg)) (zeroadd (summ (e/fvar (gid nilg "l2"))))))
        h (e/fvar (gid consg "head")) t (e/fvar (gid consg "tail"))
        cl2 (e/fvar (gid consg "l2")) ih (e/fvar (gid consg "ih_tail"))
        psc (-> (focus psn (:id consg))
                (basic/rewrite (consapp h t cl2))
                (basic/rewrite (sumcons h (appnd t cl2)))
                (basic/rewrite (sumcons h t))
                (basic/rewrite ih)
                (basic/rewrite (addassoc h (summ t) (summ cl2)))
                (close))]
    [goal (when (proof/solved? psc) (extract/extract psc))]))

(defn- prove-sum-flatMap
  "∀ g xs, sum (flatMap g xs) = sum (map (λx. sum (g x)) xs). Needs sum_append_nat admitted.
   Returns [goal proof|nil]."
  []
  (let [fg (e/fvar 100) fxs (e/fvar 101)
        sumfn (e/lam "x" NatT (summ (e/app fg (e/bvar 0))) :default)
        eqn (e/app* (e/const' (nm "Eq") [L1]) NatT (summ (flatMap fg fxs)) (summ (mapf sumfn fxs)))
        gToList (e/forall' "_" NatT listN :default)
        goal (-> eqn (#(e/forall' "xs" listN (e/abstract1 % 101) :default))
                     (#(e/forall' "g" gToList (e/abstract1 % 100) :default)))
        ps0 (basic/intros (first (proof/start-proof (a/env) goal)) ["g" "xs"])
        g (e/fvar (gid (proof/current-goal ps0) "g"))
        sumfn* (e/lam "x" NatT (summ (e/app g (e/bvar 0))) :default)
        ps1 (basic/induction ps0 (gid (proof/current-goal ps0) "xs"))
        ps2 (basic/rfl ps1)                                ; nil: both sides ≡ sum [] ≡ 0
        cg (proof/current-goal ps2)
        h (e/fvar (gid cg "head")) t (e/fvar (gid cg "tail")) ih (e/fvar (gid cg "ih_tail"))
        ps3 (-> ps2
                (basic/rewrite (flatmapcons h t g))                    ; flatMap g (h::t) → g h ++ flatMap g t
                (basic/rewrite (sumappnat (e/app g h) (flatMap g t)))  ; sum(g h ++ ..) → sum(g h) + sum(flatMap g t)
                (basic/rewrite ih)                                     ; sum(flatMap g t) → sum(map f t)
                (basic/rewrite (mapcons sumfn* h t))                   ; map f (h::t) → f h :: map f t
                (basic/rewrite (sumcons (e/app sumfn* h) (mapf sumfn* t)))  ; sum(f h :: ..) → f h + sum(map f t)
                (close))]
    [goal (when (proof/solved? ps3) (extract/extract ps3))]))

(defn- admit! [s g p]
  (when (and p (not (kenv/lookup (a/env) (nm s))))
    (reset! a/ansatz-env (kenv/check-constant (a/env) (kenv/mk-thm (nm s) [] g p)))))

(defn- prove-proj-through-join
  "map (λp. w(snd p)) (flatMap (λx. map (pair x)(g x)) xs) = flatMap (λx. map w (g x)) xs.
   The structural half (projection pushdown, no (x,y) materialized). Returns [goal proof|nil]."
  []
  (let [fg (e/fvar 100) fxs (e/fvar 101) fw (e/fvar 102)
        flatform (flatMapNP (e/lam "x" NatT (mapNP pairfn (e/app fg (e/bvar 0))) :default) fxs)
        projfn (e/lam "p" PNN (e/app fw (sndN (e/bvar 0))) :default)
        lhs (mapPN projfn flatform)
        rhs (flatMap (e/lam "x" NatT (mapf fw (e/app fg (e/bvar 0))) :default) fxs)
        eqn (e/app* (e/const' (nm "Eq") [L1]) listN lhs rhs)
        goal (-> eqn (#(e/forall' "xs" listN (e/abstract1 % 101) :default))
                     (#(e/forall' "g" (e/forall' "_" NatT listN :default) (e/abstract1 % 100) :default))
                     (#(e/forall' "w" (e/forall' "_" NatT NatT :default) (e/abstract1 % 102) :default)))
        ps (basic/intros (first (proof/start-proof (a/env) goal)) ["w" "g" "xs"])
        ps (try (simp/simp-all ps ['List.map_flatMap 'List.map_map 'Function.comp 'Prod.snd]) (catch Throwable _ ps))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defn- prove-weighted-sum-factor
  "The WEIGHTED SUM aggregation-through-join (needs proj_through_join_nat + sum_flatMap admitted):
     sum (map (λp. w(snd p)) (flatMap (λx. map (pair x)(g x)) xs)) = sum (map (λx. sum (map w (g x))) xs)
   Proof = rewrite projection-through-join, then sum_flatMap. Returns [goal proof|nil]."
  []
  (let [fg (e/fvar 100) fxs (e/fvar 101) fw (e/fvar 102)
        flatform (flatMapNP (e/lam "x" NatT (mapNP pairfn (e/app fg (e/bvar 0))) :default) fxs)
        projfn (e/lam "p" PNN (e/app fw (sndN (e/bvar 0))) :default)
        lhs (summ (mapPN projfn flatform))
        rhs (summ (mapf (e/lam "x" NatT (summ (mapf fw (e/app fg (e/bvar 0)))) :default) fxs))
        eqn (e/app* (e/const' (nm "Eq") [L1]) NatT lhs rhs)
        goal (-> eqn (#(e/forall' "xs" listN (e/abstract1 % 101) :default))
                     (#(e/forall' "g" (e/forall' "_" NatT listN :default) (e/abstract1 % 100) :default))
                     (#(e/forall' "w" (e/forall' "_" NatT NatT :default) (e/abstract1 % 102) :default)))
        ps0 (basic/intros (first (proof/start-proof (a/env) goal)) ["w" "g" "xs"])
        gg (fn [n] (e/fvar (gid (proof/current-goal ps0) n)))
        w (gg "w") g (gg "g") xs (gg "xs")
        H (e/lam "x" NatT (mapf w (e/app g (e/bvar 0))) :default)   ; H = λx. map w (g x)
        ps (-> ps0
               (basic/rewrite (e/app* (e/const' (nm "List.proj_through_join_nat") []) w g xs))
               (basic/rewrite (e/app* (e/const' (nm "List.sum_flatMap") []) H xs))
               (close))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(deftest sum-flatMap-monoid-hom
  (if @test-env/init-full-env
    (binding [a/*verbose* false]
      (reset! a/ansatz-env @test-env/init-full-env)
      ;; (1) sum_append_nat
      (let [[g1 p1] (prove-sum-append-nat)]
        (is (some? p1) "sum_append_nat proof extracts")
        (is (true? (kenv/verifies? (a/env) g1 p1)) "AUTHORITATIVE: (l1++l2).sum = l1.sum + l2.sum")
        (admit! "List.sum_append_nat" g1 p1))
      ;; (2) sum_flatMap (built on sum_append_nat)
      (let [[g2 p2] (prove-sum-flatMap)]
        (is (some? p2) "sum_flatMap proof extracts")
        (is (true? (kenv/verifies? (a/env) g2 p2))
            "AUTHORITATIVE: sum(flatMap g xs) = sum(map (λx. sum(g x)) xs)")
        (admit! "List.sum_flatMap" g2 p2)))
    (do (println "SKIP sum-flatMap-monoid-hom: no Init env") (is true))))

(deftest weighted-sum-aggregation-through-join
  ;; The full SUM semiring factorization: aggregate the WEIGHTED matching ys per key
  ;; BEFORE the cross product — never materialize the join. Composes the proven
  ;; projection-through-join with sum_flatMap. THE FAQ asymptotic win, SUM instance.
  (if @test-env/init-full-env
    (binding [a/*verbose* false]
      (reset! a/ansatz-env @test-env/init-full-env)
      ;; prerequisites (independent of the other deftest's ordering)
      (let [[ga pa] (prove-sum-append-nat)] (admit! "List.sum_append_nat" ga pa))
      (let [[gs ps] (prove-sum-flatMap)]   (admit! "List.sum_flatMap" gs ps))
      (let [[gp pp] (prove-proj-through-join)]
        (is (some? pp) "projection-through-join proof extracts")
        (is (true? (kenv/verifies? (a/env) gp pp)) "AUTHORITATIVE: map(w∘snd)(join) = flatMap(map w ∘ bucket)")
        (admit! "List.proj_through_join_nat" gp pp))
      (let [[gw pw] (prove-weighted-sum-factor)]
        (is (some? pw) "weighted-sum factorization proof extracts")
        (is (true? (kenv/verifies? (a/env) gw pw))
            "AUTHORITATIVE: sum(map(w∘snd)(join)) = sum(map (λx. sum(map w (bucket x))) xs)")))
    (do (println "SKIP weighted-sum-aggregation-through-join: no Init env") (is true))))
