(ns ansatz.plan-test
  "The plan LENS (ansatz.plan): a typed structured VIEW of the relational/SOAC fragment of a kernel
   term — the shared interface for explain/cost and the α/γ bridge to datahike/stratum."
  (:require [ansatz.plan :as plan]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private nat (e/const' (nm "Nat") []))
(def ^:private boolT (e/const' (nm "Bool") []))
(def ^:private prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat))
(def ^:private deceq (e/const' (nm "instDecidableEqNat") []))
(def ^:private beqN (e/app* (e/const' (nm "instBEqOfDecidableEq") [z]) nat deceq))
(def ^:private g (e/fvar 1)) (def ^:private p (e/fvar 2)) (def ^:private xs (e/fvar 3))
(def ^:private ys (e/fvar 4)) (def ^:private kf (e/fvar 5)) (def ^:private lf (e/fvar 6))

(deftest term->plan-recognizes-the-relational-fragment
  ;; (1) map g (filter p xs) — a linear pipeline
  (let [t  (e/app* (e/const' (nm "List.map") [z z]) nat nat g
                   (e/app* (e/const' (nm "List.filter") [z]) nat p xs))
        pl (plan/term->plan t)]
    (is (= :map (:op pl)))
    (is (= :filter (:op (:input pl))))
    (is (= :source (:op (:input (:input pl)))))
    (is (= ["filter" "map"] (plan/ops pl)))
    (is (= "· → filter → map" (plan/plan->str pl))))
  ;; (2) Map.join is a binary node with two parsed input pipelines
  (let [t  (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq kf lf xs ys)
        pl (plan/term->plan t)]
    (is (= :join (:op pl)))
    (is (= [:source :source] [(:op (:left pl)) (:op (:right pl))]))
    (is (identical? kf (:kf pl)))
    (is (identical? ys (:term (:right pl))) "right input parsed to its source leaf")
    (is (clojure.string/includes? (plan/plan->str pl) "⋈")))
  ;; (3) a filter whose predicate is a membership scan is annotated as a semijoin
  (let [semip (e/lam "x" nat (e/app* (e/const' (nm "List.elem") [z]) nat beqN (e/bvar 0) ys) :default)
        t     (e/app* (e/const' (nm "List.filter") [z]) nat semip xs)
        pl    (plan/term->plan t)]
    (is (= :filter (:op pl)))
    (is (true? (:semijoin? pl)) "membership-scan filter flagged as a semijoin")
    (is (clojure.string/includes? (plan/plan->str pl) "∈→idx")))
  ;; (4) a non-SOAC term is a source leaf
  (is (= {:op :source :term xs} (plan/term->plan xs))))

(deftest plan-term-round-trips-and-rebuilds
  ;; the lens is BIDIRECTIONAL: plan->term ∘ term->plan = identity on a pipeline term …
  (let [t  (e/app* (e/const' (nm "List.map") [z z]) nat nat g
                   (e/app* (e/const' (nm "List.filter") [z]) nat p
                           (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq kf lf xs ys)))]
    (is (.equals t (plan/plan->term (plan/term->plan t))) "map(filter(join)) round-trips exactly")
    ;; … and rewriting a child rebuilds the new term (the γ-lowering primitive)
    (let [xs2 (e/fvar 99)
          pl  (plan/term->plan t)
          pl' (assoc-in pl [:input :input :left] {:op :source :term xs2})
          t'  (plan/plan->term pl')
          ;; re-parse the rebuilt term and read the join's left input back out
          j'  (-> (plan/term->plan t') :input :input)]
      (is (not (.equals t t')) "swapping the join's left input changes the rebuilt term")
      (is (= :join (:op j')) "rebuilt term still parses as a join")
      (is (identical? xs2 (:term (:left j'))) "the join's left input is now xs2"))))
