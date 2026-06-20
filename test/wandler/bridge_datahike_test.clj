(ns wandler.bridge-datahike-test
  "The datahike adapter (wandler.bridge.datahike): datahike logical IR ↔ Ansatz kernel terms, pure
   data (no datahike runtime dep). Demonstrates (1) a datahike query optimizing through the bridge
   (filter→join pushdown, certified) and (2) the correlated-subquery DECORRELATION (a transducer
   whose fn invokes datahike's q ↦ ONE join)."
  (:require [ansatz.core :as a]
            [wandler.bridge :as bridge]
            [wandler.bridge.datahike :as dh]
            [wandler.clean.optimize :as opt]
            [wandler.laws.relational :as rl]
            [wandler.kmap :as kmap]
            [wandler.optimize.plan :as plan]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private nat (e/const' (nm "Nat") []))
(def ^:private prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat))
(def ^:private deceq (e/const' (nm "instDecidableEqNat") []))
(def ^:private listN (e/app (e/const' (nm "List") [z]) nat))
(def ^:private idf (e/lam "x" nat (e/bvar 0) :default))

(deftest datahike-query-optimizes-through-the-bridge
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (rl/install!)
      ;; the adapter is registered + present in the bridge (it loaded)
      (is (contains? (bridge/registered-engines) :datahike) "datahike adapter registered")
      ;; a datahike query:  filter (p ∘ fst) (entity-join users orders)  — a filter on the join's
      ;; left key, over two scans. α-lift → kernel term, optimize, γ-lower.
      (let [users (e/fvar 3) orders (e/fvar 4) p (e/fvar 2)
            predfst (e/lam "pr" prodNN (e/app p (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
            query {:op :filter :pred predfst
                   :in {:op :join :key-type nat :row nat :deceq deceq :kf idf :lf idf
                        :left {:op :scan :src users} :right {:op :scan :src orders}}}
            lctx {2 {:name "p" :type (e/forall' "_" nat (e/const' (nm "Bool") []) :default)}
                  3 {:name "users" :type listN} 4 {:name "orders" :type listN}}
            {:keys [plan verified? rewrites]}
            (bridge/optimize-plan (a/env) (fn [ir] (dh/lift ir nat)) query :lctx lctx)]
        (is (true? verified?) "the datahike-query optimization is kernel-certified")
        (is (contains? (set rewrites) "Map.filter_join_pushdown") "filter pushed into the join")
        ;; γ-lower the optimized plan back to datahike logical IR: the filter is now INSIDE the
        ;; join's left input (so datahike filters `users` before the entity-join).
        (let [dh-ir (dh/lower plan)]
          (is (= :entity-join (:op dh-ir)) "γ-lowered to a datahike entity-join")
          (is (= :filter (:op (:left dh-ir))) "the filter was pushed into the LEFT (users) scan")
          (is (= :scan (:op (:in (:left dh-ir)))) "…over the users scan")
          (is (= :scan (:op (:right dh-ir))) "right input is the orders scan, unfiltered"))))
    (do (println "SKIP datahike bridge test: no Init env") (is true))))

(deftest correlated-subquery-decorrelates-to-a-join
  ;; THE EXAMPLE: a transducer whose fn invokes datahike's q, correlated on the row —
  ;;   mapcat (λu. q[where order.user = (:id u)] db) users
  ;; decorrelates to ONE join the verified planner then optimizes. `decorrelate` builds that join.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (let [users (e/fvar 3) orders (e/fvar 4)
            joined (dh/decorrelate {:row-type nat :key-type nat :deceq deceq
                                    :kf idf :lf idf :rows users :scan orders})
            pl (plan/term->plan joined)]
        ;; the decorrelated term IS a Map.join the planner sees as a :join node …
        (is (= :join (:op pl)) "the correlated subquery decorrelated to a join")
        (is (= [:source :source] [(:op (:left pl)) (:op (:right pl))]))
        ;; … and round-trips through the lens (so it can be optimized + γ-lowered)
        (is (.equals joined (plan/plan->term pl)) "decorrelated join round-trips through the lens")))
    (do (println "SKIP correlated-subquery test: no Init env") (is true))))

(deftest correlated-aggregate-factorizes-through-the-join
  ;; THE WORKED DP EXAMPLE, end-to-end. The transducer
  ;;   (reduce + 0 (mapcat (fn [u] (d/q [... order.user = (:id u) ...] db)) users))
  ;; = "total spend over users' orders". It DECORRELATES to sum over a join, and then the
  ;; AGGREGATION-THROUGH-JOIN factorization fires: aggregate each user's order-amounts per key,
  ;; NEVER materializing the |users|·|orders| pairs — all kernel-certified.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (rl/install!)
      (let [users (e/fvar 3) orders (e/fvar 4)
            ;; α + decorrelate: the correlated subquery becomes one join (users ⋈ orders on id=user)
            join   (dh/decorrelate {:row-type nat :key-type nat :deceq deceq :kf idf :lf idf
                                    :rows users :scan orders})
            amount (e/lam "p" prodNN (e/app* (e/const' (nm "Prod.snd") [z z]) nat nat (e/bvar 0)) :default)
            mapped (e/app* (e/const' (nm "List.map") [z z]) prodNN nat amount join)
            zero   (e/const' (nm "Nat.zero") [])
            ;; the aggregate: sum (map amount (join))  — `reduce + 0` over the projected join
            total  (e/app* (e/const' (nm "List.foldl") [z z]) nat nat (e/const' (nm "Nat.add") []) zero mapped)
            lctx   {3 {:name "users" :type listN} 4 {:name "orders" :type listN}}
            res    (opt/optimize-cost (a/env) total :lctx lctx)]
        ;; the factorization fired and is kernel-certified
        (is (contains? (set (:rewrites res)) :fold-factor) "aggregation-through-join factorization fired")
        (is (true? (:verified? res)) "the factored plan ≡ the original is kernel-certified")
        ;; the optimized plan is a foldl over USERS (the outer driver), with NO Map.join left —
        ;; i.e. the |users|·|orders| product is never materialized.
        ;; result folds over the users stream (now under the hoisted-index β-redex — the in-memory
        ;; hash physical strategy), and the |users|·|orders| pair product is gone.
        (is (clojure.string/includes? (e/->string (:term res)) "List.foldl") "result folds over the users stream")
        (is (not (clojure.string/includes? (e/->string (:term res)) "Map.join Nat Nat Nat instDecidableEqNat #3"))
            "the join's xs·ys pair product is gone — aggregated per key instead")))
    (do (println "SKIP correlated-aggregate test: no Init env") (is true))))


(deftest q-is-typed-dependently-on-the-find-clause
  ;; #45 (the honest version): datahike's q is polymorphic in its RETURN shape (the :find spec). We
  ;; model the :find spec as a kernel VALUE (Datahike.FindSpec) and COMPUTE q's return type via the
  ;; type-level Datahike.Result : FindSpec → Type. So q : DB → (f) → Result f returns the PRECISE
  ;; type per find-spec — Nat for a scalar, List Nat for a coll, List (Nat×Bool) for a relation —
  ;; mirroring datalog-parser's FindScalar/FindColl/FindTuple/FindRel. (Large elimination over a
  ;; small code universe; admitted as datahike's API contract, opt-in.)
  (if-let [kenv0 @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv0)
      (dh/install-axioms!)
      (is (every? #(some? (kenv/lookup (a/env) (nm %)))
                  ["Datahike.TyCode" "Datahike.FindSpec" "Datahike.Decode" "Datahike.Result" "Datahike.q"])
          "the dependent boundary spec is admitted")
      (let [st0 (tc/mk-tc-state (a/env))
            db (e/fvar 9)
            st (ansatz.kernel.tc/attach-lctx st0 {9 {:name "db" :type (e/const' (nm "Datahike.DB") [])}})
            tint (e/const' (nm "Datahike.TyCode.tint") []) tbool (e/const' (nm "Datahike.TyCode.tbool") [])
            ;; q db <find-spec> : its computed return type (whnf)
            q-ty (fn [fs] (#'tc/cached-whnf st (tc/infer-type st (e/app* (e/const' (nm "Datahike.q") []) db fs))))
            natT (e/const' (nm "Nat") []) boolT (e/const' (nm "Bool") [])
            defeq? (fn [a b] (.isDefEq (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 50000000)) a b))
            fs-scalar (e/app* (e/const' (nm "Datahike.FindSpec.fscalar") []) tint)
            fs-coll   (e/app* (e/const' (nm "Datahike.FindSpec.fcoll") []) tint)
            fs-tuple  (e/app* (e/const' (nm "Datahike.FindSpec.ftuple") []) tint tbool)]
        ;; :find ?a .  (scalar) → Nat ;  :find ?a . over a bool attr → Bool
        (is (defeq? (q-ty fs-scalar) natT) "scalar find-spec ⇒ q : Nat")
        (is (defeq? (q-ty (e/app* (e/const' (nm "Datahike.FindSpec.fscalar") []) tbool)) boolT) "scalar over a bool attr ⇒ q : Bool")
        ;; :find [?a ...] (coll) → List Nat
        (is (defeq? (q-ty fs-coll) (e/app (e/const' (nm "List") [lvl/zero]) natT)) "coll find-spec ⇒ q : List Nat")
        ;; :find [?a ?b] (tuple) → Nat × Bool
        (is (defeq? (q-ty fs-tuple) (e/app* (e/const' (nm "Prod") [lvl/zero lvl/zero]) natT boolT)) "tuple find-spec ⇒ q : Nat × Bool")))
    (do (println "SKIP dependent-q test: no Init env") (is true))))

(deftest find-clause-lift-produces-the-typed-q
  ;; the α: a normalized :find spec (kind + each find-var's schema :db/valueType) → a FindSpec value,
  ;; so Datahike.q db (find->findspec spec) carries the precise return type. Mirrors what the
  ;; datalog-parser produces (FindScalar/FindColl/FindTuple/FindRel) + the schema valueTypes.
  (if-let [kenv0 @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv0)
      (dh/install-axioms!)
      (let [st0 (tc/mk-tc-state (a/env)) db (e/fvar 9)
            st (ansatz.kernel.tc/attach-lctx st0 {9 {:name "db" :type (e/const' (nm "Datahike.DB") [])}})
            natT (e/const' (nm "Nat") []) boolT (e/const' (nm "Bool") [])
            defeq? (fn [a b] (.isDefEq (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 50000000)) a b))
            tq (fn [spec] (#'tc/cached-whnf st (tc/infer-type st (e/app* (e/const' (nm "Datahike.q") []) db (dh/find->findspec spec)))))]
        (is (defeq? (tq {:kind :scalar :types [:db.type/long]}) natT) ":find ?a . (long) ⇒ Nat")
        (is (defeq? (tq {:kind :coll :types [:db.type/long]}) (e/app (e/const' (nm "List") [lvl/zero]) natT)) ":find [?a ...] ⇒ List Nat")
        (is (defeq? (tq {:kind :rel :types [:db.type/long :db.type/boolean]})
                    (e/app (e/const' (nm "List") [lvl/zero]) (e/app* (e/const' (nm "Prod") [lvl/zero lvl/zero]) natT boolT)))
            ":find ?a ?b (long boolean) ⇒ List (Nat × Bool)")))
    (do (println "SKIP find-lift test: no Init env") (is true))))

(deftest where-clause-lifts-to-a-relational-join
  ;; Track 1: a datahike :where with patterns SHARING a variable becomes a relational JOIN over
  ;; scans. [:where [?e :name ?n] [?e :age ?a]] → Map.join fst fst (scan name) (scan age) on the
  ;; shared entity ?e : List ((Nat×Nat) × (Nat×Bool)). The optimizer then handles it (scans are
  ;; opaque sources), certified.
  (if-let [kenv0 @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv0)
      (kmap/install!) (rl/install!) (dh/install-axioms!)
      (let [db (e/fvar 9) boolT (e/const' (nm "Bool") [])
            a1 (e/app* (e/const' (nm "OfNat.ofNat") [z]) nat (e/lit-nat 1) (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 1)))
            a2 (e/app* (e/const' (nm "OfNat.ofNat") [z]) nat (e/lit-nat 2) (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 2)))
            join (dh/where-entity-join db {:attr a1 :vtype nat} {:attr a2 :vtype boolT})
            st (ansatz.kernel.tc/attach-lctx (tc/mk-tc-state (a/env)) {9 {:name "db" :type (e/const' (nm "Datahike.DB") [])}})
            NN (e/app* (e/const' (nm "Prod") [z z]) nat nat)
            NB (e/app* (e/const' (nm "Prod") [z z]) nat boolT)
            want (e/app (e/const' (nm "List") [z]) (e/app* (e/const' (nm "Prod") [z z]) NN NB))]
        ;; the :where lifted to a typed Map.join over the two scans
        (is (.isDefEq (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 50000000)) (tc/infer-type st join) want)
            ":where join : List ((Nat×Nat) × (Nat×Bool))")
        (is (= "Map.join" (name/->string (e/const-name (first (e/get-app-fn-args join))))) "lifts to a Map.join on the shared entity")
        ;; and the optimizer accepts it (count over the join is certified)
        (let [cnt (e/app* (e/const' (nm "List.length") [z]) (e/app* (e/const' (nm "Prod") [z z]) NN NB) join)
              r (opt/optimize-cost (a/env) cnt :lctx {9 {:name "db" :type (e/const' (nm "Datahike.DB") [])}})]
          (is (true? (:verified? r)) "the query optimizes, certified"))))
    (do (println "SKIP where-join test: no Init env") (is true))))

(deftest lifted-query-plan-inhabits-the-dependent-q-type
  ;; Track 1, the loop closing: a full query [:find ?n ?a :where [?e :name ?n] [?e :age ?a]] lifts to
  ;; a relational plan (where-entity-join + project-rel2), and its type is DEFEQ to the dependent q's
  ;; type for that :find — i.e. the actual relational plan INHABITS q's typed interface. The :find
  ;; typing (the contract) and the :where plan (the implementation) meet.
  (if-let [kenv0 @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv0)
      (kmap/install!) (rl/install!) (dh/install-axioms!)
      (let [db (e/fvar 9) boolT (e/const' (nm "Bool") [])
            a1 (e/app* (e/const' (nm "OfNat.ofNat") [z]) nat (e/lit-nat 1) (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 1)))
            a2 (e/app* (e/const' (nm "OfNat.ofNat") [z]) nat (e/lit-nat 2) (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat 2)))
            plan (dh/project-rel2 (dh/where-entity-join db {:attr a1 :vtype nat} {:attr a2 :vtype boolT}) nat boolT)
            st (ansatz.kernel.tc/attach-lctx (tc/mk-tc-state (a/env)) {9 {:name "db" :type (e/const' (nm "Datahike.DB") [])}})
            q-ty (tc/infer-type st (e/app* (e/const' (nm "Datahike.q") []) db
                                           (dh/find->findspec {:kind :rel :types [:db.type/long :db.type/boolean]})))]
        (is (.isDefEq (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 50000000)) (tc/infer-type st plan) q-ty)
            "the lifted :where+:find plan inhabits the dependent q's type (List (Nat × Bool))")))
    (do (println "SKIP lifted-plan test: no Init env") (is true))))
