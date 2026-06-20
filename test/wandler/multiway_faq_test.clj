(ns wandler.multiway-faq-test
  "RECURSIVE FAQ variable elimination over a MULTI-WAY join. The single aggregation-through-join step
   (Map.foldl_join_factor) is the INDUCTIVE CASE: after the outer join factors, the result is again a fold
   over a join, whose inner join factors by the SAME law. `optimize-cost` (via try-fold-factor*) iterates
   it to a fixpoint, eliminating EVERY join in the tree — O(N^k) → O(N) — composing the per-step Eq.trans
   proofs into one certificate. Here: a 3-way Σ over custs⋈orders⋈C, fully factored, certified, executed."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.clean.optimize :as opt]
            [wandler.clean.optimize.cost :as cost]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(defn- build3 []
  (let [N  (e/const' (nm "Nat") [])
        NN (e/app* (e/const' (nm "Prod") [z z]) N N)
        PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN)        ; custs×orders pair
        PJ2 (e/app* (e/const' (nm "Prod") [z z]) PJ NN)       ; (custs×orders)×C pair
        listNN (e/app (e/const' (nm "List") [z]) NN)
        dec (e/const' (nm "instDecidableEqNat") [])
        cid (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)
        cidPJ (e/lam "r" PJ (e/app* (e/const' (nm "Prod.fst") [z z]) N N
                              (e/app* (e/const' (nm "Prod.fst") [z z]) NN NN (e/bvar 0))) :default)
        join (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid (e/fvar 5001) (e/fvar 5002))
        join3 (e/app* (e/const' (nm "Map.join") []) N PJ NN dec cidPJ cid join (e/fvar 5003))
        ;; measure = C's amount = (snd (snd p)) : PJ2 →snd→ NN(C) →snd→ N(amount)
        amount3 (e/lam "p" PJ2 (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                                 (e/app* (e/const' (nm "Prod.snd") [z z]) PJ NN (e/bvar 0))) :default)
        amts3 (e/app* (e/const' (nm "List.map") [z z]) PJ2 N amount3 join3)
        sum3 (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") [])
                     (e/const' (nm "Nat.zero") []) amts3)]
    {:sum3 sum3 :listNN listNN
     :lctx {5001 {:name "custs" :type listNN} 5002 {:name "ords" :type listNN} 5003 {:name "cc" :type listNN}}}))

(defn- compile3 [{:keys [listNN]} t]
  (let [t1 (e/abstract1 t 5003) l3 (e/lam "cc" listNN t1 :default)
        t2 (e/abstract1 l3 5002) l2 (e/lam "ords" listNN t2 :default)
        t3 (e/abstract1 l2 5001) l1 (e/lam "custs" listNN t3 :default)]
    (eval (a/ansatz->clj (a/env) l1 []))))

(def ^:private CUSTS [[1 10] [2 20]])
(def ^:private ORDS  [[1 100] [2 50]])
(def ^:private CC    [[1 5] [1 7] [2 3]])     ; Σ C.amount over the 3-way = 5+7+3 = 15

(deftest multiway-faq-full-elimination
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [{:keys [sum3 lctx] :as D} (build3)
          sz {5001 1000 5002 1000 5003 1000}
          r (opt/optimize-cost (a/env) sum3 :lctx lctx :sizes sz)
          run (fn [t] (long ((((compile3 D t) CUSTS) ORDS) CC)))]
      (testing "every join in the 3-way tree is eliminated (recursive FAQ), certified ≡ naive"
        (is (:verified? r))
        (is (contains? (set (:rewrites r)) :fold-factor))
        (is (not (cost/mentions-const? (:term r) "Map.join")) "ALL joins eliminated — not just the outermost")
        (is (< (double (cost/pipeline-cost (:term r) {:sizes sz}))
               (double (cost/pipeline-cost sum3 {:sizes sz}))) "asymptotically cheaper")
        (println (format "  multiway FAQ: 3-way Σ cardinality %.0f → %.0f (join-free)"
                         (double (cost/pipeline-cost sum3 {:sizes sz}))
                         (double (cost/pipeline-cost (:term r) {:sizes sz})))))
      (testing "the fully-factored plan executes to the naive answer"
        (is (= 15 (run sum3)) "naive Σ C.amount over custs⋈orders⋈C")
        (is (= 15 (run (:term r))) "recursively-factored Σ = same answer")))))
