(ns wandler.gradual-test
  "The gradual-typing → gradual-optimization front door (wandler.gradual): `gradient` shows what each
   tier of annotation unlocks, `coach` suggests what to annotate next — every plan kernel-certified.
   Over the canonical customers ⋈ orders sum-over-join."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.laws.faq :as rl]
            [wandler.gradual :as g]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (km/install!) (rl/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(defn- sum-join []
  (let [N (e/const' (nm "Nat") []) NN (e/app* (e/const' (nm "Prod") [z z]) N N) PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN)
        dec (e/const' (nm "instDecidableEqNat") [])
        cid (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)
        xs (e/fvar 5001) ys (e/fvar 5002)
        join (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid xs ys)
        amount (e/lam "p" PJ (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                               (e/app* (e/const' (nm "Prod.snd") [z z]) NN NN (e/bvar 0))) :default)
        amts (e/app* (e/const' (nm "List.map") [z z]) PJ N amount join)
        sum (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) amts)]
    {:term sum :lctx {5001 {:name "custs" :type (e/app (e/const' (nm "List") [z]) NN)}
                      5002 {:name "ords"  :type (e/app (e/const' (nm "List") [z]) NN)}}}))

(deftest gradient-shows-each-tier-unlocking-optimization
  (when (ready?)
    (testing "more annotations ⇒ more (certified) optimization"
      (let [{:keys [term lctx]} (sum-join)
            grad (g/gradient (a/env) term lctx
                   [["untyped"   {}]
                    ["+ ndv"     {:sizes {5001 1000 5002 1000} :ndv {5002 3.0}}]
                    ["+ budget"  {:sizes {5001 1000 5002 1000} :memory-budget 1.0}]])
            by-tier (into {} (map (juxt :tier identity)) grad)]
        (is (every? :verified? grad) "every tier's plan is kernel-certified")
        (is (some #{:hoist-index} (:rewrites (by-tier "untyped"))) "untyped: in-memory hash (factor + hoist)")
        (is (= [:pre-agg-index] (:gained (by-tier "+ ndv"))) "the ndv estimate UNLOCKS the pre-aggregated index")
        (is (some #{:nested-loop} (:rewrites (by-tier "+ budget"))) "a tight budget routes to the nested-loop")
        (is (string? (g/render-gradient grad)))))))


(deftest coach-suggests-annotations-that-unlock-rewrites
  (when (ready?)
    (testing "coach reports, empirically, which annotation unlocks which rewrite"
      (let [{:keys [term lctx]} (sum-join)
            sugg (g/coach (a/env) term lctx)
            by-ann (into {} (map (juxt :annotation identity)) sugg)]
        (is (contains? by-ann :ndv) "coach suggests :ndv")
        (is (= [:pre-agg-index] (:unlocks (by-ann :ndv))) ":ndv unlocks the pre-aggregated index")
        (is (string? (g/render-coach sugg)))))))
