(ns wandler.nested-faq-test
  "Under-binder cost search (#C): a SEPARABLE nested sum `Σx Σy x·y` factors to `(Σx x)·(Σy y)` —
   O(N·M) → O(N+M). The inner hoist `Σy x·y → x·(Σy y)` fires UNDER the outer `λx` (internalize-binders
   opens the SOAC step-λs), is rebuilt with a `funext` congruence proof, and the outer hoist then
   factors the now-x-invariant `Σy y` out. The composed proof is kernel-verified."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.clean.optimize.egraph :as ege]
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

(defn- cst [s] (e/const' (nm s) []))
(def ^:private N (cst "Nat"))
(defn- foldl0 [l] (e/app* (e/const' (nm "List.foldl") [z z]) N N (cst "Nat.add") (cst "Nat.zero") l))
(defn- mapN [f l] (e/app* (e/const' (nm "List.map") [z z]) N N f l))
(def ^:private LN (e/app (e/const' (nm "List") [z]) N))

(deftest nested-separable-sum-factors-and-verifies
  (when (ready?)
    (testing "Σx Σy x·y  →  (Σx x)·(Σy y), kernel-verified (under-binder #C)"
      (let [xs (e/fvar 1) ys (e/fvar 2)
            ;; foldl+0 (map (λx. foldl+0 (map (λy. x·y) ys)) xs)
            inner (e/lam "y" N (e/app* (cst "Nat.mul") (e/bvar 1) (e/bvar 0)) :default)
            term  (foldl0 (mapN (e/lam "x" N (foldl0 (mapN inner ys)) :default) xs))
            lctx  {1 {:name "xs" :type LN} 2 {:name "ys" :type LN}}
            r     (ege/saturate-and-extract (a/env) term :lctx lctx)
            s     (e/->string (:term r))]
        (is (:changed? r) "the nested sum was rewritten")
        (is (:verified? r) "the composed funext+congruence proof kernel-verifies")
        ;; result is a top-level product of two INDEPENDENT folds: Nat.mul (foldl … xs) (foldl … ys)
        (is (some? (re-find #"Nat.mul \(List.foldl" s)) "factored into a product of two sums")
        (is (< (cost/soac-depth-cost (:term r)) (cost/soac-depth-cost term))
            "strictly cheaper by the honest depth cost (O(N·M) → O(N+M))")))))
