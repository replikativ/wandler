(ns wandler.dist-laws-test
  "The FinSet/FinDist monad keystone (wandler.laws.dist): `WList.left_unit` — the monad left-unit law for the
   weighted-list `List(A×S)`, proven generic over `(S, mul, one)` with `one_mul` as a hypothesis. Anchors the
   runtime monad of wandler.inference.dist in the kernel; instantiates at any ⊗-unital semiring (Bool = FinSet, Nat = counting)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.laws.dist :as dl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(defn- setup [f] (when @test-env/init-full-env (reset! a/ansatz-env @test-env/init-full-env) (dl/install!)) (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest wlist-unit-laws-are-proven
  (when (ready?)
    (testing "BOTH monad unit laws are PROVEN kernel theorems (not admitted)"
      (doseq [n ["WList.left_unit" "WList.right_unit"]]
        (let [ci (kenv/lookup (a/env) (nm n))]
          (is (some? ci) (str n " present + kernel-verified"))
          (is (not (.isAxiom ci)) (str n " proven generically over the ⊗-monoid (one_mul/mul_one), not an axiom")))))
    (testing "it INSTANTIATES at Bool (the FinSet monad) via Bool.true_and — Bool ⊨ the left-unit law"
      ;; the application @WList.left_unit Bool Bool Bool Bool.and Bool.true Bool.true_and type-checks (the
      ;; FinSet monad left-unit holds); checked here by re-deriving its type through the kernel TypeChecker.
      (let [boolT (e/const' (nm "Bool") [])
            inst (e/app* (e/const' (nm "WList.left_unit") [])
                         boolT boolT boolT (e/const' (nm "Bool.and") [])
                         (e/const' (nm "Bool.true") []) (e/const' (nm "Bool.true_and") []))
            tc (ansatz.kernel.TypeChecker. (a/env))]
        (is (some? (.inferType tc inst)) "the Bool (FinSet) instantiation type-checks")))))
