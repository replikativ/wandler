(ns wandler.stream-comonad-test
  "`Stream A := Nat → A` is a lawful COMONAD, proven in the kernel (`wandler.stream-comonad`): the
   exponent/stream comonad `(extract, duplicate, map)` with the three comonad laws (counit-left,
   counit-right, coassociativity). Closes the literal \"not a comonad\" part of the comonad/∂ debt; the
   guarded/causal ▷-modality is a separate formal system, documented as such. See [[programming-model-4-structures]]."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.stream-comonad :as sc]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (sc/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest stream-is-a-lawful-comonad
  (when (ready?)
    (testing "the comonad operations exist as kernel-checked defs"
      (doseq [n ["Stream.extract" "Stream.duplicate" "Stream.map"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present + kernel-verified"))))
    (testing "the three COMONAD LAWS are PROVEN (funext + Nat.add_zero/zero_add/add_assoc), not admitted"
      (doseq [n ["Stream.comonad_counit_l" "Stream.comonad_counit_r" "Stream.comonad_coassoc"]]
        (let [ci (kenv/lookup (a/env) (nm n))]
          (is (some? ci) (str n " present + kernel-verified"))
          (is (not (.isAxiom ci)) (str n " proven, not admitted")))))))
