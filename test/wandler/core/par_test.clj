(ns wandler.core.par-test
  "Phase 2: the certified parallel fold (wandler.core.par). Pins that `parFold` (the curried
   divide-and-conquer fold — Lean's brecOn-with-function-motive encoding, where the recursion
   TRANSFORMS the carried list) defines + kernel-verifies, and that `parFold_eq` (parallel ≡
   sequential) check-constant-verifies. The fork-join certificate, by proof."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.test-env :as test-env]
            [wandler.core.par :as par]
            [wandler.diff :as diff]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (par/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))

(deftest certified-parallel-fold
  (when (ready?)
    (testing "parFold — curried divide-and-conquer fold (transforms the carried list) kernel-verifies"
      (is (diff/verifies? (a/env) "parFold") "kernel check-constant verifies"))
    (testing "parFold_eq — THE CERTIFICATE: parallel fold ≡ sequential fold, by proof"
      (is (diff/verifies? (a/env) "parFold_eq") "kernel check-constant verifies"))
    (testing "proof-gate (Phase 0 harness) green"
      (is (:ok? (diff/proof-gate (a/env) ["parFold" "parFold_eq"]))))))
