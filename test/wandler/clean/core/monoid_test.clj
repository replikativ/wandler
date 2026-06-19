(ns wandler.clean.core.monoid-test
  "Phase 2 keystone: the parallel-fold licence (wandler.clean.core.monoid). Pins that both laws
   kernel `check-constant`-verify over the full Init store — the certificate that fork-join folding
   is sound (the proof lean-reducers omits)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [wandler.test-env :as test-env]
            [wandler.clean.core.monoid :as monoid]
            [wandler.clean.diff :as diff]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (monoid/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))

(deftest parallel-fold-licence-certified
  (when (ready?)
    (testing "foldl_hom — fold-from-accumulator factors as op a (fold-from-identity)"
      (is (diff/verifies? (a/env) "foldl_hom") "kernel check-constant verifies"))
    (testing "foldl_split — THE LICENCE: (xs ++ ys).fold = xs.fold ⊕ ys.fold, fork-join sound by proof"
      (is (diff/verifies? (a/env) "foldl_split") "kernel check-constant verifies"))
    (testing "split_certificate — the licence CONSUMED: fold-halves-and-combine = sequential fold"
      (is (diff/verifies? (a/env) "split_certificate") "kernel check-constant verifies"))
    (testing "the proof-gate (Phase 0 harness) reports all green"
      (is (:ok? (diff/proof-gate (a/env) ["foldl_hom" "foldl_split" "split_certificate"]))))))
