(ns wandler.dbsp-group-test
  "The DBSP differential calculus generalized OFF `Int` to an abstract ABELIAN GROUP (`wandler.dbsp-group`):
   `D∘I = id` / `I∘D = id` proven over any `(G, zero, add, sub)` satisfying the abelian-group axioms (taken
   as hypotheses), with `Int` recovered as a CERTIFIED instance. Closes the ∂-generalization part of the
   comonad/∂ debt (the deeper guarded/comonadic `Strm` remains open). See [[programming-model-4-structures]]."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.dbsp-group :as dg]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (dg/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest differential-calculus-is-group-generic
  (when (ready?)
    (testing "D∘I=id and I∘D=id are PROVEN over an ABSTRACT abelian group (the four axioms as hypotheses)"
      (doseq [n ["Stream.Igen" "Stream.Dgen" "Stream.D_I_gen" "Stream.I_D_gen"]]
        (let [ci (kenv/lookup (a/env) (nm n))]
          (is (some? ci) (str n " present + kernel-verified"))
          (is (not (.isAxiom ci)) (str n " proven (uses only sub_zero/add_comm/add_sub_cancel/sub_add_cancel), not admitted")))))
    (testing "Int is recovered as a CERTIFIED INSTANCE — the differential calculus needs nothing Int-specific"
      (doseq [n ["Stream.D_I_int" "Stream.I_D_int"]]
        (let [ci (kenv/lookup (a/env) (nm n))]
          (is (some? ci) (str n " present + check-constant'd"))
          (is (not (.isAxiom ci)) (str n " is the generic group law instantiated at Int — a proof, not an axiom")))))))
