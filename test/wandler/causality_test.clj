(ns wandler.causality-test
  "Extrinsic causality as a kernel theorem (wandler.causality) — the worked example for docs/TYPE_THEORY.md:
   `Stream.delay_causal` proves the DBSP delay is causal (output at t depends only on inputs ≤ t) in PLAIN
   CIC, no `▷` modality. Evidence that causality does NOT require a guarded-kernel extension."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.causality :as causal]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (causal/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest causality-is-provable-in-plain-cic
  (when (ready?)
    (testing "Stream.delay_causal is a PROVEN kernel theorem (extrinsic causality, no ▷ extension)"
      (let [ci (kenv/lookup (a/env) (nm "Stream.delay_causal"))]
        (is (some? ci) "Stream.delay_causal present + kernel-verified")
        (is (not (.isAxiom ci)) "proven by Nat.casesOn over the delay, not admitted")))))
