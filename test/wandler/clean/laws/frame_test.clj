(ns wandler.clean.laws.frame-test
  "The clean relational frame laws (wandler.clean.laws.frame): aggregate-level join factorization +
   join-commutativity, proved with NO List.Perm. Pins that both kernel `check-constant`-verify over
   the full Init store. The capstone of the aggregate-level refinement (retires the List.Perm cluster)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [wandler.test-env :as test-env]
            [wandler.clean.laws.frame :as frame]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (frame/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))
(defn- has? [s] (some? (kenv/lookup (a/env) (name/from-string s))))
(defn- verifies? [s]
  ;; Authoritative kernel re-check (check-constant) under the original name.
  (let [ci (kenv/lookup (a/env) (name/from-string s))]
    (boolean (and ci (try (kenv/check-constant-replace (a/env) ci) true (catch Throwable _ false))))))

(deftest frame-laws-certified
  (when (ready?)
    (testing "aggJoin_split — the FAQ factorization (pure simp, no induction/Perm)"
      (is (has? "aggJoin_split"))
      (is (verifies? "aggJoin_split") "kernel check-constant verifies"))
    (testing "aggJoin_reorder — join-commutativity capstone via Fubini, NO List.Perm"
      (is (has? "aggJoin_reorder"))
      (is (verifies? "aggJoin_reorder") "kernel check-constant verifies"))
    (testing "the generic big-operator bridge it rides stays in the ansatz prelude"
      (is (has? "sum_filter_map") "filter→guard lemma installed (ansatz.prelude.list)")
      (is (has? "wsum") "the owned big-operator fold (ansatz.prelude.list)"))))
