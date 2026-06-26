(ns wandler.laws.fusion-test
  "Phase 3: the deforestation algebra (wandler.laws.fusion) — the fusion laws the clean optimizer
   rides are present in the env (free from Init). A fail-fast gate over that dependency."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.test-env :as test-env]
            [wandler.laws.fusion :as fusion]))

(defn- setup [f]
  (when @test-env/init-full-env (reset! a/ansatz-env @test-env/init-full-env))
  (f))
(use-fixtures :once setup)

(deftest deforestation-algebra-present
  (when @test-env/init-full-env
    (testing "the free Init fusion laws the optimizer fuses with are all present"
      (let [a (fusion/available?)]
        (is (:ok? a) (str "missing deforestation laws: " (:missing a)))))
    (testing "install! succeeds (fail-fast gate over the fusion dependency)"
      (is (= :installed (fusion/install!))))))
