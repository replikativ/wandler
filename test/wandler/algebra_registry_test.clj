(ns wandler.algebra-registry-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.prelude.algebra :as prelude]
            [ansatz.tactic.instance :as instance]
            [wandler.algebra :as algebra]
            [wandler.test-env :as test-env]))

(defn- nm [s] (name/from-string s))

(deftest carrier-instances-synthesize-with-an-environment-local-registry
  (when-let [base @test-env/init-full-env]
    (reset! a/ansatz-env base)
    (is (= :verified (:status (algebra/install-semiring-instance! "Nat" prelude/nat-row))))
    (doseq [cls ["WAddMonoid" "WSemiring"]]
      (let [ke (a/env)
            goal (e/app (e/const' (nm cls) []) (e/const' (nm "Nat") []))]
        (is (some? (instance/synthesize ke (instance/index-for ke) goal))
            (str cls " must synthesize without a discovery scan"))))
    ;; A checked cache can restore constants before their registry entries.
    (let [ke (a/env)
          index (env/get-extension ke :instances nil)]
      (reset! a/ansatz-env
              (env/with-extension ke :instances (dissoc index (nm "WAddMonoid") (nm "WSemiring"))))
      (dotimes [_ 2] (algebra/install-semiring-instance! "Nat" prelude/nat-row))
      (let [restored (instance/index-for (a/env))]
        (doseq [[cls iname] [["WAddMonoid" "instWAddMonoid_Nat"]
                             ["WSemiring" "instWSemiring_Nat"]]]
          (is (= 1 (count (filter #(= (nm iname) (:name %)) (get restored (nm cls)))))
              "restoring and re-registering an instance must not duplicate it"))))))
