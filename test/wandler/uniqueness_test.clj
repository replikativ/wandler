(ns wandler.uniqueness-test
  "Step 4 capability proof: DISTINCT-removal (`eraseDups l = l`) is sound ONLY given a declared
   uniqueness (`Nodup l`). Installs + kernel-verifies the law + its helper. Gated on an Init env."
  (:require [wandler.clean.laws.uniqueness :as uniq]
            [wandler.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is testing]]))

(defn- verifies? [s]
  (let [c (env/lookup (a/env) (name/from-string s))]
    (boolean (and c (env/verifies? (a/env) (.type c) (.value c))))))

(deftest uniqueness-laws-kernel-verify
  (if-let [ke @test-env/init-full-env]
    (do (reset! a/ansatz-env ke)
        (uniq/install!)
        (testing "the BEq+membership helper proves"
          (is (verifies? "filter_bne_self_not_mem")
              "a ∉ l → filter (·≠a) l = l, kernel-checked"))
        (testing "THE capability proof: eraseDups is identity on a Nodup list (sound only with the key)"
          (is (verifies? "nodup_eraseDups")
              "Nodup l → eraseDups l = l, kernel-checked — DISTINCT removal a stats planner can't do")))
    (println "SKIP uniqueness-laws-kernel-verify: no Init env")))
