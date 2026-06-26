(ns wandler.uniqueness-test
  "Step 4 capability proof: DISTINCT-removal (`eraseDups l = l`) is sound ONLY given a declared
   uniqueness (`Nodup l`). Installs + kernel-verifies the law + its helper. Gated on an Init env."
  (:require [wandler.laws.uniqueness :as uniq]
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
              "Nodup l → eraseDups l = l, kernel-checked — DISTINCT removal a stats planner can't do"))
        (testing "Path 2a — the KEYED helper proves (key-image membership contradiction)"
          (is (verifies? "filter_kf_not_mem")
              "kf a ∉ map kf l → filter (·≠ₖa) l = l, kernel-checked"))
        (testing "Path 2a capability: distinct-by-key is identity when the key is unique (relational FD)"
          (is (verifies? "nodup_map_eraseDupsBy")
              "Nodup (map kf xs) → eraseDupsBy (·==ₖ·) xs = xs — keyed DISTINCT removal, kernel-checked"))
        (testing "Path 2b helpers — absent-key bucket empty + distinct-key beq≠true"
          (is (verifies? "filter_key_eq_nil") "k ∉ map kf l → filter (k==kf·) l = []")
          (is (verifies? "key_beq_ne_true") "unique key ⇒ tail element's beq is not true"))
        (testing "Path 2b KEYSTONE: a unique-key group-by bucket is a SINGLETON (group-by elim foundation)"
          (is (verifies? "bucket_singleton")
              "Nodup (map kf l) → r ∈ l → filter (kf r == kf·) l = [r] — sound only with the key")))
    (println "SKIP uniqueness-laws-kernel-verify: no Init env")))
