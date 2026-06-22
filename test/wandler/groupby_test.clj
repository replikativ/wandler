(ns wandler.groupby-test
  "Path 2b — GROUP-BY ELIMINATION capability proofs: under a declared unique key, a group-by bucket is
   a singleton, so denormalize-each-row-with-its-group collapses to a map over rows. Installs +
   kernel-verifies the laws. Gated on the full Init env (needs Map/group_by/bucket machinery)."
  (:require [wandler.clean.laws.groupby :as groupby]
            [wandler.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is testing]]))

(defn- verifies? [s]
  (let [c (env/lookup (a/env) (name/from-string s))]
    (boolean (and c (env/verifies? (a/env) (.type c) (.value c))))))

(deftest groupby-elimination-laws-kernel-verify
  (if-let [ke @test-env/init-full-env]
    (do (reset! a/ansatz-env ke)
        (groupby/install!)
        (testing "explicit-argument map_congr_left wrapper (lift bridge)"
          (is (verifies? "List.map_congr_left_expl")
              "∀a∈l, f a = g a ⊢ map f l = map g l"))
        (testing "a unique-key bucket lookup returns the singleton (bucket_content ∘ bucket_singleton)"
          (is (verifies? "Map.bucket_singleton_lookup")
              "Nodup (map kf l) → r ∈ l → getD (lookup (kf r) (group_by kf l)) [] = [r]"))
        (testing "THE group-by-elimination law: group_by + per-row lookup collapses to map-over-rows"
          (is (verifies? "Map.groupby_self_elim")
              "Nodup (map kf xs) → map (λr. lookup (kf r) (group_by kf xs)) xs = map (λr. [r]) xs — sound only with the key")))
    (println "SKIP groupby-elimination-laws-kernel-verify: no Init env")))
