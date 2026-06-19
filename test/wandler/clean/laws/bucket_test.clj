(ns wandler.clean.laws.bucket-test
  "The clean group_by-bucket foundation (wandler.clean.laws.bucket): the bridge from a real
   `Map.join` (group_by = foldl of inserts) down to the keyed `filter`-of-rows form the aggregate
   frame laws reason about. Pins that every lemma in the chain kernel `check-constant`-verifies over
   the full Init store. Replaces the ~1500-LOC term-built bucket cluster (old wandler.laws.proofs §3)
   with thin surface proofs riding ansatz.prelude.list's assoc-list lookup lemmas."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [wandler.test-env :as test-env]
            [wandler.clean.laws.bucket :as bucket]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (bucket/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))
(defn- has? [s] (some? (kenv/lookup (a/env) (name/from-string s))))
(defn- verifies? [s]
  (let [ci (kenv/lookup (a/env) (name/from-string s))]
    (boolean (and ci (try (kenv/check-constant-replace (a/env) ci) true (catch Throwable _ false))))))

(deftest bucket-foundation-certified
  (when (ready?)
    (testing "the assoc-list lookup foundation (ansatz.prelude.list) is present + verified"
      (is (has? "List.lookup_filter_ne"))
      (is (verifies? "List.lookup_filter_ne"))
      (is (has? "List.lookup_insert"))
      (is (verifies? "List.lookup_insert") "lookup-after-insert (cond via bif), kernel-verified"))
    (testing "Map.lookup_insert — exact at m.val, def-eq through the opaque Subtype Map"
      (is (has? "Map.lookup_insert"))
      (is (verifies? "Map.lookup_insert")))
    (testing "Map.bucket_content_gen — foldl-of-inserts invariant (induction generalizing m)"
      (is (has? "Map.bucket_content_gen"))
      (is (verifies? "Map.bucket_content_gen")))
    (testing "Map.bucket_content — closed form at empty (group_by bucket = keyed filter, reversed)"
      (is (has? "Map.bucket_content"))
      (is (verifies? "Map.bucket_content") "the keystone bridge, kernel check-constant-verified"))
    (testing "Map.join_eq + wsum_map_Map_join — the aggregate bridge to the clean filter-flatMap form"
      (is (has? "Map.join_eq"))
      (is (verifies? "Map.join_eq") "rfl-unfolding of the opaque Map.join")
      (is (has? "wsum_map_Map_join"))
      (is (verifies? "wsum_map_Map_join")
          "∑ over a real Map.join = ∑ over the clean join form (aggJoin_split's input), kernel-verified"))
    (testing "Map_aggJoin_factor — the planner-facing keyed FAQ factor law over a real Map.join"
      (is (has? "Map_aggJoin_factor"))
      (is (verifies? "Map_aggJoin_factor")
          "separable w·v over a group_by Map.join factors to sum-v-once-per-bucket (O(N²)→O(N)), kernel-verified"))))
