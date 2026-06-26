(ns wandler.laws.groupby-join-test
  "Capstone #184 foundation (wandler.laws.groupby-join): the group-by-over-join factorization keystone.
   Pins that every lemma in the chain kernel `check-constant`-verifies over the full Init store —
   culminating in LEMMA A `Map.scatter_groupby_entries` (group-then-reduce = reduce-by-key / scatter),
   the theorem that licenses rewriting `map agg (vals (group-by key zs))` into a scatter that never
   materializes the join product. Commutativity-free: holds for any WAddMonoid (the scatter step uses
   group_by's own prepend order, so the per-key head equation closes definitionally)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [wandler.test-env :as test-env]
            [wandler.laws.groupby-join :as gbj]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (gbj/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))
(defn- has? [s] (some? (kenv/lookup (a/env) (name/from-string s))))
(defn- verifies? [s]
  (let [ci (kenv/lookup (a/env) (name/from-string s))]
    (boolean (and ci (try (kenv/check-constant-replace (a/env) ci) true (catch Throwable _ false))))))

(deftest groupby-join-foundation-certified
  (when (ready?)
    (testing "Map ops ↔ entries (rfl bridges over the opaque Subtype Map)"
      (doseq [n ["Map.insert_entries" "Map.empty_entries" "Map.lookup_entries"]]
        (is (has? n) n)
        (is (verifies? n) (str n " kernel-verified"))))
    (testing "lookup-through-value-map + filter/map-fst commute (the entries-step plumbing)"
      (doseq [n ["List.getD_lookup_map_val" "List.getD_lookup_map_wsum" "List.filter_fst_map_comm"]]
        (is (has? n) n)
        (is (verifies? n) (str n " kernel-verified"))))
    (testing "Map.scatter_head_val — per-key value equation (commutativity-free)"
      (is (has? "Map.scatter_head_val"))
      (is (verifies? "Map.scatter_head_val")))
    (testing "Map.scatter_groupby_step — one step preserves the entries-correspondence invariant"
      (is (has? "Map.scatter_groupby_step"))
      (is (verifies? "Map.scatter_groupby_step")))
    (testing "LEMMA A — Map.scatter_groupby_entries: group-then-reduce = reduce-by-key (the keystone)"
      (is (has? "Map.scatter_groupby_entries"))
      (is (verifies? "Map.scatter_groupby_entries")
          "the group-by-over-join factorization keystone, kernel check-constant-verified"))
    (testing "foldl↔wsum bridge (the query's `reduce + 0` aggregate = wsum, both unfused and fused)"
      (doseq [n ["Nat_wsum_cons" "Nat_wsum_nil" "List.foldl_Natadd_acc" "List.foldl_add_eq_wsum"
                 "List.foldl_inlineh_acc" "List.foldl_inlineh_eq_wsum"]]
        (is (has? n) n)
        (is (verifies? n) (str n " kernel-verified"))))
    (testing "integration laws — query shape = vals of scatter, and scatter∘join fusion"
      (doseq [n ["Map.scatter_groupby_entries_empty" "Map.groupby_reduce_eq_scatter" "Map.foldl_scatter_join_fuse"]]
        (is (has? n) n)
        (is (verifies? n) (str n " kernel check-constant-verified"))))
    (testing "fused-aggregate laws (match the elaborator's deforested query; uses the funext tactic)"
      (doseq [n ["Map.gbreduce_funeq" "Map.groupby_reduce_eq_scatter_fused"]]
        (is (has? n) n)
        (is (verifies? n) (str n " kernel check-constant-verified"))))
    (testing "CAPSTONE — Map.groupby_reduce_join_factor: the recognizer-facing whole-query law"
      (is (has? "Map.groupby_reduce_join_factor"))
      (is (verifies? "Map.groupby_reduce_join_factor")
          "group-by-over-join analytics shape = scatter (no join materialized), kernel-verified"))))
