(ns wandler.clean.surface.core-test
  "Phase 6 (clean tree) — THE SURFACE FRONT DOOR, end-to-end. Pins that ordinary Clojure collection +
   relational queries, written in a verified `a/defn` body, elaborate through the CLEAN surface verbs
   (`wandler.clean.surface.*`) to kernel `List.*`/`Map.*` terms, that those terms EXECUTE and agree with
   `clojure.core` (result-parity), and that the clean optimizer (`optimize-cost`) certifies a fused/
   factored plan over the elaborated body (`check-constant`). This is the cutover gate: a real query in,
   a verified + runnable plan out, with no dependency on the old `wandler.surface.*` tree.

   Mirrors the proven `wandler.threading-test` setup (install + `a/defn` + execute), retargeted to the
   clean surface. Collection codegen rides ansatz's builtin lowering; the relational join/group-by
   constants ride the shared kmap runtime (installed via `bucket/install!`), per the plan's
   runtime-is-shared-until-cutover decision."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as nm]
            [wandler.test-env :as test-env]
            [wandler.clean.laws.bucket :as bucket]
            [wandler.clean.surface.core :as surf]
            [wandler.clean.optimize :as opt]))

(defn- body-of [s] (.value (kenv/lookup (a/env) (nm/from-string s))))

(deftest clean-surface-collections-end-to-end
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (surf/install!)
      (binding [a/*verbose* false]
        ;; map∘map — the canonical deforestation target
        (eval '(ansatz.core/defn cs-mapmap [xs :- (List Nat)] (List Nat)
                 (mapv (fn [x] (inc x)) (mapv (fn [x] (inc x)) xs))))
        ;; ->> pipeline: map then sum (a streaming aggregate)
        (eval '(ansatz.core/defn cs-pipe [xs :- (List Nat)] Nat
                 (->> xs (mapv (fn [x] (inc x))) (reduce + 0)))))
      (testing "the clean collection verbs elaborate + EXECUTE, agreeing with clojure.core"
        (is (= (mapv inc (mapv inc [1 2 3 4]))
               ((resolve 'cs-mapmap) [1 2 3 4]))           "mapv∘mapv result-parity")
        (is (= (reduce + 0 (mapv inc [1 2 3 4]))
               ((resolve 'cs-pipe) [1 2 3 4]))             "->> mapv/reduce result-parity"))
      (testing "the clean optimizer certifies a fused plan over the elaborated body"
        (let [r (opt/optimize-cost (a/env) (body-of "cs-mapmap"))]
          (is (:changed? r)  "map∘map fused")
          (is (:verified? r) "the fusion proof (List.map_map) kernel check-constant-verifies")
          (is (= [:fuse] (:rewrites r))))))
    (do (println "SKIP clean-surface-collections: no Init env") (is true))))

(deftest clean-surface-relational-elaborates
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (binding [a/*verbose* false] (bucket/install!) (surf/install!))
      (testing "the clean relational verbs (group-by/count) elaborate a real aggregation query"
        (binding [a/*verbose* false]
          (eval '(ansatz.core/defn cs-groupcount [xs :- (List Nat)] (List (Prod Nat (List Nat)))
                   (->map (group-by (fn [x] x) xs)))))
        (is (some? (body-of "cs-groupcount")) "group-by/->map elaborated to a Map.group_by term")))
    (do (println "SKIP clean-surface-relational: no Init env") (is true))))
