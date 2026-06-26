(ns wandler.run-surface-test
  "Rung 5 front door — `wandler.core/run`: ONE verified `a/defn` pipeline, run in three execution MODES
   selected by the SOURCE type (the mode dispatcher re-interprets the SAME certified batch plan):
     :batch       List source      → fused + codegen'd runnable
     :incremental Zset source       → DBSP pull view (differential route + certificate)
     :async       Strm (Zset) source → push-driven live graph (async-incremental route + certificate)
   Regression-guards the two fixes that made this work from a fresh `a/init!`/installed env:
     (1) wandler.surface.streams/install-join! proves its law DAG against the canonical simp set (so
         mode/install! succeeds when the bundled @[simp] attrs are loaded), and
     (2) streams/type-head nil-guards (so a List a/defn pipeline still elaborates after the stream
         router is installed)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.exec.mode :as mode]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (wc/install!)
    (mode/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest one-pipeline-three-modes
  (when (ready?)
    ;; a plain batch pipeline over a List source, defined through the ordinary a/defn surface AFTER the
    ;; mode layer is installed (the path that previously NPE'd in the stream router / failed to install).
    (eval '(ansatz.core/defn dsum_rs [xs :- (List Nat)] Nat
             (reduce + 0 (map (fn [x :- Nat] (Nat.mul x 2)) xs))))
    (testing ":batch — fused, codegen'd, runs"
      (let [r (wc/run (a/env) 'dsum_rs :mode :batch)]
        (is (= :batch-fuse (:route r)) "List source ⇒ batch")
        (is (fn? (:run r)) "batch yields a runnable")
        (is (== 20 ((:run r) [1 2 3 4])) "and it executes (2+4+6+8)")))
    (testing ":incremental — the SAME plan routes to a differential (DBSP) view, certified"
      (let [r (wc/run (a/env) 'dsum_rs :mode :incremental)]
        (is (= :incremental (:route r)) "Zset source ⇒ pull-incremental")
        (is (true? (:diff (:mode r))) "differential mode")
        (is (some? (:certificate r)) "carries a boundary certificate")))
    (testing ":async — the SAME plan routes to an async-incremental (push) graph"
      (let [r (wc/run (a/env) 'dsum_rs :mode :async)]
        (is (= :async-incremental (:route r)) "Strm(Zset) source ⇒ async incremental")
        (is (= :async (:sched (:mode r))) "push-driven")))
    (testing "an unknown mode is rejected"
      (is (thrown? Throwable (wc/run (a/env) 'dsum_rs :mode :bogus))))))

(deftest non-join-incremental-runs
  (when (ready?)
    ;; the :incremental route now returns a RUNNABLE query for non-join pipelines too (not only joins):
    ;; the single-source delta stream is integrated and the linear map/filter/sum stages apply (DBSP).
    (eval '(ansatz.core/defn dsum_inc [xs :- (List Nat)] Nat
             (reduce + 0 (map (fn [x :- Nat] (Nat.mul x 2)) xs))))
    (testing "running incremental SUM over Z-set deltas == cumulative batch result"
      (let [r (wc/run (a/env) 'dsum_inc :mode :incremental)]
        (is (fn? (:run r)) "a non-join incremental pipeline now yields a runnable")
        ;; insert 1, then 2, then 3 — each doubled, summed cumulatively: 2, 2+4=6, 2+4+6=12
        (is (= [2 6 12] (mapv long ((:run r) [{1 1} {2 1} {3 1}]))))))
    (testing "filter + count increments correctly (delta retraction-safe Z-set engine)"
      (eval '(ansatz.core/defn cnt_inc [xs :- (List Nat)] Nat
               (reduce + 0 (map (fn [x :- Nat] 1) (filter (fn [x :- Nat] (Nat.ble 3 x)) xs)))))
      (let [r (wc/run (a/env) 'cnt_inc :mode :incremental)]
        ;; deltas 1,5,3,2 — count of elems ≥3 cumulatively: 0,1,2,2
        (is (= [0 1 2 2] (mapv long ((:run r) [{1 1} {5 1} {3 1} {2 1}]))))))))

(deftest optimizer-transformed-incremental-uses-naive
  ;; Regression for the unified front door: :batch runs the OPTIMIZED (fused) term, but
  ;; :incremental / :async DIFFERENTIATE the canonical NAIVE term. Here the optimizer fuses
  ;; filter+map+sum into a single `foldl` (the filter/map stages VANISH from the optimized
  ;; term) — differentiating THAT would miss the filter and give a wrong running view. The ∂
  ;; pass must see the un-fused [filter map sum] skeleton, so `run` sources the naive term.
  (when (ready?)
    (eval '(ansatz.core/defn fms_inc [xs :- (List Nat)] Nat
             (reduce + 0 (map (fn [x :- Nat] (Nat.mul x 2))
                              (filter (fn [x :- Nat] (Nat.ble 3 x)) xs)))))
    (testing "optimizer fuses the pipeline into a single foldl (filter/map gone)"
      (is (= ["foldl"] (mapv str (:stages-after (wc/explain 'fms_inc)))) "batch term is fully fused"))
    (testing ":incremental drives the un-fused skeleton — elems≥3 doubled, summed cumulatively"
      (let [r (wc/run (a/env) 'fms_inc :mode :incremental)]
        ;; deltas 1,5,3,2 : 1<3→0 ; 5→10 ; 3→16 ; 2<3→16
        (is (= [0 10 16 16] (mapv long ((:run r) [{1 1} {5 1} {3 1} {2 1}])))
            "differentiating the optimized [foldl] would drop the filter; naive term is correct")))))

(deftest per-group-aggregate-runs
  ;; Regression: the central data-crunching idiom `(map f (vals (group-by k xs)))`. map-fusion
  ;; eta-reduces the per-group `count`/`reduce` into a comp, which previously crashed codegen
  ;; (List.length / List.foldl as a fn value with the list arg missing). Now arity-tolerant.
  (when (ready?)
    (testing "count per group"
      (eval '(ansatz.core/defn gcount_rs [xs :- (List Nat)] (List Nat)
               (map (fn [g] (count g)) (vals (group-by (fn [x] (Nat.mod x 2)) xs)))))
      (is (= [4 3] (mapv long ((eval 'gcount_rs) '(1 2 3 4 5 6 7))))
          "odds {1,3,5,7}=4, evens {2,4,6}=3"))
    (testing "sum per group"
      (eval '(ansatz.core/defn gsum_rs [xs :- (List Nat)] (List Nat)
               (map (fn [g] (reduce + 0 g)) (vals (group-by (fn [x] (Nat.mod x 2)) xs)))))
      (is (= [16 12] (mapv long ((eval 'gsum_rs) '(1 2 3 4 5 6 7))))
          "Σodds=16, Σevens=12"))))
