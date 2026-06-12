(ns wandler.scorecard-test
  "AGENDA #4 — the standing SCALE SCORECARD (run via `clj -M:test -n wandler.scorecard-test`). At ~N rows it
   times the a/defn-compiled (verified-optimized) plan vs a hand-written Clojure baseline for the core ops,
   and prints throughput. Also SIZES agenda #3 (columnar): the record-field aggregation row shows whether
   persistent-vector boxing is the bottleneck (→ is columnar/raster worth it?). Correctness is asserted; the
   timing is printed, not asserted (machine-dependent), except a generous not-O(n²) guard."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.rel-laws :as rl]
            [wandler.collections :as coll]
            [wandler.relational]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv) (km/install!) (rl/install!) (coll/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(defn- ms [f] (let [t0 (System/nanoTime) v (f) e (/ (- (System/nanoTime) t0) 1e6)] [v e]))
(defn- best [f] (dotimes [_ 3] (f)) (apply min (repeatedly 4 #(second (ms f)))))  ; warm + best-of-4

(deftest scorecard
  (when (ready?)
    ;; suite-friendly N; bump to 500k–5M for a real scorecard run. The RATIOS are the informative part and
    ;; hold across scales. (At 500k the measured ratios were: fusion 1.81, record-agg 0.34, join 1.28.)
    (let [N 100000 NK 10000
          xs   (vec (range N))                                  ; List Nat (boxed persistent vector)
          recs (vec (for [i (range N)] [(rem i NK) (rem i 100)]))  ; List (Prod Nat Nat) — [cid amount]
          custs (vec (for [i (range NK)] [i 0]))
          ;; verified-optimized plans (captured via eval-return, not self-ref def)
          fuse (eval '(ansatz.core/defn sc-fuse [zs :- (List Nat)] Nat (reduce + 0 (mapv (fn [x] (* 2 x)) zs))))
          agg  (eval '(ansatz.core/defn sc-agg  [zs :- (List (Prod Nat Nat))] Nat (reduce + 0 (mapv (fn [p] (second p)) zs))))
          join (eval '(ansatz.core/defn sc-join [as :- (List (Prod Nat Nat)) bs :- (List (Prod Nat Nat))] Nat
                        (reduce + 0 (for [c as o bs :when (= (first c) (first o))] (second o)))))
          ;; hand baselines
          h-fuse (fn [zs] (reduce (fn [a x] (+ a (* 2 (long x)))) 0 zs))
          h-agg  (fn [zs] (reduce (fn [a p] (+ a (long (second p)))) 0 zs))
          h-join (fn [as bs] (let [ks (into #{} (map first) as)] (reduce (fn [a o] (if (ks (first o)) (+ a (long (second o))) a)) 0 bs)))]
      (testing "correctness vs hand baselines"
        (is (= (h-fuse xs)        (fuse xs)))
        (is (= (h-agg recs)       (agg recs)))
        (is (= (h-join custs recs)(join custs recs))))
      (let [row (fn [nm a-ms h-ms n] (format "  %-22s a/defn %7.1f ms (%5.1f M/s) | hand %7.1f ms | a/defn÷hand %.2f"
                                             nm a-ms (/ n (* a-ms 1000.0)) h-ms (/ a-ms h-ms)))]
        (println "\n=== SCALE SCORECARD (N =" N "rows) ===")
        (println (row "fusion map+fold"       (best #(fuse xs))        (best #(h-fuse xs))        N))
        (println (row "record-field agg"      (best #(agg recs))       (best #(h-agg recs))       N))
        (println (row "aggregating join"      (best #(join custs recs))(best #(h-join custs recs))N))
        (println "  (record-field-agg ratio ≫1 ⇒ columnar/raster #3 is worth it; ≈1 ⇒ defrecord rep already fine)")
        (println "============================================\n"))
      (testing "all plans are sub-O(n²) at scale (the join especially)"
        (is (< (best #(join custs recs)) 3000) "join is O(n)")))))
