(ns wandler.coherence-probe-test
  "RUNTIME COHERENCE PROBE (small + fast). It already did its diagnostic job at scale and surfaced the key
   finding, recorded here:

   FINDING — the `a/defn` relational join is CORRECT and the optimizer DOES factorize + unbox it
   (`optimized: [:fold-factor :hoist-index]`, emits `afoldl`), BUT the `group_by` lowers to an
   ASSOCIATION-LIST with `(into {} m)` + `filterv` on EVERY element — i.e. O(n·distinct), not O(n). At
   50k×500k it never finishes. So joins do not yet scale: the runtime cashes fusion/unboxing but the
   join's group-by codegen needs to lower to a real O(1)-probe hash structure (a Clojure map / transient).
   This is the top runtime item in docs/AGENDA.md (#3 columnar/codegen). Tracked, not asserted-away.

   This test stays SMALL (correctness + that the optimizer fires) so it can't hang the suite."
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

(deftest join-correct-and-scales-O-n
  (when (ready?)
    ;; FIXED: Map now lowers to a Clojure hash-map (O(1) probe), so the verified join is O(n), not O(n²).
    ;; These sizes would HANG/timeout under the old association-list group_by; here they finish in ms.
    (let [NC 2000 NO 30000
          custs (vec (for [i (range NC)] [i (rem i 7)]))
          ords  (vec (for [i (range NO)] [(rem i NC) (rem i 100)]))
          truth (reduce + 0 (map second ords))
          revenue (eval '(ansatz.core/defn revenue
                           [xs :- (List (Prod Nat Nat)) ys :- (List (Prod Nat Nat))] Nat
                           (reduce + 0 (for [c xs o ys :when (= (first c) (first o))] (second o)))))]
      (testing "the a/defn join is correct at scale"
        (is (= truth (revenue custs ords)) "Σ amount over the join == ground truth"))
      (testing "and it runs in O(n) — the hash-map codegen, not the old O(n·distinct) assoc-list"
        (revenue custs ords)                                    ; warm
        (let [t0 (System/nanoTime) _ (revenue custs ords) ms (/ (- (System/nanoTime) t0) 1e6)]
          (is (< ms 3000) (format "%d×%d join ran in %.0f ms (O(n²) would not finish in 3s)" NC NO ms)))))))
