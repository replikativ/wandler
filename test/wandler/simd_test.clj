(ns wandler.simd-test
  "OPTIONAL Layer C demo (run under :stratum — `clj -M:stratum:test`). Gated at runtime. Demonstrates the
   floating-point determinism GUARANTEE: wandler proves whether a monoid's combine is associative and uses
   the proof to license (or refuse) the SIMD lane-reduction. The base wandler suite never loads this."
  (:require [clojure.test :refer [deftest is]]
            [wandler.reducers :as r]))

(defn- simd? [] (try (require 'wandler.simd) true (catch Throwable _ false)))

;; exact (associativity provable) vs floating-point (associativity false) monoids
(def bit-or-mono (r/monoid-spec {:name :nat/bit-or :unit-fn (constantly 0) :combine bit-or
                                 :laws {:assoc 'Nat.lor_assoc :left-identity 'a :right-identity 'b}
                                 :metadata {:ansatz/type 'Nat}}))
(def float-add   (r/monoid-spec {:name :float/add :unit-fn (constantly 0) :combine +'
                                 :laws {:assoc 'Float.add_assoc :left-identity 'a :right-identity 'b}
                                 :metadata {:ansatz/type 'Float}}))

(deftest proof-gated-simd
  (if-not (simd?)
    (do (println "SKIP simd-test: stratum/SimdReduce not on classpath (run with -M:stratum:test)") (is true))
    (let [licensed?   (requiring-resolve 'wandler.simd/simd-licensed?)
          simd-reduce (requiring-resolve 'wandler.simd/simd-reduce)
          col (long-array (map #(long (bit-shift-left 1 (mod % 20))) (range 100000)))
          scalar-or (areduce col i acc (long 0) (bit-or acc (aget col i)))]
      ;; the GATE: exact ops are licensed (associativity proven); Float.add is refused
      (is (licensed? r/int-add)   "Int.add — associativity proven ⇒ SIMD licensed")
      (is (licensed? bit-or-mono) "bit-OR — proven ⇒ licensed")
      (is (not (licensed? float-add)) "Float.add — NOT associative ⇒ SIMD refused")

      ;; licensed → deterministic SIMD, result identical to scalar
      (let [{:keys [result simd deterministic]} (simd-reduce col bit-or-mono)]
        (is simd "licensed ⇒ vectorized")
        (is deterministic "exact op ⇒ deterministic across vector widths")
        (is (= result scalar-or) "SIMD result == scalar"))

      ;; refused → deterministic scalar (the hazard avoided), with a reason
      (let [{:keys [simd deterministic reason]} (simd-reduce col float-add)]
        (is (not simd) "Float.add ⇒ NOT vectorized")
        (is deterministic "fell back to deterministic scalar")
        (is (= reason :assoc-not-proven) "refused because associativity isn't proven"))

      ;; ── double[] end-to-end: the hazard made concrete ──
      ;; crafted column where lane-reordering changes the float sum dramatically
      (let [n 2000002
            dcol (let [a (double-array n)] (aset a 0 1e20) (aset a (dec n) -1e20)
                       (dotimes [i 2000000] (aset a (inc i) 1.0)) a)]
        ;; default: Float.add refused → deterministic scalar (the correct left-fold answer, 0.0)
        (let [{:keys [result simd deterministic reason]} (simd-reduce dcol float-add)]
          (is (not simd) "Float.add over double[] ⇒ refused")
          (is deterministic "⇒ deterministic scalar")
          (is (= reason :assoc-not-proven))
          (is (== 0.0 result) "scalar left-fold = 0.0 (the reproducible answer)")
          ;; opt-in: fast SIMD (ColumnOps), flagged non-deterministic, and DEMONSTRABLY different
          (let [{simd-res :result vsimd :simd vdet :deterministic vwarn :warning}
                (simd-reduce dcol float-add {:reassociate-ok true})]
            (is vsimd ":reassociate-ok ⇒ vectorized")
            (is (not vdet) "...flagged non-deterministic")
            (is (some? vwarn))
            (is (not= simd-res result) "SIMD lane-reorder gives a DIFFERENT float sum — the hazard")))))))
