(ns wandler.stratum-offload-test
  "OPTIONAL stratum reducer-offload demo (run under :stratum — `clj -M:stratum:test`). Gated at runtime
   so the base suite never loads stratum. Demonstrates Integration 2: a group-by/aggregate REDUCER not
   written as a query is transparently offloaded to stratum's in-memory SIMD engine, CORRECT (== eager,
   the monoid spec is the certificate) AND faster on large numeric-key data. The base wandler suite
   (clj -M:test) never requires this — stratum stays fully optional."
  (:require [clojure.test :refer [deftest is]]
            [wandler.reducers :as r]))

(defn- stratum? [] (try (require 'wandler.backend.stratum) true (catch Throwable _ false)))

(deftest stratum-reducer-offload
  (if-not (stratum?)
    (do (println "SKIP stratum-offload-test: stratum not on classpath (run with -M:stratum:test)") (is true))
    (let [register!   (requiring-resolve 'wandler.backend.stratum/register!)
          unregister! (requiring-resolve 'wandler.backend.stratum/unregister!)]
      (try
        ;; ── correctness: offload result == eager result (the differential certificate check) ──
        ;; numeric keys (stratum groups them with SIMD directly)
        (let [data (mapv (fn [i] {:dept (long (mod i 7)) :salary (long (mod i 100))}) (range 5000))]
          (unregister!)
          (let [eager (r/group-by nil r/int-add :dept :salary data)]
            (register!)
            (let [offl (r/group-by nil r/int-add :dept :salary data)]
              (is (= eager offl) "stratum offload (numeric keys) == eager group-by+sum"))))
        ;; arbitrary (keyword) keys — dictionary-encoded, proving generality of key-f
        (let [data (mapv (fn [i] {:region ([:north :south :east :west] (mod i 4))
                                  :amt (long (mod i 50))}) (range 5000))]
          (unregister!)
          (let [eager (r/group-by nil r/int-add :region :amt data)]
            (register!)
            (let [offl (r/group-by nil r/int-add :region :amt data)]
              (is (= eager offl) "stratum offload (keyword keys, dict-encoded) == eager"))))
        ;; frequencies = sum-of-ones falls out of the same path
        (let [data (mapv (fn [i] {:k (long (mod i 13))}) (range 5000))]
          (unregister!)
          (let [eager (r/frequencies nil r/nat-add :k data)]
            (register!)
            (let [offl (r/frequencies nil r/nat-add :k data)]
              (is (= eager offl) "stratum offload of frequencies == eager"))))

        ;; ── value: HIGH-CARDINALITY group-by+sum, where it matters. wandler's eager group-by merges
        ;; PERSISTENT maps, which is slow at many groups; the offload (fast dict-encode + stratum SIMD
        ;; group) wins. (At LOW cardinality the columnarization boundary dominates and it's ~1×; and a
        ;; hand-coded mutable loop over already-columnar data can still beat stratum — so the cost model
        ;; must route by cardinality. This test pins the regime where offload helps.)
        (let [n     2000000
              groups 100000
              dvec  (vec (map (fn [i] {:dept (long (mod i groups)) :salary (long (mod i 1000))}) (range n)))
              time! (fn [f] (let [s (System/nanoTime)] (dotimes [_ 5] (f)) (/ (- (System/nanoTime) s) 5e6)))]
          (let [call #(r/group-by nil r/int-add :dept :salary dvec)]
            (unregister!)                                            ; measure TRUE eager
            (dotimes [_ 2] (call))
            (let [eager-res (call) te (time! call)]
              (register!)                                            ; now measure offload
              (dotimes [_ 2] (call))
              (let [offl-res (call) to (time! call)]
                (is (= eager-res offl-res) "2M-row / 100k-group result agrees")
                (println (format "  group-by+sum over 2M rows (%d groups): eager %.0f ms · stratum offload %.0f ms (%.2f×)"
                                 groups te to (/ te (max 0.01 to))))))))
        (finally (unregister!))))))
