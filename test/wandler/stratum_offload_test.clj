(ns wandler.stratum-offload-test
  "OPTIONAL stratum reducer-offload demo (run under :stratum — `clj -M:stratum:test`). Gated at runtime
   so the base suite never loads stratum. Integration 2 (tiers 1+2): a group-by/aggregate (and equi-
   join+aggregate) REDUCER not written as a query is transparently offloaded to stratum's in-memory SIMD
   engine, CORRECT (== eager; the monoid spec is the certificate), cost-gated, and faster on large
   high-cardinality data. The base wandler suite (clj -M:test) never requires this."
  (:require [clojure.test :refer [deftest is]]
            [wandler.reducers :as r]))

(defn- stratum? [] (try (require 'wandler.backend.stratum) true (catch Throwable _ false)))

;; local non-sum monoids (no such specs in the library yet) to exercise the min/max agg mapping
(def nat-max (r/monoid-spec {:name :nat/max :unit-fn (constantly 0) :combine max
                             :laws {:assoc 'Nat.max_assoc :left-identity 'Nat.zero_max :right-identity 'Nat.max_zero}}))
(def nat-min (r/monoid-spec {:name :nat/min :unit-fn (constantly Long/MAX_VALUE) :combine min
                             :laws {:assoc 'Nat.min_assoc :left-identity 'Nat.max_min :right-identity 'Nat.min_max}}))

;; a CUSTOM monoid OUTSIDE stratum's closed built-in agg set (no :bit-or kernel): bitwise-OR, identity 0
(def bit-or-monoid (r/monoid-spec {:name :nat/bit-or :unit-fn (constantly 0) :combine bit-or
                                   :laws {:assoc 'Nat.lor_assoc :left-identity 'Nat.zero_lor :right-identity 'Nat.lor_zero}
                                   :metadata {:stratum/prim-op 'clojure.core/bit-or}}))   ; Layer A primitive callback

(def ^:private force {:offload/force? true})   ; bypass the cost-gate so correctness tests hit stratum

(deftest stratum-reducer-offload
  (if-not (stratum?)
    (do (println "SKIP stratum-offload-test: stratum not on classpath (run with -M:stratum:test)") (is true))
    (let [register!   (requiring-resolve 'wandler.backend.stratum/register!)
          unregister! (requiring-resolve 'wandler.backend.stratum/unregister!)
          offload     (requiring-resolve 'wandler.backend.stratum/offload-group-by)
          joinsum     (requiring-resolve 'wandler.backend.stratum/offload-join-group-sum)
          diff        (fn [spec kf vf data]                  ; eager vs forced-offload, must agree
                        (unregister!)
                        (let [eager (r/group-by nil spec kf vf data)]
                          (register!)
                          (let [offl (r/group-by nil spec kf vf data force)] [eager offl])))]
      (try
        ;; ── correctness: offload == eager across aggregates + key kinds (the certificate check) ──
        (let [data (mapv (fn [i] {:dept (long (mod i 7)) :sal (long (mod i 100))}) (range 5000))
              [e o] (diff r/int-add :dept :sal data)] (is (= e o) "sum, numeric keys"))
        (let [data (mapv (fn [i] {:region ([:north :south :east :west] (mod i 4)) :amt (long (mod i 50))}) (range 5000))
              [e o] (diff r/int-add :region :amt data)] (is (= e o) "sum, keyword keys (dict-encoded)"))
        (let [data (mapv (fn [i] {:k (long (mod i 13))}) (range 5000))]
          (unregister!) (let [e (r/frequencies nil r/nat-add :k data)]
                          (register!) (is (= e (r/frequencies nil r/nat-add :k data force)) "frequencies = sum-of-ones")))
        (let [data (mapv (fn [i] {:dept (long (mod i 7)) :sal (long (mod (* i 31) 1000))}) (range 5000))
              [e o] (diff nat-max :dept :sal data)] (is (= e o) "MAX per group"))
        (let [data (mapv (fn [i] {:dept (long (mod i 7)) :sal (long (mod (* i 31) 1000))}) (range 5000))
              [e o] (diff nat-min :dept :sal data)] (is (= e o) "MIN per group"))

        ;; ── cost-gate: low cardinality DECLINES (→ eager), high cardinality offloads ──
        (unregister!)
        (let [low  (mapv (fn [i] {:d (long (mod i 8)) :v (long i)}) (range 5000))
              high (mapv (fn [i] {:d (long (mod i 50000)) :v (long i)}) (range 200000))]
          (is (nil? (offload nil r/int-add :d :v low {})) "cost-gate DECLINES low-cardinality/small data")
          (is (map? (offload nil r/int-add :d :v high {})) "cost-gate ACCEPTS high-cardinality large data"))

        ;; ── tier 3: an OPEN monoid (bitwise-OR, not in stratum's closed agg set) rides stratum's
        ;; grouped-fold — proving the substrate generalizes beyond the built-in aggregates ──
        (let [data (mapv (fn [i] {:dept (long (mod i 7)) :flags (long (bit-shift-left 1 (mod i 5)))}) (range 5000))
              [e o] (diff bit-or-monoid :dept :flags data)] (is (= e o) "OPEN monoid (bitwise-OR) via grouped-fold == eager"))

        ;; ── equi-join + group + sum (stratum builds the in-memory join index) ──
        (let [facts (mapv (fn [i] {:cust (long (mod i 1000)) :amt (long (mod i 100))}) (range 20000))
              dim   (mapv (fn [c] {:cust (long c) :region ([:n :s :e :w] (mod c 4))}) (range 1000))
              ;; eager join+group+sum reference
              c->r  (into {} (map (juxt :cust :region)) dim)
              eager (persistent! (reduce (fn [m x] (let [g (c->r (:cust x))]
                                                     (assoc! m g (+ (long (get m g 0)) (:amt x)))))
                                         (transient {}) facts))
              offl  (joinsum facts dim :cust :cust :region :amt)]
          (is (= eager offl) "equi-join + group-by region + sum amt == eager"))

        ;; ── value: high-cardinality group-by+sum, eager vs offload ──
        (let [n 2000000 groups 100000
              dvec  (vec (map (fn [i] {:dept (long (mod i groups)) :salary (long (mod i 1000))}) (range n)))
              time! (fn [f] (let [s (System/nanoTime)] (dotimes [_ 5] (f)) (/ (- (System/nanoTime) s) 5e6)))
              call  #(r/group-by nil r/int-add :dept :salary dvec force)]
          (unregister!) (dotimes [_ 2] (r/group-by nil r/int-add :dept :salary dvec))
          (let [eres (r/group-by nil r/int-add :dept :salary dvec) te (time! #(r/group-by nil r/int-add :dept :salary dvec))]
            (register!) (dotimes [_ 2] (call))
            (let [ores (call) to (time! call)]
              (is (= eres ores) "2M-row / 100k-group result agrees")
              (println (format "  group-by+sum, 2M rows / %d groups: eager %.0f ms · stratum %.0f ms (%.2f×)"
                               groups te to (/ te (max 0.01 to)))))))

        ;; ── tier 3 value: OPEN monoid (bit-OR) at high cardinality, eager vs stratum PARALLEL fold ──
        (let [n 2000000 groups 100000
              dvec  (vec (map (fn [i] {:dept (long (mod i groups)) :flags (long (bit-shift-left 1 (mod i 20)))}) (range n)))
              time! (fn [f] (let [s (System/nanoTime)] (dotimes [_ 5] (f)) (/ (- (System/nanoTime) s) 5e6)))
              call  #(r/group-by nil bit-or-monoid :dept :flags dvec force)]
          (unregister!) (dotimes [_ 2] (r/group-by nil bit-or-monoid :dept :flags dvec))
          (let [eres (r/group-by nil bit-or-monoid :dept :flags dvec)
                te   (time! #(r/group-by nil bit-or-monoid :dept :flags dvec))]
            (register!) (dotimes [_ 2] (call))
            (let [ores (call) to (time! call)]
              (is (= eres ores) "open-monoid 2M/100k result agrees")
              (println (format "  group-by+bitOR (OPEN monoid), 2M rows / %d groups: eager %.0f ms · stratum parallel %.0f ms (%.2f×)"
                               groups te to (/ te (max 0.01 to)))))))

        ;; ── Layer A: primitive (boxing-free) callback vs general Object accumulators — measured on the
        ;; FOLD IN ISOLATION (codes/values pre-built once). End-to-end this win is masked by the shared
        ;; dict-encode/materialization boundary (~200ms), which is the real bottleneck and the target of
        ;; the next sub-step (native-column fusion). Here we measure what the callback actually changes. ──
        (let [gfp   (requiring-resolve 'stratum.query.custom-agg/grouped-fold-prim-long)
              gfo   (requiring-resolve 'stratum.query.custom-agg/grouped-fold)
              n 2000000 groups 100000 t 8
              codes (long-array (map #(long (mod % groups)) (range n)))
              lvals (long-array (map #(long (bit-shift-left 1 (mod % 20))) (range n)))
              ovals (object-array lvals)
              lbo   (reify java.util.function.LongBinaryOperator (applyAsLong [_ a b] (bit-or a b)))
              time! (fn [f] (let [s (System/nanoTime)] (dotimes [_ 8] (f)) (/ (- (System/nanoTime) s) 8e6)))
              prim  #(gfp codes lvals groups 0 lbo t)
              obj   #(gfo codes ovals groups {:unit (constantly 0) :combine bit-or :threads t})]
          (dotimes [_ 3] (prim) (obj))
          (is (= (vec (prim)) (vec (obj))) "primitive long[] fold == Object fold")
          (let [tp (time! prim) tob (time! obj)]
            (println (format "  grouped-fold bitOR, 2M/%d (FOLD only): Object accs %.0f ms · primitive callback %.0f ms (%.2f×)"
                             groups tob tp (/ tob (max 0.01 tp))))))
        (finally (unregister!))))))
