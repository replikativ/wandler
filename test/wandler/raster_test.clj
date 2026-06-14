(ns wandler.raster-test
  "OPTIONAL raster backend demo (run under the :raster alias: `clj -M:raster:test`). Gated at runtime so
   the base suite never loads raster. Demonstrates the value: a verified Float reduction lowered to
   raster's unboxed SIMD kernel, correct AND faster than boxed Clojure reduce. The base wandler suite
   (clj -M:test) never requires this — raster stays fully optional."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defn- nm [s] (name/from-string s))
(defn- raster? [] (try (require 'wandler.backend.raster) true (catch Throwable _ false)))

(deftest raster-array-backend-numeric
  (if-not (raster?)
    (do (println "SKIP raster-test: raster not on classpath (run with -M:raster:test)") (is true))
    (let [raf (requiring-resolve 'wandler.backend.raster/raster-array-form)
          floatT (e/const' (nm "Float") [])
          fadd   (e/const' (nm "Float.add") [])
          fmul   (e/const' (nm "Float.mul") [])
          sq     (e/lam "x" floatT (e/app* fmul (e/bvar 0) (e/bvar 0)) :default)  ; λx. x*x
          src    {:op :source :term (e/bvar 0)}                                    ; the input list
          sum    {:op :foldl :fn fadd :init nil :input src}                        ; Σ xs
          sumsq  {:op :foldl :fn fadd :init nil :input {:op :map :fn sq :input src}} ; Σ x²
          mk     (fn [plan] (when-let [form (raf nil plan ["xs"])] (eval (list 'clojure.core/fn '[xs] form))))
          fsum   (mk sum)
          fsq    (mk sumsq)
          data   (mapv double (range 1 11))]   ; 1.0 .. 10.0
      ;; recognizer + emission + the raster kernel are correct
      (is (some? fsum) "raster recognizes Σ xs → par/sum")
      (is (some? fsq)  "raster recognizes Σ x² → par/dot-product")
      (is (== 55.0  (fsum data)) "Σ 1..10 = 55 (raster.par/sum)")
      (is (== 385.0 (fsq data))  "Σ k² 1..10 = 385 (raster.par/dot-product)")
      ;; an UNrecognized shape declines (→ eager fallback): a foldl with a non-add step
      (is (nil? (raf nil {:op :foldl :fn fmul :init nil :input src} ["xs"])) "non-add fold declines")
      ;; value demo. The chunked-array model keeps data in unboxed arrays — so the FAIR comparison is
      ;; raster's SIMD kernel vs a Clojure scalar loop over the SAME double[] (the genuine win). The
      ;; List→double[] conversion my backend emits is the one-time boundary cost (amortized for
      ;; array-native data); shown separately so the kernel win isn't masked by it.
      (let [n   2000000
            da  (double-array (range n))
            box (vec da)
            cloj-arr (fn [^doubles a] (areduce a i acc 0.0 (+ acc (* (aget a i) (aget a i)))))
            cloj-box (fn [v] (reduce (fn [^double a ^double x] (+ a (* x x))) 0.0 v))
            rast (requiring-resolve 'raster.par/dot-product)]
        (dotimes [_ 5] (cloj-arr da) (rast da da) (cloj-box box) (fsq box))   ; warm the JIT
        (let [time! (fn [f] (let [s (System/nanoTime)] (dotimes [_ 10] (f)) (/ (- (System/nanoTime) s) 1e7)))
              t-karr (time! #(cloj-arr da))
              t-krast (time! #(rast da da))
              t-bbox (time! #(cloj-box box))
              t-bsq  (time! #(fsq box))]
          (is (== (cloj-arr da) (rast da da)) "raster matches Clojure on 2M doubles")
          (println (format "  Σx² over 2M doubles, KERNEL (double[] in): clojure areduce %.1f ms · raster SIMD %.1f ms (%.2f×)"
                           t-karr t-krast (/ t-karr (max 0.01 t-krast))))
          (println (format "  Σx² from a boxed list (incl. List→double[] boundary): clojure reduce %.1f ms · raster %.1f ms (%.2f×)"
                           t-bbox t-bsq (/ t-bbox (max 0.01 t-bsq)))))))))
