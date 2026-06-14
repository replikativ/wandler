(ns wandler.raster-test
  "OPTIONAL raster backend demo (run under the :raster alias: `clj -M:raster:test`). Gated at runtime so
   the base suite never loads raster. Demonstrates the value: a verified Float reduction lowered to
   raster's unboxed SIMD kernel, correct AND faster than boxed Clojure reduce. The base wandler suite
   (clj -M:test) never requires this — raster stays fully optional."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.env :as env]
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

(deftest raster-general-deftm-kernel
  "The GENERAL deftm path: a compute-heavy Float λ (Σ x^16) inlined into a raster deftm+compile-aot SIMD
   kernel — where raster ACTUALLY wins (compute-bound, not memory-bound). Demonstrates the value: a
   verified per-element kernel lowered to a fused SIMD/parallel loop, correct AND ~4× over single-thread."
  (if-not (raster?)
    (do (println "SKIP raster-general-deftm: raster not on classpath (run with -M:raster:test)") (is true))
    (let [raf   (requiring-resolve 'wandler.backend.raster/raster-array-form)
          floatT (e/const' (nm "Float") [])
          fmul   (e/const' (nm "Float.mul") [])
          fadd   (e/const' (nm "Float.add") [])
          ;; pow: x^n as nested binary Float.mul (n-1 muls), no float literals needed
          pow    (fn [n] (reduce (fn [acc _] (e/app* fmul (e/bvar 0) acc)) (e/bvar 0) (range (dec n))))
          k16    (e/lam "x" floatT (pow 16) :default)                       ; λx. x^16  (15 muls)
          src    {:op :source :term (e/bvar 0)}
          sum16  {:op :foldl :fn fadd :init nil :input {:op :map :fn k16 :input src}}  ; Σ x^16
          env    (env/empty-env)
          form   (raf env sum16 ["xs"])]
      (is (some? form) "raster recognizes Σ x^16 → general deftm kernel")
      (let [f      (eval (list 'clojure.core/fn '[xs] form))
            small  (mapv double (range 1 5))                                ; 1^16+2^16+3^16+4^16
            expect (reduce + (map #(Math/pow % 16) small))]
        (is (< (Math/abs (- (f small) expect)) 1.0)
            (str "Σ x^16 over 1..4 = " expect))
        ;; value demo: the compiled raster kernel vs single-thread Clojure over the SAME double[]
        (let [n   2000000
              da  (double-array (map #(/ (double %) (double n)) (range n)))
              pc  (fn ^double [^double a] (reduce (fn [^double acc _] (* a acc)) a (range 15)))
              cl  (fn [^doubles x] (areduce x i acc 0.0 (+ acc (pc (aget x i)))))
              kf  ((requiring-resolve 'wandler.backend.raster/compile-sum-kernel)
                   ((requiring-resolve 'ansatz.codegen/ansatz->clj) env (e/lam-body k16) ["a"]))]
          (dotimes [_ 5] (cl da) (kf da))
          (let [time! (fn [g] (let [s (System/nanoTime)] (dotimes [_ 10] (g)) (/ (- (System/nanoTime) s) 1e7)))
                tc (time! #(cl da))
                tr (time! #(kf da))]
            (is (< (Math/abs (- (cl da) (kf da))) 1e-6) "raster deftm kernel matches Clojure on 2M doubles")
            (println (format "  Σ x^16 over 2M doubles (COMPUTE-bound, double[] in): clojure single-thread %.1f ms · raster deftm SIMD %.1f ms (%.2f×)"
                             tc tr (/ tc (max 0.01 tr))))))))))
