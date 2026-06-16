(ns wandler.jit-test
  "The verified hot-swap keystone: a windowed stream whose per-window operator is REPLACED mid-flight by
   a re-optimized one. Because the optimized plan is kernel-certified ≡ the original, every window — before
   AND after the swap — yields exactly the clojure.core ground truth. That is the property no other JIT
   has: profiling can trigger a recompile+swap, and the answer cannot change, only the speed."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.jit.stream :as jit]
            [wandler.optimize :as opt]
            [wandler.optimize.cost :as cost]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is use-fixtures]]))

(def ^:private z lvl/zero)
(defn- c [s] (e/const' (nm/from-string s) []))
(defn- setup [f] (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (w/install!)) (f))
(use-fixtures :once setup)

(deftest hot-swap-mid-stream-is-result-identical
  (if-not @test-env/init-full-env
    (is true "skipped — no Init env")
    (let [N (c "Nat") listN (e/app (e/const' (nm/from-string "List") [z]) N)
          win (e/fvar 1)
          p   (e/lam "x" N (e/app* (c "Nat.blt") (e/lit-nat 2) (e/bvar 0)) :default)
          sq  (e/lam "x" N (e/app* (c "Nat.mul") (e/bvar 0) (e/bvar 0)) :default)
          ;; per-window kernel: Σ x² over (filter (>2) window)
          term (e/app* (e/const' (nm/from-string "List.foldl") [z z]) N N (c "Nat.add") (c "Nat.zero")
                       (e/app* (e/const' (nm/from-string "List.map") [z z]) N N sq
                               (e/app* (e/const' (nm/from-string "List.filter") [z]) N p win)))
          compile (fn [t] (eval (a/ansatz->clj (a/env) (e/lam "w" listN (e/abstract1 t 1) :default) [])))
          naive-fn (compile term)
          r        (opt/optimize-cost (a/env) term :lctx {1 {:name "w" :type listN}})
          opt-fn   (compile (:term r))
          windows  [[1 2 3 4] [5 6 7 8] [9 10 11 12]]
          truth    (fn [w] (long (reduce + 0 (map #(* % %) (filter #(< 2 %) w)))))
          cell     (jit/swap-cell naive-fn)
          ;; drive the stream; after window 0, HOT-SWAP the operator to the optimized one
          results  (jit/drive-windows cell windows
                                      (fn [idx] (when (= idx 0) ((:swap! cell) opt-fn))))]
      (is (:verified? r) "the optimized per-window plan is kernel-certified ≡ the original")
      (is (:changed? r)  "the optimizer actually fused it (a real swap, not a no-op)")
      (is (= (mapv truth windows) (mapv long results))
          "every window — naive (w0) AND post-swap optimized (w1,w2) — = clojure.core ground truth")
      (is (= 1 ((:generation cell))) "exactly one hot-swap happened")
      ;; the swap was to a no-more-expensive plan (the planner only adopts cost-improving rewrites)
      (is (<= (double (cost/pipeline-cost (:term r) {})) (double (cost/pipeline-cost term {})))
          "the swapped operator is not more expensive than the original"))))

(deftest self-driving-jit-loop-measures-replans-swaps-stays-correct
  (if-not @test-env/init-full-env
    (is true "skipped — no Init env")
    (let [N (c "Nat") listN (e/app (e/const' (nm/from-string "List") [z]) N)
          p   (e/lam "x" N (e/app* (c "Nat.blt") (e/lit-nat 2) (e/bvar 0)) :default)
          sq  (e/lam "x" N (e/app* (c "Nat.mul") (e/bvar 0) (e/bvar 0)) :default)
          ;; per-window kernel: Σ x² over (filter (>2) window) — starts NAIVE (filter→map→fold), the loop
          ;; re-plans it to the fused single pass and hot-swaps mid-stream.
          term (e/app* (e/const' (nm/from-string "List.foldl") [z z]) N N (c "Nat.add") (c "Nat.zero")
                       (e/app* (e/const' (nm/from-string "List.map") [z z]) N N sq
                               (e/app* (e/const' (nm/from-string "List.filter") [z]) N p (e/fvar 1))))
          windows [[1 2 3 4] [5 6 7 8] [9 10 11 12] [13 14 15 16]]
          truth   (fn [w] (long (reduce + 0 (map #(* % %) (filter #(< 2 %) w)))))
          out (jit/jit-stream (a/env) term {1 {:name "w" :type listN}} 1 windows :warmup 1)]
      (is (= (mapv truth windows) (mapv long (:results out)))
          "every window — pre-swap (naive) AND post-swap (auto-re-planned) — = clojure.core ground truth")
      (is (= 1 (:swaps out)) "the loop measured, re-planned, and hot-swapped once (after warmup)")
      (is (< (:cost-after out) (:cost-before out))
          "the auto-selected plan is cheaper than the naive starting operator"))))
