(ns wandler.hoist-invariant-test
  "Loop-invariant distributive hoist (1-variable FAQ elimination): a multiplicative factor
   independent of the fold variable distributes OUT of a sum, so an expensive invariant (here a
   nested reduce over a second stream) is computed ONCE instead of per element. This is the
   certified fix for the measured nested-fold quadratic:
       reduce + 0 (map (λx. x * (reduce + 0 ys)) xs)   →   (reduce + 0 xs) * (reduce + 0 ys)
   O(|xs|·|ys|) → O(|xs|+|ys|). Certified by `List.sum_map_mul_const` (proofs.clj); the optimizer
   adopts it via `phys/try-hoist-invariant`, gated locally on the invariant being loop-shaped."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.kmap :as km]
            [wandler.clean.laws.faq :as rl]
            [wandler.clean.optimize :as opt]
            [wandler.clean.optimize.faq :as phys]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is use-fixtures]]))

(def ^:private z lvl/zero)
(defn- cst [s] (e/const' (nm/from-string s) []))
(def ^:private N (cst "Nat"))
(def ^:private ready (atom false))

(use-fixtures :once
  (fn [f]
    (if @test-env/init-full-env
      (do (reset! a/ansatz-env @test-env/init-full-env)
          (binding [a/*verbose* false] (w/install!) (km/install!) (rl/install!))
          (reset! ready true) (f))
      (do (println "SKIP hoist-invariant: no Init env") (f)))))

(defn- foldl0 [l] (e/app* (e/const' (nm/from-string "List.foldl") [z z]) N N (cst "Nat.add") (cst "Nat.zero") l))
(defn- mapN [fexpr l] (e/app* (e/const' (nm/from-string "List.map") [z z]) N N fexpr l))
(def ^:private LN (e/app (e/const' (nm/from-string "List") [z]) N))

(deftest sum-map-mul-const-installed
  (when @ready
    (is (some? (env/lookup (a/env) (nm/from-string "List.sum_map_mul_const")))
        "the loop-invariant distributive law is admitted (install! kernel-checks it)")))

(deftest hoist-fires-certifies-and-runs
  (when @ready
    (let [xs (e/fvar 1) ys (e/fvar 2)
          C  (foldl0 ys)                                   ; loop-invariant inner reduce (SOAC-shaped)
          step (e/lam "x" N (e/app* (cst "Nat.mul") (e/bvar 0) C) :default)
          term (foldl0 (mapN step xs))                     ; reduce + 0 (map (λx. x * ∑ys) xs)
          lctx {1 {:name "xs" :type LN} 2 {:name "ys" :type LN}}
          direct (phys/try-hoist-invariant (a/env) term :lctx lctx)
          r (opt/optimize-cost (a/env) term :lctx lctx)]
      (is (:verified? direct) "try-hoist-invariant produces a kernel-certified rewrite")
      (is (= :hoist-invariant (:rw direct)) "tagged as the invariant hoist")
      (is (= [:hoist-invariant] (vec (:rewrites r))) "optimize-cost adopts the hoist")
      (is (:verified? r) "the adopted plan kernel-certifies ≡ original")
      ;; runtime: original ≡ optimized ≡ clojure.core ground truth on varied data
      (let [lam (fn [t] (reduce (fn [body id] (e/lam (if (= id 1) "xs" "ys") LN (e/abstract1 body id) :default))
                                t (sort > [1 2])))
            f-orig (eval (a/ansatz->clj (a/env) (lam term) []))
            f-opt  (eval (a/ansatz->clj (a/env) (lam (:term r)) []))
            truth  (fn [xs ys] (reduce + 0 (map #(* % (reduce + 0 ys)) xs)))]
        (doseq [[xs ys] [['(1 2 3) '(10 20)] ['() '(1 2)] [(range 20) (range 15)] ['(5) '()]]]
          (is (= (long (truth xs ys)) (long ((f-orig xs) ys)) (long ((f-opt xs) ys)))
              (str "orig=opt=truth on " (mapv count [xs ys]))))))))

(deftest no-hoist-when-factor-is-not-invariant
  (when @ready
    ;; map (λx. x * x) xs — the second factor DEPENDS on x, so nothing to hoist; matcher returns nil.
    (let [xs (e/fvar 1)
          step (e/lam "x" N (e/app* (cst "Nat.mul") (e/bvar 0) (e/bvar 0)) :default)
          term (foldl0 (mapN step xs))]
      (is (nil? (phys/try-hoist-invariant (a/env) term :lctx {1 {:name "xs" :type LN}}))
          "no spurious hoist when both factors depend on the bound variable"))))

(deftest no-hoist-when-invariant-is-cheap
  (when @ready
    ;; map (λx. x * 7) xs — invariant is a scalar literal (not loop-shaped); skip (not worth a rewrite).
    (let [xs (e/fvar 1)
          step (e/lam "x" N (e/app* (cst "Nat.mul") (e/bvar 0) (e/lit-nat 7)) :default)
          term (foldl0 (mapN step xs))]
      (is (nil? (phys/try-hoist-invariant (a/env) term :lctx {1 {:name "xs" :type LN}}))
          "cheap scalar invariant is not worth hoisting (local SOAC gate)"))))
