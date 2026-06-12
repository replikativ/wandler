(ns wandler.reducers.affine-test
  (:require [wandler.reducers.affine :as af]
            [wandler.reducers :as r]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [clojure.test :refer [deftest is]]))

;; Full Lean `Init` carries the arithmetic lemmas (Nat.left_distrib, mul_assoc,
;; add_assoc) and funext the affine-collapse proof needs. Shared, loaded once.
(def ^:private init-full-env test-env/init-full-env)

(deftest collapse-coeffs-folds-affine-composition
  ;; Pure coefficient arithmetic, no kernel needed: (3x+5)∘(2x+1) = 6x+8, etc.
  (is (= [6 8] (af/collapse-coeffs [[2 1] [3 5]])))
  (is (= [24 40] (af/collapse-coeffs [[2 1] [3 5] [1 2] [4 0]])))
  ;; runtime affine-fn matches the folded coefficients
  (let [coeffs [[2 1] [3 5] [1 2] [4 0]]
        [A B] (af/collapse-coeffs coeffs)
        chain (apply comp (reverse (map (fn [[a b]] (af/affine-fn a b)) coeffs)))]
    (is (= (mapv chain (range 25))
           (mapv (af/affine-fn A B) (range 25))))))

(deftest collapse-emits-kernel-checked-proof
  ;; Integration: the kernel proves (f_K ∘ … ∘ f_1) = (λx. A*x + B) from Init
  ;; lemmas only (no Mathlib).  Skips when init.ndjson is absent.
  (if-let [kenv @init-full-env]
    (let [coeffs [[2 1] [3 5] [1 2] [4 0] [2 7] [5 1] [1 9] [3 2]]
          res (af/collapse kenv coeffs)]
      (is (= 720 (:a res)))
      (is (= 1337 (:b res)))
      (is (= 16 (:ops-before res)))
      (is (= 2 (:ops-after res)))
      ;; the theorem type is the function equality we expect
      (is (re-find #"Function\.comp" (e/->string (:theorem-type res))))
      ;; runtime collapsed fn equals the actual 8-map composition
      (let [chain (apply comp (reverse (map (fn [[a b]] (af/affine-fn a b)) coeffs)))]
        (is (= (mapv chain (range 50)) (mapv (:fn res) (range 50)))))
      ;; end-to-end: the proven-collapsed pipeline computes the same sum as the
      ;; full transducer chain that Clojure would run
      (let [xs (vec (range 5000))
            fns (mapv (fn [[a b]] (af/affine-fn a b)) coeffs)
            baseline (transduce (apply comp (conj (mapv #(map %) fns) (filter odd?))) + 0 xs)
            collapsed (r/sum-by (r/pipeline (map (:fn res)) (filter odd?))
                                r/nat-add identity xs {:grain 512})]
        (is (= baseline collapsed))))
    (do
      (println "SKIP collapse-emits-kernel-checked-proof: test-data/init.ndjson absent")
      (is true))))
