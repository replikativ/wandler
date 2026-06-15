(ns wandler.surface-hoist-test
  "Step 3 (end-to-end): the user's actual cross-stream nested sum-product, written as ORDINARY
   Clojure and defined with a/defn, compiles to a CERTIFIED linear plan. The elaborator produces
   the hoistable shape, the optimize-hook runs the physical strategies, and phys/try-hoist-invariant
   (boundary-normalized to accept the surface `0` literal — the #73 issue) fires + certifies:

       (reduce + 0 (mapv (fn [x] (* x (reduce + 0 ys))) xs))   ;; O(|xs|·|ys|)
         ==>  (reduce + 0 xs) * (reduce + 0 ys)                ;; O(|xs|+|ys|), kernel-certified

   This is the headline: a nested cross-stream reduce that was quadratic is now linear, end to end
   from surface Clojure, with the speedup being the certificate of the rewrite."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is use-fixtures]]))

(def ^:private ready (atom false))

(use-fixtures :once
  (fn [f]
    (if @test-env/init-full-env
      (do (reset! a/ansatz-env @test-env/init-full-env)
          (binding [a/*verbose* false] (w/install!) (km/install!) (rl/install!))
          (reset! ready true) (f))
      (do (println "SKIP surface-hoist: no Init env") (f)))))

(deftest cross-stream-reduce-hoists-end-to-end
  (when @ready
    (binding [a/*verbose* false]
      (eval '(ansatz.core/defn cross-hoist [xs :- (List Nat), ys :- (List Nat)] Nat
               (reduce + 0 (mapv (fn [x] (* x (reduce + 0 ys))) xs)))))
    ;; the optimizer adopted the certified loop-invariant hoist during a/defn
    (is (= [:hoist-invariant] (vec (:rewrites (w/explain 'cross-hoist))))
        "a/defn ran the certified hoist on the cross-stream nested reduce")
    (is (:verified? (w/explain 'cross-hoist))
        "the adopted plan is kernel-certified ≡ the original definition")
    ;; runtime correctness: the optimized fn == clojure.core ground truth on varied data
    (let [f (deref (resolve 'cross-hoist))
          truth (fn [xs ys] (reduce + 0 (map #(* % (reduce + 0 ys)) xs)))]
      (doseq [[xs ys] [[[1 2 3] [10 20]] [[] [1 2]] [[5] []]
                       [(vec (range 50)) (vec (range 30))]
                       [(vec (range 200)) (vec (range 150))]]]
        (is (= (long (truth xs ys)) (long (f xs ys)))
            (str "hoisted cross == clojure.core on " (mapv count [xs ys])))))))

(deftest naive-path-still-correct
  (when @ready
    ;; with the optimizer OFF, the same surface compiles to the naive (quadratic) plan — still correct.
    (binding [a/*verbose* false, w/*optimize* false]
      (eval '(ansatz.core/defn cross-naive2 [xs :- (List Nat), ys :- (List Nat)] Nat
               (reduce + 0 (mapv (fn [x] (* x (reduce + 0 ys))) xs)))))
    (let [f (deref (resolve 'cross-naive2))]
      (is (= 180 (long (f [1 2 3] [10 20]))) "naive plan computes the same answer"))))
