(ns wandler.sum-linearity-test
  "Step 2 of the FAQ programme: the LINEARITY structure of the sum semiring — the additive
   laws the optimizer / e-graph composes for sum-product variable elimination. All proven in
   proofs.clj and kernel-checked on admit by rl/install!:
     · List.sum_map_add_distrib : foldl(+) (a+b) (map (λx. f x + g x) xs)
                                  = foldl(+) a (map f xs) + foldl(+) b (map g xs)   (∑ is additive)
     · List.sum_map_zero        : foldl(+) acc (map (λ_. 0) ys) = acc                (∑ of zeros)
     · List.foldl_add_pull      : foldl(+) acc L = acc + foldl(+) 0 L                (init extraction)
   Together with step 1's List.sum_map_mul_const (∑ scales) these are the sum-semiring algebra."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.kmap :as km]
            [wandler.clean.laws.faq :as rl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is use-fixtures]]))

(def ^:private z lvl/zero)
(defn- cst [s] (e/const' (nm/from-string s) []))
(def ^:private N (cst "Nat"))
(def ^:private LN (e/app (e/const' (nm/from-string "List") [z]) N))
(def ^:private ready (atom false))

(use-fixtures :once
  (fn [f]
    (if @test-env/init-full-env
      (do (reset! a/ansatz-env @test-env/init-full-env)
          (binding [a/*verbose* false] (w/install!) (km/install!) (rl/install!))
          (reset! ready true) (f))
      (do (println "SKIP sum-linearity: no Init env") (f)))))

(deftest linearity-laws-installed
  (when @ready
    ;; install! kernel-checks each on admit, so presence == verified
    (doseq [n ["List.sum_map_add_distrib" "List.sum_map_zero"
               "List.foldl_add_pull" "List.sum_map_mul_const"]]
      (is (some? (env/lookup (a/env) (nm/from-string n)))
          (str n " admitted (kernel-checked by install!)")))))

(deftest add-distrib-runs
  (when @ready
    ;; ∑(map (λx. x + x*2) xs)  ==  ∑(map id xs) + ∑(map (λx.x*2) xs)  — the content of sum_map_add_distrib
    (let [xs (e/fvar 1)
          foldl0 (fn [l] (e/app* (e/const' (nm/from-string "List.foldl") [z z]) N N (cst "Nat.add") (cst "Nat.zero") l))
          mapN (fn [fexpr l] (e/app* (e/const' (nm/from-string "List.map") [z z]) N N fexpr l))
          idf  (e/lam "x" N (e/bvar 0) :default)
          dbl  (e/lam "x" N (e/app* (cst "Nat.mul") (e/bvar 0) (e/lit-nat 2)) :default)
          sumf (e/lam "x" N (e/app* (cst "Nat.add") (e/bvar 0) (e/app* (cst "Nat.mul") (e/bvar 0) (e/lit-nat 2))) :default)
          lhs  (foldl0 (mapN sumf xs))
          rhs  (e/app* (cst "Nat.add") (foldl0 (mapN idf xs)) (foldl0 (mapN dbl xs)))
          lam  (fn [t] (e/lam "xs" LN (e/abstract1 t 1) :default))
          fl   (eval (a/ansatz->clj (a/env) (lam lhs) []))
          fr   (eval (a/ansatz->clj (a/env) (lam rhs) []))]
      (doseq [xs [[1 2 3] [] [5 7 9 11] (range 12)]]
        (is (= (long (fl xs)) (long (fr xs)) (long (reduce + 0 (map #(+ % (* % 2)) xs))))
            (str "∑(x+2x) = ∑x + ∑2x on " (count xs)))))))
