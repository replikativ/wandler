(ns wandler.membership-normalization-test
  "Normalization (#73) + elaboration breadth (#72): membership written several idiomatic Clojure ways
   all NORMALIZE to List.elem, so they ALL fire the verified SEMIJOIN (index probe) — addressing
   'a large class of Clojure functions, written many ways'. Plus some/every? as general ∃/∀."
  (:require [wandler.core]
            [ansatz.core :as a]
            [wandler.clean.surface.collections :as coll]
            [wandler.clean.surface.relational :as rel]
            [wandler.laws.relational :as rl]
            [wandler.kmap :as kmap]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest membership-spellings-all-fire-the-semijoin
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!) (kmap/install!) (rel/install!) (rl/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn mn-member   [xs :- (List Nat), ys :- (List Nat)] (List Nat) (filterv (fn [x] (member x ys)) xs)))
        (eval '(ansatz.core/defn mn-contains  [xs :- (List Nat), ys :- (List Nat)] (List Nat) (filterv (fn [x] (contains? ys x)) xs)))
        (eval '(ansatz.core/defn mn-some-eq   [xs :- (List Nat), ys :- (List Nat)] (List Nat) (filterv (fn [x] (some (fn [y] (== x y)) ys)) xs))))
      ;; all three spellings normalize to List.elem → the semijoin fires, certified, and runs the same
      (doseq [f '[mn-member mn-contains mn-some-eq]]
        (is (= ["List.elem_filter_eq_index_probe"] (:rewrites (wandler.core/explain (name f)))) (str f " fires the semijoin"))
        (is (true? (:verified? (wandler.core/explain (name f)))) (str f " certified"))
        (is (= [2 4] (vec ((resolve f) (list 1 2 3 4) (list 2 4 6)))) (str f " runs correctly"))))
    (do (println "SKIP membership normalization: no Init env") (is true))))

(deftest some-every-as-general-quantifiers
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!) (kmap/install!) (rel/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn mn-every [ys :- (List Nat)] Bool (every? (fn [y] (Nat.ble 1 y)) ys)))
        (eval '(ansatz.core/defn mn-some  [ys :- (List Nat)] Bool (some  (fn [y] (Nat.ble 5 y)) ys))))
      (is (true?  ((resolve 'mn-every) (list 1 2 3))) "every? y≥1 over [1 2 3]")
      (is (false? ((resolve 'mn-every) (list 0 2 3))) "every? fails when a 0 present")
      (is (false? ((resolve 'mn-some)  (list 1 2 3))) "some y≥5 over [1 2 3] is false")
      (is (true?  ((resolve 'mn-some)  (list 1 6 3))) "some y≥5 true when a 6 present"))
    (do (println "SKIP some/every: no Init env") (is true))))

(deftest more-membership-spellings-and-verbs
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!) (kmap/install!) (rel/install!) (rl/install!)
      (binding [a/*verbose* false]
        ;; two more membership spellings → semijoin
        (eval '(ansatz.core/defn mn-some-set     [xs :- (List Nat), ys :- (List Nat)] (List Nat) (filterv (fn [x] (some #{x} ys)) xs)))
        (eval '(ansatz.core/defn mn-contains-set [xs :- (List Nat), ys :- (List Nat)] (List Nat) (filterv (fn [x] (contains? (set ys) x)) xs)))
        ;; new verbs
        (eval '(ansatz.core/defn mn-nth   [xs :- (List Nat)] Nat (nth xs 1 99)))
        (eval '(ansatz.core/defn mn-range [n :- Nat] (List Nat) (mapv (fn [x] (Nat.mul x x)) (range n)))))
      (doseq [f '[mn-some-set mn-contains-set]]
        (is (= ["List.elem_filter_eq_index_probe"] (:rewrites (wandler.core/explain (name f)))) (str f " (set spelling) fires the semijoin"))
        (is (= [2 4] (vec ((resolve f) (list 1 2 3 4) (list 2 4 6)))) (str f " runs")))
      (is (= 20 ((resolve 'mn-nth) (list 10 20 30))) "nth with default")
      (is (= 99 ((resolve 'mn-nth) (list 10))) "nth out-of-bounds → default")
      (is (= [0 1 4 9] (vec ((resolve 'mn-range) 4))) "range feeds a map pipeline"))
    (do (println "SKIP more spellings/verbs: no Init env") (is true))))
