(ns wandler.more-ops-test
  "Bare operators as fold steps + mapcat. A bare `+`/`*`/`-` passed as a reducing function
   resolves to the typed op for the ELEMENT type — so (reduce + 0 int-list) is Int.add, not
   Nat.add (users write `+`, never Int.add). mapcat → List.flatMap. See
   [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.collections :as coll]
            [wandler.relational :as rel]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest bare-ops-and-mapcat
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!) (rel/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn o-sum-i [xs :- (List Int)] Int (reduce + 0 xs)))
        (eval '(ansatz.core/defn o-prod-i [xs :- (List Int)] Int (reduce * 1 xs)))
        (eval '(ansatz.core/defn o-sum-n [xs :- (List Nat)] Nat (reduce + 0 xs)))
        (eval '(ansatz.core/defn o-mcat [xs :- (List Nat)] (List Nat)
                 (mapcat (fn [x] (cons x (cons x nil))) xs)))
        ;; map-indexed → List.mapIdx (f index elem)
        (eval '(ansatz.core/defn o-midx [xs :- (List Nat)] (List Nat)
                 (map-indexed (fn [i x] (+ i x)) xs)))
        ;; reductions → List.scanl (cumulative folds; bare-op step too)
        (eval '(ansatz.core/defn o-scan [xs :- (List Nat)] (List Nat) (reductions + 0 xs)))
        (eval '(ansatz.core/defn o-scani [xs :- (List Int)] (List Int) (reductions * 1 xs)))
        ;; dedupe → List.eraseReps (drops CONSECUTIVE duplicates)
        (eval '(ansatz.core/defn o-dedup [xs :- (List Nat)] (List Nat) (dedupe xs))))
      ;; bare + / * as a reduce STEP picks the element-typed op
      (is (= 12 ((resolve 'o-sum-i)  [3 4 5])) "(reduce + 0 …) over Int → Int.add")
      (is (= 24 ((resolve 'o-prod-i) [2 3 4])) "(reduce * 1 …) over Int → Int.mul")
      (is (= 12 ((resolve 'o-sum-n)  [3 4 5])) "Nat unaffected")
      ;; mapcat → List.flatMap
      (is (= [1 1 2 2] ((resolve 'o-mcat) [1 2])) "mapcat duplicates each element")
      ;; map-indexed → List.mapIdx
      (is (= [10 21 32] ((resolve 'o-midx) [10 20 30])) "map-indexed adds the index")
      ;; reductions → List.scanl (cumulative)
      (is (= [0 1 3 6 10] ((resolve 'o-scan) [1 2 3 4])) "reductions + : cumulative sums")
      (is (= [1 2 6 24] ((resolve 'o-scani) [2 3 4])) "reductions * over Int : cumulative products")
      ;; dedupe → List.eraseReps (consecutive, unlike distinct)
      (is (= [1 2 3 1] ((resolve 'o-dedup) [1 1 2 2 2 3 1 1])) "dedupe drops consecutive dups"))
    (do (println "SKIP bare-ops-and-mapcat: no Init env") (is true))))
