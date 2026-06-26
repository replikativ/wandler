(ns wandler.seq-ops-test
  "More clojure.core sequence vocabulary — take/drop/take-while/drop-while/first/last/rest
   — each mapped to its Lean List op (the verified DENOTATION) and lowered to the Clojure
   runtime op. take/take-while/drop are lazy in Clojure, so a bounded terminal like
   (take n …) makes an INFINITE lazy pipeline fully CONSUMABLE: fold over (take 5 …) of an
   infinite seq terminates. Closes the streaming story. See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.surface.collections :as coll]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest seq-vocabulary-and-streaming-closure
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn s-take  [xs :- (List Int)] (List Int) (take 3 xs)))
        (eval '(ansatz.core/defn s-drop  [xs :- (List Int)] (List Int) (drop 2 xs)))
        (eval '(ansatz.core/defn s-tw    [xs :- (List Int)] (List Int) (take-while (fn [x] (< x 30)) xs)))
        (eval '(ansatz.core/defn s-first [xs :- (List Int)] (Option Int) (first xs)))
        (eval '(ansatz.core/defn s-last  [xs :- (List Int)] (Option Int) (last xs)))
        ;; the streaming closure: fold over a bounded prefix of an INFINITE seq
        (eval '(ansatz.core/defn s-sum5  [xs :- (List Int)] Int
                 (reduce (fn [acc x] (Int.add acc x)) 0 (take 5 xs))))
        (eval '(ansatz.core/defn s-sum5m [xs :- (List Int)] Int
                 (reduce (fn [acc x] (Int.add acc x)) 0 (take 5 (mapv (fn [x] (* x 2)) xs))))))
      ;; eager (vector) cases
      (is (= [10 20 30] ((resolve 's-take) [10 20 30 40 50])) "take 3")
      (is (= [30 40 50] ((resolve 's-drop) [10 20 30 40 50])) "drop 2")
      (is (= [10 20]    ((resolve 's-tw)   [10 20 30 40]))    "take-while < 30")
      (is (= 7 ((resolve 's-first) [7 8 9])) "first")
      (is (= 9 ((resolve 's-last)  [7 8 9])) "last")
      ;; THE STREAMING CLOSURE — these would previously HANG (infinite seq forced)
      (is (= 15 ((resolve 's-sum5)  (map inc (range)))) "sum of first 5 of an infinite seq = 1+2+3+4+5")
      (is (= 30 ((resolve 's-sum5m) (map inc (range)))) "fused sum(take 5 (map *2)) of infinite = 2+4+6+8+10"))
    (do (println "SKIP seq-vocabulary-and-streaming-closure: no Init env") (is true))))
