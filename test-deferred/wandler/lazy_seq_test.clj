(ns wandler.lazy-seq-test
  "Lazy-sequence handling: a verified pipeline given a LAZY seq STREAMS it (preserves
   laziness) instead of forcing it eagerly — so an INFINITE lazy seq through a map/filter
   pipeline doesn't hang and can be consumed with `take`. An eager vector still maps
   eagerly to a vector (unchanged); folds over a lazy seq stream via reduce. The fusion
   laws (proven on the finite List) license this — List is the verified denotation; the
   runtime sequence representation (lazy seq / vector / array) is a codegen backend. See
   [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.collections :as coll]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest lazy-seqs-stream-not-forced
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn l-dbl  [xs :- (List Int)] (List Int) (mapv (fn [x] (* x 2)) xs)))
        ;; fused map-chain (x*2 then +1)
        (eval '(ansatz.core/defn l-chain [xs :- (List Int)] (List Int)
                 (mapv (fn [x] (+ x 1)) (mapv (fn [x] (* x 2)) xs))))
        (eval '(ansatz.core/defn l-sum  [xs :- (List Int)] Int (reduce (fn [acc x] (Int.add acc x)) 0 xs))))
      ;; (1) lazy in → lazy out, correct values
      (let [out ((resolve 'l-dbl) (map inc (range 5)))]
        (is (instance? clojure.lang.LazySeq out) "lazy input stays lazy")
        (is (= [2 4 6 8 10] out) "lazy map computes the right thing"))
      ;; (2) INFINITE lazy seq does NOT hang — streams, consumed with take
      (let [out ((resolve 'l-chain) (map inc (range)))]   ; infinite
        (is (instance? clojure.lang.LazySeq out) "infinite stays lazy")
        (is (= [3 5 7 9 11] (take 5 out)) "(x*2)+1 over infinite, take 5"))
      ;; (3) eager vector input → eager vector output (unchanged, no regression)
      (let [out ((resolve 'l-dbl) [1 2 3])]
        (is (vector? out) "vector input → vector output")
        (is (= [2 4 6] out)))
      ;; (4) fold over a lazy seq streams (reduce — no intermediate materialization)
      (is (= 5050 ((resolve 'l-sum) (map inc (range 100)))) "fold streams a lazy seq"))
    (do (println "SKIP lazy-seqs-stream-not-forced: no Init env") (is true))))
