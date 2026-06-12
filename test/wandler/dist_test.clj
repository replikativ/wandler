(ns wandler.dist-test
  "FinSet / FinDist (wandler.inference.dist) — the monad view of the semiring's `Rel A S`. Demonstrates: (1) a FinDist
   probabilistic program (Bernoulli edges + Boolean reachability) whose marginal AGREES with the provenance
   semiring → WMC path (same answer, different route); (2) FinSet nondeterminism via the set monad; (3) the
   monad laws for both instances. All pure runtime — the symbolic correctness lives in the proven semiring."
  (:require [clojure.test :refer [deftest is testing]]
            [wandler.inference.dist :as d]
            [wandler.inference.semiring :as sr]))

;; the joint FinDist of independent Bernoulli draws (a vector of outcomes), built by monadic bind
(defn- joint [ps]
  (reduce (fn [acc p] (d/dist-bind acc (fn [v] (d/dist-bind (d/bernoulli p) (fn [b] (d/dist-return (conj v b)))))))
          (d/dist-return []) ps))

(deftest findist-probabilistic-program
  (testing "a FinDist program: 1→9 via two independent 2-hop paths; P = 1−(1−.9·.8)(1−.5·.4) = 0.776"
    (let [model (d/fin-map sr/probability
                           (fn [[e12 e29 e13 e39]] (or (and e12 e29) (and e13 e39)))
                           (joint [0.9 0.8 0.5 0.4]))]   ; FinDist Bool
      (is (< (Math/abs (- (get model true) 0.776)) 1e-9) "the FinDist marginal P(reachable) = 0.776")
      (is (< (Math/abs (- (d/prob model true?) 0.776)) 1e-9) "…also via prob")
      (testing "and it AGREES with the provenance semiring → WMC (the FAQ route) — monad ≡ sum-product"
        (let [edge (sr/relation [:a :b] {[1 2] #{#{:e12}} [1 3] #{#{:e13}} [2 9] #{#{:e29}} [3 9] #{#{:e39}}})
              formula (get (:rel (sr/q {:find [:x :y] :where [[:edge :x :m] [:edge :m :y]]} sr/provenance {:edge edge})) {:x 1 :y 9})]
          (is (< (Math/abs (- (get model true) (sr/wmc {:e12 0.9 :e29 0.8 :e13 0.5 :e39 0.4} formula))) 1e-9)
              "FinDist monad marginal == provenance → WMC == 0.776"))))))

(deftest finset-nondeterminism
  (testing "FinSet = the powerset monad: graph reachability by binding the step relation"
    (let [edges {1 #{2 3} 2 #{9} 3 #{9} 9 #{}}
          step  (fn [a] (d/fset (get edges a #{})))]                   ; a ↦ its neighbours (a FinSet)
      (is (= #{2 3} (d/to-set (d/fset-bind (d/singleton 1) step))) "1-hop from 1 = {2,3}")
      (is (= #{9}   (d/to-set (d/fset-bind (d/fset-bind (d/singleton 1) step) step))) "2-hop from 1 = {9}"))))

(deftest monad-laws
  (testing "left-unit (bind (return a) f = f a) and right-unit (bind m return = m), both instances"
    (let [f (fn [a] (d/bernoulli (/ a 10.0)))
          g (fn [a] (d/fset [(inc a) (dec a)]))]
      (is (= (f 7) (d/dist-bind (d/dist-return 7) f)) "FinDist left-unit")
      (is (= (g 3) (d/fset-bind (d/singleton 3) g))   "FinSet left-unit")
      (is (= {:a 0.3 :b 0.7} (d/dist-bind {:a 0.3 :b 0.7} d/dist-return)) "FinDist right-unit")
      (is (= (d/fset [:x :y]) (d/fset-bind (d/fset [:x :y]) d/singleton)) "FinSet right-unit"))))
