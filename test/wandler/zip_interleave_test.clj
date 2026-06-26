(ns wandler.zip-interleave-test
  "Two-input surface verbs zip / interleave (Tier-1 surface desugars onto Init ops):
   zip → List.zip α β; interleave → mapcat over zip (flatten each Prod pair). Each case is
   compiled + kernel-certified through a/defn and checked against clojure.core ground truth."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(def ^:private as '(1 2 3 4))
(def ^:private bs '(10 20 30 40))

(def ^:private cases
  ;; [name [param-types] ret body ground-truth-fn]
  [['zi-interleave '[as :- (List Nat) bs :- (List Nat)] '(List Nat)
    '(interleave as bs) #(interleave %1 %2)]
   ['zi-interleave-sum '[as :- (List Nat) bs :- (List Nat)] 'Nat
    '(reduce + 0 (interleave as bs)) #(reduce + 0 (interleave %1 %2))]
   ['zi-zip-fst '[as :- (List Nat) bs :- (List Nat)] '(List Nat)
    '(map (fn [p] (first p)) (zip as bs)) #(mapv first (map vector %1 %2))]
   ['zi-zip-dot '[as :- (List Nat) bs :- (List Nat)] 'Nat
    '(reduce + 0 (map (fn [p] (* (first p) (second p))) (zip as bs)))
    #(reduce + 0 (map (fn [[a b]] (* a b)) (map vector %1 %2)))]])

(defn- cmp [got want]
  (if (or (sequential? got) (sequential? want)) (= (seq got) (seq want)) (= got want)))

(deftest zip-interleave-differential
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (w/install!)
      (doseq [[n params ret body truth] cases]
        (binding [a/*verbose* false]
          (eval (list 'ansatz.core/defn n params ret body)))
        (let [f @(resolve n)
              got ((f as) bs)
              want (truth as bs)]
          (is (cmp got want) (str n ": " (pr-str got) " ≠ clojure.core " (pr-str want))))))
    (println "zip-interleave: no Init env, skipping")))
