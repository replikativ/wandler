(ns wandler.foreign-test
  "Trusted FOREIGN functions — the gradual escape hatch. An arbitrary Clojure fn asserted
   at a kernel type (a/foreign → axiom, trusted) composes into a verified, optimized,
   FUSED pipeline: the optimizer's SOAC/relational laws are parametric in the element
   functions, so the structure is kernel-certified while the function stays a blackbox.
   This is 'verify the algebra; the functions are parameters.'"
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest foreign-fns-fuse-and-run
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (w/install!)
      (binding [a/*verbose* false]
        ;; arbitrary Clojure, asserted Nat→Nat (body NOT a kernel term — trusted)
        (eval '(ansatz.core/foreign tripleq [x :- Nat] Nat (fn [x] (* 3 x))))
        (eval '(ansatz.core/foreign evenq [x :- Nat] Bool (fn [x] (even? x))))
        ;; foreign fns inside a FUSED map∘filter pipeline
        (eval '(ansatz.core/defn fpq [xs :- (List Nat)] (List Nat)
                 (mapv (fn [x] (tripleq x)) (filterv (fn [x] (evenq x)) xs)))))
      ;; the structure fused + kernel-certified, despite trusted element fns
      (let [ex (w/explain 'fpq)]
        (is (true? (:verified? ex)) "pipeline over foreign fns kernel-certified")
        (is (true? (:changed? ex))  "fused")
        (is (= ["List.map_filter_filterMap"] (:rewrites ex)) "map∘filter → filterMap"))
      ;; and it computes the right thing: keep evens, triple them
      (is (= '(6 12) (seq ((resolve 'fpq) '(2 5 4 7)))))
      ;; direct call of the foreign fn works too (it IS the Clojure fn)
      (is (= 15 ((resolve 'tripleq) 5))))
    (println "foreign-test: no Init env, skipping")))
