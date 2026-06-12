(ns wandler.threading-test
  "Threading macros + some->. ->/->> are registered threading elaborators (records.clj), so
   they desugar to nested application before the type-arrow case (type arrows use the `arrow`
   keyword). some-> rides the Option-narrowing layer: it expands to
   (let [g e] (if (nil? g) nil (-> g step))), and compile-nilable-if narrows g + returns
   Option. inc/dec map to type-inferring +1/-1. See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.collections :as coll]   ; ->/->> threading lives here now (the base ns)
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest threading-and-some->
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn th-arrow [x :- Nat] Nat (-> x inc inc inc)))
        (eval '(ansatz.core/defn th-last  [xs :- (List Nat)] Nat
                 (->> xs (mapv (fn [x] (* x 2))) (reduce + 0))))
        (eval '(ansatz.core/defn th-incdec [x :- Nat] Nat (inc (inc (dec x)))))
        ;; some-> rides the Option narrowing (present branch narrows the threaded var)
        (eval '(ansatz.core/defn th-some1 [xs :- (List Nat)] (Option Nat) (some-> (first xs) inc)))
        (eval '(ansatz.core/defn th-some2 [xs :- (List Nat)] (Option Nat) (some-> (first xs) inc inc))))
      (is (= 7 ((resolve 'th-arrow) 4))   "-> threads first-position")
      (is (= 12 ((resolve 'th-last) [1 2 3])) "->> threads last-position over a collection")
      (is (= 6 ((resolve 'th-incdec) 5))  "inc/dec → +1/-1")
      ;; some-> short-circuits on nil, threads on present
      (is (= 8 ((resolve 'th-some1) [7]))  "some-> present (one step)")
      (is (nil? ((resolve 'th-some1) [])) "some-> nil short-circuits")
      (is (= 9 ((resolve 'th-some2) [7]))  "some-> two steps")
      (is (nil? ((resolve 'th-some2) [])) "some-> two steps, nil"))
    (do (println "SKIP threading-and-some->: no Init env") (is true))))
