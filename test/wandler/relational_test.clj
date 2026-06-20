(ns wandler.relational-test
  "Relational / ordering vocabulary (distinct/sort/sort-by) over List compile,
   verify, and run. Gated on an Init env."
  (:require [ansatz.core :as a]
            [wandler.clean.surface.collections :as coll]
            [wandler.clean.surface.relational :as rel]
            [wandler.kmap :as kmap]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- verified? [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (let [tc (doto (TypeChecker. (a/env)) (.setFuel 50000000))]
      (.isDefEq tc (.inferType tc (.value ci)) (.type ci)))))

(deftest relational-ops-verify-and-run
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (rel/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn rel-distinct [xs :- (List Nat)] (List Nat) (distinct xs)))
        (eval '(ansatz.core/defn rel-sort     [xs :- (List Nat)] (List Nat) (sort xs)))
        (eval '(ansatz.core/defn rel-sortby   [xs :- (List Nat)] (List Nat) (sort-by (fn [x] (+ x 1)) xs))))
      ;; all kernel-verified
      (is (true? (verified? "rel-distinct")))
      (is (true? (verified? "rel-sort")))
      (is (true? (verified? "rel-sortby")))
      ;; and the compiled runtime computes the right thing
      (is (= [3 1 2] ((resolve 'rel-distinct) (list 3 1 3 2 1))))
      (is (= [1 2 3 4 5] (vec ((resolve 'rel-sort) (list 3 1 2 5 4)))))
      (is (= [1 2 3] (vec ((resolve 'rel-sortby) (list 3 1 2))))))
    (do (println "SKIP relational-ops-verify-and-run: no Init env") (is true))))

(deftest group-by-and-to-map-verify-and-run
  ;; group-by is verified BY CONSTRUCTION (foldl of the proven Map.insert); ->map
  ;; materializes the verified assoc-list to an idiomatic Clojure map at the edge.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (coll/install!) (rel/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn rel-gb  [xs :- (List Nat)] (Map Nat (List Nat))
                 (group-by (fn [x] x) xs)))
        (eval '(ansatz.core/defn rel-gbm [xs :- (List Nat)] (List (Prod Nat (List Nat)))
                 (->map (group-by (fn [x] x) xs)))))
      (is (true? (verified? "rel-gb")))
      (is (true? (verified? "rel-gbm")))
      ;; the verified Map (assoc-list of [k group] pairs) groups correctly
      (is (= [[1 '(1 1 1)] [2 '(2 2)] [3 '(3)]]
             (vec ((resolve 'rel-gb) (list 1 2 1 3 2 1)))))
      ;; ->map yields a real Clojure map at the boundary
      (is (= {1 '(1 1 1) 2 '(2 2) 3 '(3)}
             ((resolve 'rel-gbm) (list 1 2 1 3 2 1)))))
    (do (println "SKIP group-by-and-to-map-verify-and-run: no Init env") (is true))))

(deftest join-verify-and-run
  ;; inner join, verified by construction (group ys by key, lookup per x).
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!) (coll/install!) (rel/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn rel-join [xs :- (List Nat), ys :- (List Nat)] (List (Prod Nat Nat))
                 (join (fn [x] x) (fn [y] y) xs ys))))
      (is (true? (verified? "rel-join")))
      ;; every (x,y) with x=y: 2 matches both 2s in ys, 3 matches, 1 & 4 unmatched
      (is (= [[2 2] [2 2] [3 3]]
             (sort ((resolve 'rel-join) (list 1 2 3) (list 2 2 3 4))))))
    (do (println "SKIP join-verify-and-run: no Init env") (is true))))
