(ns ansatz.seq-accessors-test
  "Clojure-matching sequence accessors: first/second/rest dispatch on the receiver — a List gives
   the head / 2nd element / tail, a Prod (a pair, sequential in Clojure) gives fst / snd. Lets the
   join/semijoin examples read as ordinary Clojure (e.g. `(first pr)` instead of `Prod.fst α β pr`)."
  (:require [ansatz.core :as a]
            [ansatz.collections :as coll]
            [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest first-second-rest-dispatch
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (binding [a/*verbose* false]
        ;; List: head / 2nd / tail
        (eval '(ansatz.core/defn sa-head [xs :- (List Nat)] (Option Nat) (first xs)))
        (eval '(ansatz.core/defn sa-2nd  [xs :- (List Nat)] (Option Nat) (second xs)))
        (eval '(ansatz.core/defn sa-rest [xs :- (List Nat)] (List Nat) (rest xs)))
        ;; Prod (pair): fst / snd
        (eval '(ansatz.core/defn sa-fsts [ps :- (List (Prod Nat Nat))] (List Nat) (mapv (fn [p] (first p)) ps)))
        (eval '(ansatz.core/defn sa-snds [ps :- (List (Prod Nat Nat))] (List Nat) (mapv (fn [p] (second p)) ps))))
      (is (= 7 ((resolve 'sa-head) (list 7 8 9))) "first on a List → head")
      (is (= 8 ((resolve 'sa-2nd)  (list 7 8 9))) "second on a List → 2nd element")
      (is (= [8 9] (vec ((resolve 'sa-rest) (list 7 8 9)))) "rest on a List → tail")
      (is (= [6 7] (vec ((resolve 'sa-fsts) [[6 1] [7 2]]))) "first on a Prod → fst")
      (is (= [1 2] (vec ((resolve 'sa-snds) [[6 1] [7 2]]))) "second on a Prod → snd"))
    (do (println "SKIP seq-accessors: no Init env") (is true))))

(deftest bare-filter-map-aliases
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (binding [a/*verbose* false]
        ;; bare `map`/`filter` (no -v) — eager, single-collection — alias mapv/filterv
        (eval '(ansatz.core/defn bfm [xs :- (List Nat)] (List Nat)
                 (map (fn [x] (Nat.succ x)) (filter (fn [x] (<= 3 x)) xs)))))
      (is (= [4 5 6] (vec ((resolve 'bfm) (list 1 2 3 4 5)))) "bare map∘filter runs"))
    (do (println "SKIP") (is true))))

(deftest vals-keys-over-maps
  ;; Track 2 breadth: vals/keys over a Map (e.g. group-by's result) → List.map snd/fst (Map.entries).
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (require 'ansatz.kmap 'ansatz.relational)
      ((resolve 'ansatz.kmap/install!)) ((resolve 'ansatz.relational/install!))
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn gbk [xs :- (List Nat)] (List Nat) (keys (group-by (fn [x] x) xs))))
        (eval '(ansatz.core/defn gbv [xs :- (List Nat)] (List (List Nat)) (vals (group-by (fn [x] x) xs)))))
      ;; the runtime Map is now a Clojure hash-map (O(1) probe); key/value ORDER is not semantically
      ;; meaningful for a Map, so assert content order-independently.
      (is (= [1 2 3] (sort ((resolve 'gbk) (list 1 2 2 3)))) "keys of a group-by Map = the distinct keys")
      (is (= #{[1] [2 2] [3]} (set (mapv vec ((resolve 'gbv) (list 1 2 2 3))))) "vals of a group-by Map = the groups"))
    (do (println "SKIP vals/keys") (is true))))

(deftest more-sequence-verbs
  ;; Track 2 breadth: reverse/concat/interpose lift to List.reverse/append/intersperse + run.
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn rv2 [xs :- (List Nat)] (List Nat) (reverse xs)))
        (eval '(ansatz.core/defn ip2 [xs :- (List Nat)] (List Nat) (interpose 0 xs)))
        (eval '(ansatz.core/defn ct2 [xs :- (List Nat), ys :- (List Nat)] (List Nat) (concat xs ys))))
      (is (= [3 2 1] (vec ((resolve 'rv2) (list 1 2 3)))) "reverse")
      (is (= [1 0 2 0 3] (vec ((resolve 'ip2) (list 1 2 3)))) "interpose")
      (is (= [1 2 3 4] (vec ((resolve 'ct2) (list 1 2) (list 3 4)))) "concat"))
    (do (println "SKIP more-verbs") (is true))))
