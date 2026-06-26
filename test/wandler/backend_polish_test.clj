(ns wandler.backend-polish-test
  "Backend-dev rough-edge fixes #2–4 from the stress findings:
   #2 `=` is an alias for `==` (equality-against-a-literal — the most common filter).
   #3 `count` over a malli `:set` field (a refined Subtype(List, Nodup)) coerces to the base list.
   #4 a pipeline over an `(LSeq A)` PARAMETER — the dev's OWN lazy seq / data feed — routes to the stream
      verbs (windowed map/take), forcing only the window; a running scan over an LSeq gives a clear error."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.exec.mode :as mode]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env) (wc/install!) (wc/install-laws!) (mode/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))
(defn- malli? [] (try (require 'malli.core) true (catch Throwable _ false)))

(deftest eq-alias
  (when (ready?)
    (testing "#2 `(= a b)` is the Bool equality filter (alias for ==)"
      (eval '(ansatz.core/defn bp-eqi [xs :- (List Nat)] (List Nat) (filter (fn [x] (= x 3)) xs)))
      (is (= [3 3] (mapv long ((deref (resolve 'bp-eqi)) '(1 2 3 3 4)))))
      (when (malli?)
        (eval (list (symbol "malli.core" "=>") 'bp-eqs
                    [:=> [:cat [:sequential [:map [:k :string] [:n [:int {:min 0}]]]]] :int]))
        (eval '(ansatz.core/defn bp-eqs [xs]
                 (reduce + 0 (map (fn [x] (:n x)) (filter (fn [x] (= (:k x) "active")) xs)))))
        (is (= 5 (long ((deref (resolve 'bp-eqs)) [{:k "active" :n 5} {:k "idle" :n 9}])))
            "equality against a string literal on a record field")))))

(deftest set-field-count
  (when (and (ready?) (malli?))
    (testing "#3 count over a :set field (refined Subtype) coerces to the base list"
      (eval (list (symbol "malli.core" "=>") 'bp-set
                  [:=> [:cat [:sequential [:map [:tags [:set :int]]]]] :int]))
      (eval '(ansatz.core/defn bp-set [xs] (reduce + 0 (map (fn [x] (count (:tags x))) xs))))
      (is (= 4 (long ((deref (resolve 'bp-set)) [{:tags #{1 2 3}} {:tags #{4}}])))
          "Σ |tags| = 3 + 1"))))

(deftest lseq-param-stream
  (when (ready?)
    (testing "#4 windowed map over an (LSeq A) PARAMETER — the dev's own (possibly-infinite) lazy seq"
      (eval '(ansatz.core/defn bp-win [feed :- (LSeq Nat)] (List Nat)
               (take 3 (map (fn [x] (Nat.mul x x)) feed))))
      (is (= [1 4 9] (mapv long ((deref (resolve 'bp-win)) (map inc (range)))))
          "forces only the 3-element window of an INFINITE lazy seq"))
    (testing "chained stream maps over the feed"
      (eval '(ansatz.core/defn bp-chain [feed :- (LSeq Nat)] (List Nat)
               (take 3 (map (fn [x] (+ x 1)) (map (fn [x] (* x 2)) feed)))))
      (is (= [1 3 5] (mapv long ((deref (resolve 'bp-chain)) (range))))))
    (testing "a running scan over an LSeq is refused cleanly (LSeq.scan not yet wired)"
      (let [err (try (eval '(ansatz.core/defn bp-badscan [feed :- (LSeq Nat)] (List Nat)
                              (take 4 (reductions + 0 feed))))
                     nil (catch Throwable t (loop [c t] (if-let [n (.getCause c)] (recur n) (.getMessage c)))))]
        (is (and err (re-find #"reductions" err)) (str "clear message, got: " err))))
    (testing "a List param is NOT mis-routed to the stream verbs (regression)"
      (eval '(ansatz.core/defn bp-list [xs :- (List Nat)] Nat (reduce + 0 (map (fn [x] (* x x)) xs))))
      (is (= 14 (long ((deref (resolve 'bp-list)) '(1 2 3))))))))
