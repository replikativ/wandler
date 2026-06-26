(ns wandler.cse-test
  "SHARED-SUBTREE PLANNING (common-subexpression elimination). A dataflow TREE that uses the same
   BARRIER subexpression (a sort / group-by / join — something fusion cannot inline) for two consumers
   recomputes it once per consumer. CSE hoists it into a `let` so it runs ONCE. The certificate is
   `Eq.refl`: `(f S S)` and `(let s := S in f s s)` are ZETA-definitionally equal, so no law/search is
   needed; the kernel gate accepts the refl proof and ansatz.codegen lowers `:let` to a sharing Clojure
   `let`. CSE runs AFTER fusion and only on barriers — streaming map/filter is left to fusion (cheaper
   to fuse a cheap filter into each consumer than to materialize+share it).

   Each case: ordinary Clojure through a/defn, checked against clojure.core (value), with w/explain
   asserting CSE did / did not fire as intended."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is use-fixtures]]))

(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (w/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest shared-barrier-is-hoisted-once
  (if-not (ready?)
    (is true "skipped — no Init env")
    (do
      ;; a shared SORT consumed two ways → hoisted into a `let`, computed once
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn cse-sort [xs :- (List Nat)] Nat
                 (+ (reduce + 0 (sort xs))
                    (reduce + 0 (map (fn [x] (* x 2)) (sort xs)))))))
      (let [ex (w/explain "cse-sort")
            truth (fn [xs] (+ (reduce + 0 (sort xs)) (reduce + 0 (map #(* % 2) (sort xs)))))
            inp '(3 1 2 5 4)]
        (is (:verified? ex) "CSE rewrite kernel-certified (Eq.refl / zeta)")
        (is (contains? (set (:rewrites ex)) :cse) "the shared sort was hoisted (CSE fired)")
        (is (= (long ((resolve 'cse-sort) inp)) (long (truth inp))) "value = clojure.core ground truth")))))

(deftest streaming-share-is-fused-not-hoisted
  (if-not (ready?)
    (is true "skipped — no Init env")
    (do
      ;; a shared FILTER is cheap and fusable — fusion inlines it into each consumer; CSE stays out
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn cse-filter [xs :- (List Nat)] Nat
                 (+ (reduce + 0 (map (fn [x] (* x 2)) (filter (fn [x] (< 2 x)) xs)))
                    (reduce + 0 (map (fn [x] (* x 3)) (filter (fn [x] (< 2 x)) xs)))))))
      (let [ex (w/explain "cse-filter")
            truth (fn [xs] (+ (reduce + 0 (map #(* % 2) (filter #(< 2 %) xs)))
                              (reduce + 0 (map #(* % 3) (filter #(< 2 %) xs)))))
            inp '(1 2 3 4 5)]
        (is (:verified? ex))
        (is (not (contains? (set (:rewrites ex)) :cse)) "streaming filter is fused, not CSE'd")
        (is (= (long ((resolve 'cse-filter) inp)) (long (truth inp))) "value = clojure.core ground truth")))))
