(ns ansatz.surface-query-test
  "STEP 1 of the optimizer-term integration, completed: a NORMAL Clojure relational query — written with
   `for` / `=` / `count` / `reduce` over typed record lists — elaborates through `a/defn` to a KERNEL-VERIFIED
   term (a/defn kernel-checks every definition), is optimized (`optimize-body`), codegens to a Clojure fn,
   and EXECUTES — agreeing with the runtime `ansatz.semiring` FAQ engine. So the general surface→kernel→
   optimize→run path is the EXISTING `a/defn` elaborator (its `for`/`join` desugaring); the manual
   `ansatz.faq-plan` is the cost-directed factorization slice on top. The aggregation (`count` = ⊕1,
   `reduce +` = weighted ⊕) IS the semiring sum. See [[programming-model-4-structures]], PROGRAMMING_MODEL.md §13.

   A relation is a `(List (Prod Nat Nat))` = rows `[key value]`; the join is on `first` (the key)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.kmap :as km]
            [ansatz.rel-laws :as rl]
            [ansatz.collections :as coll]
            [ansatz.relational]                         ; registers the `join` surface elaborator (load side-effect)
            [ansatz.semiring :as sr]
            [ansatz.test-env :as test-env]))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv) (km/install!) (rl/install!) (coll/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(def ^:private CUSTS [[1 10] [2 20] [3 30]])               ; [cid tier]
(def ^:private ORDS  [[1 100] [1 200] [2 50] [3 5] [3 6]]) ; [cid amount] — 5 matching pairs, Σ amount = 361

;; the SAME queries computed by the runtime semiring engine (rel-join = ⊗ on matching keys, sum = ⊕)
(defn- sr-count [custs ords]
  (reduce + 0 (vals (sr/rel-join sr/counting :cid :id
                      (into {} (map-indexed (fn [i [c _]] [{:cid c :idx i} 1]) ords))
                      (into {} (map (fn [[k _]] [{:id k} 1]) custs))))))
(defn- sr-sum [custs ords]
  (reduce + 0 (vals (sr/rel-join sr/counting :cid :id
                      (into {} (map-indexed (fn [i [c amt]] [{:cid c :idx i} amt]) ords))
                      (into {} (map (fn [[k _]] [{:id k} 1]) custs))))))

(deftest surface-relational-query-is-the-certified-path
  (when (ready?)
    ;; a/defn returns the interned var; capture + invoke it (the symbol isn't resolvable at compile time)
    (let [jcount (eval '(ansatz.core/defn jcount [xs :- (List (Prod Nat Nat)) ys :- (List (Prod Nat Nat))] Nat
                          (count (for [x xs y ys :when (= (first x) (first y))] (first x)))))
          jsum   (eval '(ansatz.core/defn jsum   [xs :- (List (Prod Nat Nat)) ys :- (List (Prod Nat Nat))] Nat
                          (reduce + 0 (for [x xs y ys :when (= (first x) (first y))] (second y)))))]
      (testing "Clojure for/join queries elaborate + kernel-verify + run (a/defn checks every def)"
        (is (var? jcount)) (is (var? jsum))
        (is (= 5 (jcount CUSTS ORDS)) "5 matching (customer, order) pairs")
        (is (= 361 (jsum CUSTS ORDS)) "Σ order amount over the join"))
      (testing "the certified surface query and the runtime semiring engine agree (one query, two engines)"
        (is (= (jcount CUSTS ORDS) (sr-count CUSTS ORDS)) "count: a/defn kernel plan == sr rel-join")
        (is (= (jsum CUSTS ORDS) (sr-sum CUSTS ORDS))     "sum:   a/defn kernel plan == sr rel-join"))
      (testing "the path is genuinely kernel-CHECKED: an ill-typed query is REJECTED at definition"
        (is (thrown? Throwable
              (eval '(ansatz.core/defn badq [xs :- (List Nat)] Nat (mapv inc xs))))  ; body : List Nat ≠ Nat
            "a/defn refuses a body whose type doesn't match the declared return type")))))
