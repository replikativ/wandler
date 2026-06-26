(ns wandler.refined-filter-surface-test
  "End-to-end (a/defn → w/explain) REFINEMENT filter-elimination: a filter the element TYPE proves
   redundant is dropped, certified, written in NATURAL surface — `(<= 5 x)` / `(<= 3 (count s))` over a
   `Subtype`-refined element (the binder auto-coerces to its carrier via the elab-lam `:as-term` path).
   Covers the two fixes that make the tutorial Rung 4 real:
     1. optimize-body no longer skips the cost pass on a 1-SOAC pipeline that carries a `Subtype`;
     2. a refined SOAC binder's references coerce to `Subtype.val` (numbers AND strings: `count`→length).
   Sound: a genuinely non-redundant filter is KEPT."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.faq :as rl]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when-let [k @test-env/init-full-env]
    (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; The NATURAL predicate form (`(<= 5 x)` over a refined element) needs the ansatz `Subtype`-binder
;; coercion (elaborate.clj). When wandler runs against an older ansatz pin that predates it, the a/defn
;; fails to elaborate — detect that and SKIP rather than fail, so the test activates once the pin bumps.
;; memoized: define the probe ONCE (the immutable env rejects a duplicate name, so a per-call probe
;; would throw on the 2nd test and spuriously report the coercion missing).
(def ^:private coercion-ok?
  (delay (try (eval '(ansatz.core/defn rf_probe [xs :- (List (Subtype Nat (fn [v :- Nat] (Nat.le 1 v))))]
                       (List (Subtype Nat (fn [v :- Nat] (Nat.le 1 v))))
                       (filter (fn [x] (<= 1 x)) xs)))
              true
              (catch Throwable _ false))))
(defn- coercion? [] @coercion-ok?)

(deftest natural-numeric-refined-filter-eliminated
  (when (and (ready?) (coercion?))
    (testing "(<= 5 x) over {v:Nat // 5≤v} drops, certified, written naturally (auto Subtype.val)"
      (eval '(ansatz.core/defn rf_num [xs :- (List (Subtype Nat (fn [v :- Nat] (Nat.le 5 v))))]
               (List (Subtype Nat (fn [v :- Nat] (Nat.le 5 v))))
               (filter (fn [x] (<= 5 x)) xs)))
      (let [ex (wc/explain 'rf_num)]
        (is (:verified? ex) "the elimination is kernel-certified")
        (is (= [:filter-elim] (:rewrites ex)) "the redundant filter was dropped")))))

(deftest natural-string-refined-filter-eliminated
  (when (and (ready?) (coercion?))
    (testing "(<= 3 (count s)) over {s:String // 3≤length s} drops (count→String.length, auto-coerce)"
      (eval '(ansatz.core/defn rf_str [xs :- (List (Subtype String (fn [s :- String] (Nat.le 3 (String.length s)))))]
               (List (Subtype String (fn [s :- String] (Nat.le 3 (String.length s)))))
               (filter (fn [s] (<= 3 (count s))) xs)))
      (let [ex (wc/explain 'rf_str)]
        (is (:verified? ex) "the elimination is kernel-certified")
        (is (= [:filter-elim] (:rewrites ex)) "the redundant string-length filter was dropped")))))

(deftest non-redundant-refined-filter-kept
  (when (and (ready?) (coercion?))
    (testing "(<= 10 x) over {v // 5≤v} is NOT redundant (10>5) → kept (sound)"
      (eval '(ansatz.core/defn rf_keep [xs :- (List (Subtype Nat (fn [v :- Nat] (Nat.le 5 v))))]
               (List (Subtype Nat (fn [v :- Nat] (Nat.le 5 v))))
               (filter (fn [x] (<= 10 x)) xs)))
      (let [ex (wc/explain 'rf_keep)]
        (is (:verified? ex))
        (is (= [] (:rewrites ex)) "a meaningful filter is preserved")))))

(deftest reduce-over-refined-elements
  (when (and (ready?) (coercion?))
    (testing "reduce over a refined-element list folds over the CARRIER (map Subtype.val fuses in), runs"
      (eval '(ansatz.core/defn rf_sum [xs :- (List (Subtype Nat (fn [v :- Nat] (Nat.le 4 v))))] Nat
               (reduce + 0 xs)))
      (let [ex (wc/explain 'rf_sum)]
        (is (:verified? ex) "certified — the fold over the carrier (map Subtype.val) re-checks"))
      (is (== 25 ((resolve 'rf_sum) [5 9 4 7]))))
    (testing "filter-elim + reduce over refined compose: redundant filter dropped, sum over carrier"
      (eval '(ansatz.core/defn rf_bigsum [xs :- (List (Subtype Nat (fn [v :- Nat] (Nat.le 4 v))))] Nat
               (reduce + 0 (filter (fn [x] (<= 4 x)) xs))))
      (let [ex (wc/explain 'rf_bigsum)]
        (is (:verified? ex))
        (is (= [:filter-elim] (:rewrites ex)) "the redundant filter is eliminated"))
      (is (== 25 ((resolve 'rf_bigsum) [5 9 4 7]))))))
