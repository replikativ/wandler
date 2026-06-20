(ns wandler.clean.surface.option-test
  "Phase 8.2 (clean tree) — the Option NARROWING surface. An `if` whose condition is a nil-check on an
   Option-typed VARIABLE compiles to `Option.elim` with the variable narrowed (rebound at the element
   type) in the present branch — exactly what if-let/if-some/when-let/some-> macroexpand to, so those
   idioms verify + run without special forms. Standalone nil?/some? over an Option → isNone/isSome
   (and DELEGATE for non-Option operands). Clean-tree port of wandler.clean.surface.option (copy-clean)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.test-env :as test-env]
            [wandler.clean.surface.core :as surf]))

(deftest clean-option-narrowing
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (surf/install!)
      (binding [a/*verbose* false]
        ;; if-let / if-some bind the UNWRAPPED value in the present branch (Option.elim)
        (eval '(ansatz.core/defn co-iflet  [xs :- (List Nat)] Nat (if-let  [x (first xs)] (+ x 1) 0)))
        (eval '(ansatz.core/defn co-ifsome [xs :- (List Nat)] Nat (if-some [x (first xs)] (* x 2) 99)))
        ;; when-let returns Option (present → some, absent → none)
        (eval '(ansatz.core/defn co-whenlet [xs :- (List Nat)] (Option Nat) (when-let [x (first xs)] (+ x 100))))
        ;; standalone nil?/some? over an Option value → isNone/isSome
        (eval '(ansatz.core/defn co-some? [xs :- (List Nat)] Bool (some? (first xs))))
        (eval '(ansatz.core/defn co-nil?  [xs :- (List Nat)] Bool (nil?  (first xs)))))
      (testing "if-let / if-some narrow the Option var to its unwrapped element in the present branch"
        (is (= 8  ((resolve 'co-iflet)  [7 8])) "if-let present: x is the unwrapped Nat")
        (is (= 0  ((resolve 'co-iflet)  []))    "if-let absent: else branch")
        (is (= 14 ((resolve 'co-ifsome) [7 8])) "if-some present")
        (is (= 99 ((resolve 'co-ifsome) []))    "if-some absent"))
      (testing "when-let returns an Option (present → some, absent → none/nil)"
        (is (= 107 ((resolve 'co-whenlet) [7]))  "when-let present → some")
        (is (nil? ((resolve 'co-whenlet) []))    "when-let absent → none"))
      (testing "standalone some?/nil? over an Option lower to isSome/isNone"
        (is (= true  ((resolve 'co-some?) [7])) "some? present")
        (is (= false ((resolve 'co-some?) []))  "some? absent")
        (is (= true  ((resolve 'co-nil?)  []))  "nil? absent")
        (is (= false ((resolve 'co-nil?)  [7])) "nil? present")))
    (do (println "SKIP clean-option-narrowing: no Init env") (is true))))
