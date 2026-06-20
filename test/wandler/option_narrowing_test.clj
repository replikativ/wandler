(ns wandler.option-narrowing-test
  "Option-1: nil/Option-truthiness via macroexpand-first + occurrence-typing NARROWING.
   if-let/if-some/when-let are clojure.core macros; the macroexpand-1 fallback expands them
   to `(if <var-or-(nil? var)> …)`, and the `if` elaborator's third path detects an
   Option-typed condition variable and compiles to `Option.elim`, NARROWING the variable to
   its unwrapped element type in the present branch (at runtime Option is value-or-nil, so
   the narrowed value is the same — a type-level unwrap). when-let / 2-arg forms return
   Option (present → some, absent → none). Also covers standalone nil?/some? and hand-written
   (if (nil? v) …). See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.clean.surface.collections :as coll]
            [wandler.clean.surface.option :as option]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest option-truthiness-narrowing
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      ;; Re-install the Option-narrowing nil?/some? this test depends on, so it is robust to a prior
      ;; test having installed the dynamic-EDN Value nil?/some? into the process-global registry
      ;; (the Value handlers throw on a non-Value operand). Don't rely on load-order.
      (option/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn nz-iflet  [xs :- (List Nat)] Nat (if-let [x (first xs)] (+ x 1) 0)))
        (eval '(ansatz.core/defn nz-ifsome [xs :- (List Nat)] Nat (if-some [x (first xs)] (* x 2) 99)))
        (eval '(ansatz.core/defn nz-whenlet [xs :- (List Nat)] (Option Nat) (when-let [x (first xs)] (+ x 100))))
        (eval '(ansatz.core/defn nz-some? [xs :- (List Nat)] Bool (some? (first xs))))
        (eval '(ansatz.core/defn nz-nil?  [xs :- (List Nat)] Bool (nil? (first xs))))
        ;; hand-written nil-check (not a macro) — narrows too
        (eval '(ansatz.core/defn nz-hand [xs :- (List Nat)] Nat
                 (let [h (first xs)] (if (nil? h) 0 (+ h 5))))))
      ;; if-let / if-some bind the UNWRAPPED value in the present branch
      (is (= 8  ((resolve 'nz-iflet)  [7 8])) "if-let present: x is unwrapped Nat")
      (is (= 0  ((resolve 'nz-iflet)  []))    "if-let absent → else")
      (is (= 14 ((resolve 'nz-ifsome) [7]))   "if-some present (nil? → swapped branches)")
      (is (= 99 ((resolve 'nz-ifsome) []))    "if-some absent → else")
      ;; when-let returns Option (present → some, absent → none)
      (is (= 107 ((resolve 'nz-whenlet) [7])) "when-let present → some")
      (is (nil? ((resolve 'nz-whenlet) []))   "when-let absent → nil")
      ;; standalone nil?/some? on Option → isSome/isNone
      (is (true?  ((resolve 'nz-some?) [7])) "some? present")
      (is (false? ((resolve 'nz-some?) []))  "some? absent")
      (is (true?  ((resolve 'nz-nil?)  []))  "nil? absent")
      ;; hand-written nil-check narrows the same way
      (is (= 12 ((resolve 'nz-hand) [7])) "hand (if (nil? h) 0 (+ h 5)): h narrowed")
      (is (= 0  ((resolve 'nz-hand) []))  "hand absent"))
    (do (println "SKIP option-truthiness-narrowing: no Init env") (is true))))
