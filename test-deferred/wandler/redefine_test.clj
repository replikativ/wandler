(ns wandler.redefine-test
  "Consolidation: an `a/defn` can be REDEFINED like a normal Clojure `defn` (the surface macro adds via the
   kernel's add-or-REPLACE path), instead of throwing `Constant already declared`. This removes the real
   REPL papercut behind the mis-attributed 'install! pollution ⇒ StackOverflow' folklore (install! is
   idempotent; the SOE was a self-referential `(def x (eval '(a/defn x …)))` usage trap). Kernel proof /
   `install!` paths stay strict. See docs/AGENDA.md."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv) (coll/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest a-defn-is-redefinable
  (when (ready?)
    (testing "redefining an a/defn REPLACES it (no 'Constant already declared'), like Clojure defn"
      (let [v1 (eval '(ansatz.core/defn myq [xs :- (List Nat)] Nat (reduce + 0 xs)))
            r1 (v1 [1 2 3])                                   ; sum, before redefine
            v2 (eval '(ansatz.core/defn myq [xs :- (List Nat)] Nat (count xs)))  ; SAME name, new body — must not throw
            r2 (v2 [1 2 3])]                                  ; count, after redefine
        (is (= 6 r1) "first definition computes the sum")
        (is (= 3 r2) "redefinition computes the count — the replace worked, no throw")
        (is (some? (kenv/lookup (a/env) (nm "myq"))) "the kernel constant is present (now the new body)")))
    (testing "redefining is idempotent under repetition (kernel re-checks each time)"
      (is (= 3 ((eval '(ansatz.core/defn myq2 [xs :- (List Nat)] Nat (count xs))) [9 9 9])))
      (is (= 3 ((eval '(ansatz.core/defn myq2 [xs :- (List Nat)] Nat (count xs))) [9 9 9]))
          "second identical redefinition also succeeds (no duplicate-declaration error)"))))
