(ns ansatz.let-cond-test
  "let / cond surface forms, built on fvar-first elaboration. `let` infers each
   value's type (no annotation) and compiles to a kernel letE; `cond` desugars to
   nested if. Gated on an Init env."
  (:require [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- verified? [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (let [tc (doto (TypeChecker. (a/env)) (.setFuel 50000000))]
      (.isDefEq tc (.inferType tc (.value ci)) (.type ci)))))

(defn- body-str [nm]
  (e/->string (.value (env/lookup (a/env) (name/from-string nm)))))

(deftest let-infers-value-type-and-verifies
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn lc-let [n :- Nat] Nat
                 (let [x (Nat.add n n)] (Nat.add x x)))))
      (is (true? (verified? "lc-let")))
      ;; compiled to a kernel let (Lean letE), value type inferred (no annotation)
      (is (re-find #"\(let " (body-str "lc-let"))))
    (do (println "SKIP let-infers-value-type-and-verifies: no Init env") (is true))))

(deftest nested-let-verifies
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn lc-let2 [n :- Nat] Nat
                 (let [x (Nat.add n n)
                       y (Nat.add x n)]
                   (Nat.add x y)))))
      (is (true? (verified? "lc-let2"))))
    (is true)))

(deftest cond-desugars-to-if
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn lc-cond [b :- Bool] Nat
                 (cond b 1 :else 2))))
      (is (true? (verified? "lc-cond")))
      ;; lowered through `if` → Bool.rec
      (is (re-find #"Bool\.rec" (body-str "lc-cond"))))
    (is true)))

(deftest let-binds-a-projection-then-rebuilds
  ;; let + records: bind a nested projection, reuse it — the kind of idiomatic body
  ;; fvar-first unlocks.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/structure LCAddr [] (zip Nat) (num Nat)))
        (eval '(ansatz.core/defn lc-swap [r :- LCAddr] LCAddr
                 (let [z (:zip r)] (LCAddr.mk (:num r) z)))))
      (is (true? (verified? "lc-swap"))))
    (is true)))

;; ── relocated from ansatz.core-test (a/define-verified engine now lives in ansatz.pipeline) ──
(deftest defn-engine-id-add-double
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (binding [a/*verbose* false]
      (let [id  (a/define-verified 'id-nat '[n Nat] 'Nat 'n)
            add (a/define-verified 'add-nat '[a Nat b Nat] 'Nat '(+ a b))
            dbl (a/define-verified 'double '[n :- Nat] 'Nat '(+ n n))]
        (is (fn? id)) (is (= 42 (id 42))) (is (= 0 (id 0)))
        (is (= 5 ((add 2) 3))) (is (= 0 ((add 0) 0)))
        (is (= 10 (dbl 5)))))))
