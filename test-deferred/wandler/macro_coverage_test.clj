(ns wandler.macro-coverage-test
  "Clojure MACRO coverage. sexp->ansatz sees raw source (a/defn quotes the body), so we
   handle a fixed set of special forms ourselves and macroexpand-ONCE-and-retry anything
   else that's a Clojure macro — so the derived clojure.core conditional/binding macros
   (or/and/if-not/…) work for free (they expand to let*/if/do/not, which we handle).
   Macros that rely on nil/TRUTHINESS (when/if-let/when-let) or complex machinery (for/
   doseq) — which the TYPED core can't model — fail TRANSPARENTLY with a message naming
   the macro. See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.surface.collections :as coll]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(defn- err-chain [form]
  ;; the WHOLE cause chain's messages joined (the "Unsupported macro" message is on a
  ;; wrapping ex-info, not the root cause).
  (try (binding [a/*verbose* false] (eval form)) nil
       (catch Throwable t
         (loop [e t, acc ""] (if e (recur (.getCause e) (str acc " " (.getMessage e))) acc)))))

(deftest macros-expand-or-fail-transparently
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn m-or    [x :- Bool, y :- Bool] Bool (or x y)))
        (eval '(ansatz.core/defn m-and   [x :- Bool, y :- Bool] Bool (and x y)))
        (eval '(ansatz.core/defn m-ifnot [x :- Nat] Nat (if-not (< x 10) x (+ x 1))))
        (eval '(ansatz.core/defn m-not   [x :- Bool] Bool (not x)))
        ;; `for` is now a first-class surface form (relational comprehension → map/filter/join)
        (eval '(ansatz.core/defn m-for [xs :- (List Nat)] (List Nat) (for [x xs] (+ x 1)))))
      ;; derived macros work (via macroexpand-1)
      (is (true?  (((resolve 'm-or)  false) true))  "or")
      (is (true?  (((resolve 'm-and) true)  true))  "and")
      (is (= 4    ((resolve 'm-ifnot) 3))           "if-not → (if (not c) …) works")
      (is (false? ((resolve 'm-not) true))          "not → Bool.not")
      (is (= [2 3 4] (vec ((resolve 'm-for) [1 2 3]))) "for is a surface form (→ map) and runs")
      ;; truthiness/Option macros still fail TRANSPARENTLY (message names the macro)
      (let [w (err-chain '(ansatz.core/defn m-when [x :- Nat] Nat (when (< x 10) (+ x 1))))]
        (is (and w (re-find #"Unsupported macro `when`" w)) "when fails with a clear message")))
    (do (println "SKIP macros-expand-or-fail-transparently: no Init env") (is true))))
