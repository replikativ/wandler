(ns ansatz.list-literal-test
  "Vector `[a b]` and `(list a b)` literals as List VALUES (homogeneous; element type from
   the first, Nat for empty). Closes the prior cryptic NPE on (mapcat (fn [x] [x x]) xs) — the
   most idiomatic mapcat. Also: an unknown op now fails TRANSPARENTLY (compile-app-or-macro
   elaborates the head before its args, so an untyped lambda arg can't NPE-mask the cause).
   See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [ansatz.collections :as coll]
            [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(deftest vector-and-list-literals
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn ll-vec  [x :- Nat] (List Nat) [x x x]))
        (eval '(ansatz.core/defn ll-empt [x :- Nat] (List Nat) []))
        (eval '(ansatz.core/defn ll-list [x :- Nat] (List Nat) (list x (inc x))))
        ;; the previously-cryptic case
        (eval '(ansatz.core/defn ll-mcat [xs :- (List Nat)] (List Nat) (mapcat (fn [x] [x x]) xs))))
      (is (= [5 5 5] ((resolve 'll-vec) 5))   "vector literal → List")
      (is (empty? ((resolve 'll-empt) 5))      "empty vector → empty List")
      (is (= [5 6] ((resolve 'll-list) 5))     "(list a b) → List")
      (is (= [1 1 2 2] ((resolve 'll-mcat) [1 2])) "mapcat (fn [x] [x x]) — idiomatic, was cryptic NPE")
      ;; unknown op fails TRANSPARENTLY (fresh JVM: keep is unregistered)
      (let [msg (try (binding [a/*verbose* false]
                       (eval '(ansatz.core/defn ll-keep [xs :- (List Nat)] (List Nat) (keep (fn [x] x) xs))))
                     nil
                     (catch Throwable t (.getMessage (loop [e t] (if (.getCause e) (recur (.getCause e)) e)))))]
        (is (and msg (re-find #"Unknown: keep" msg)) "unsupported `keep` fails transparently, not cryptically")))
    (do (println "SKIP vector-and-list-literals: no Init env") (is true))))
