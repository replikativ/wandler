(ns wandler.string-ops-test
  "str (concat) + common clojure.string ops → kernel String ops, so idiomatic Clojure strings
   work (not just explicit String.append). See [[pipelines-system-design]]."
  (:require [ansatz.core :as a] [wandler.stdlib :as std] [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))
(deftest string-surface-ops
  (if-let [k @test-env/init-full-env]
    (do (reset! a/ansatz-env k) (std/install!)
        (binding [a/*verbose* false]
          (eval '(ansatz.core/defn so-str  [a :- String, b :- String, c :- String] String (str a b c)))
          (eval '(ansatz.core/defn so-up   [a :- String] String (clojure.string/upper-case a)))
          (eval '(ansatz.core/defn so-pre  [a :- String, p :- String] Bool (clojure.string/starts-with? a p)))
          (eval '(ansatz.core/defn so-comp [a :- String, b :- String] String (clojure.string/upper-case (str a b)))))
        (is (= "abc" ((resolve 'so-str) "a" "b" "c")) "str variadic concat")
        (is (= "HI" ((resolve 'so-up) "hi"))          "upper-case → String.toUpper")
        (is (true? ((resolve 'so-pre) "hello" "he"))  "starts-with? → String.isPrefixOf")
        (is (false? ((resolve 'so-pre) "hello" "xy")) "starts-with? false")
        (is (= "ABCD" ((resolve 'so-comp) "ab" "cd")) "str + upper compose"))
    (do (println "SKIP string-surface-ops: no Init env") (is true))))
