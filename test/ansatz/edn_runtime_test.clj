(ns ansatz.edn-runtime-test
  "#59 — the verified EDN `Value` layer is now RUNNABLE. ansatz.core's general TAGGED inductive
   codegen (`[cidx field…]` constructors + a `case`-on-`(nth t 0)` recursor) makes Value/EDN
   functions execute on real Clojure data via the `edn->value` / `value->edn` boundary. The
   kernel-verified predicates (`vint?`, `vmap?`, recursive `vget`, compiled `conforms-*`) here
   are exercised at runtime and differential-tested against `clojure.core/get` and (when present)
   `malli.core/validate`. See [[edn-core-formalization]] / [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [ansatz.edn :as edn]
            [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(def ^:private samples
  [nil true false 0 42 -7 "" "hi" :kw :a/b
   [] [1 2 3] ["a" "b"] [1 [2 3] 4]
   {} {:name "x" :age 5} {:a [1 2] :b {:c 3}} {:on true}])

(deftest edn-value-roundtrip
  ;; pure Clojure — no kernel env needed
  (doseq [x samples]
    (is (= x (edn/value->edn (edn/edn->value x)))
        (str "round-trip " (pr-str x)))))

(deftest verified-fns-run-at-runtime
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (edn/install-core!)
      (binding [a/*verbose* false]
        (eval (edn/schema->conforms-form 'conforms-person [:map [:name :string] [:age :int]])))
      (let [vint?  (resolve 'vint?)
            vstr?  (resolve 'vstr?)
            vmap?  (resolve 'vmap?)
            vget   (resolve 'vget)
            cp     (resolve 'conforms-person)
            ->v    edn/edn->value
            kw     (fn [s] (->v (keyword s)))]
        ;; type predicates run on the tagged rep
        (is (true?  (vint? (->v 5))))
        (is (false? (vint? (->v "x"))))
        (is (true?  (vstr? (->v "x"))))
        (is (true?  (vmap? (->v {:a 1}))))
        (is (false? (vmap? (->v 9))))
        ;; recursive Value-returning lookup matches clojure.core/get (differential)
        (let [m {:name "alice" :age 30 :tag :vip}
              vm (->v m)]
          (doseq [k [:name :age :tag :missing]]
            (is (= (get m k) (edn/value->edn (vget (kw (name k)) vm)))
                (str "vget " k))))
        ;; compiled malli :map conformance predicate runs correctly
        (is (true?  (cp (->v {:name "bob" :age 1}))))
        (is (false? (cp (->v {:name "bob" :age "NaN"}))))  ; wrong field type
        (is (false? (cp (->v {:name "bob"}))))             ; missing :age
        (is (false? (cp (->v 7))))                          ; not a map
        ;; differential test vs malli/validate when malli is on the classpath
        (when-let [validate (try (requiring-resolve 'malli.core/validate)
                                 (catch Throwable _ nil))]
          (let [schema [:map [:name :string] [:age :int]]
                cases [{:name "ok" :age 5}
                       {:name "x" :age "y"}
                       {:name "x"}
                       {:age 5}
                       {:name 1 :age 2}
                       {:name "x" :age 5 :extra true}]] ; malli :map is open → extra keys ok
            (doseq [c cases]
              (is (= (boolean (validate schema c)) (boolean (cp (->v c))))
                  (str "conforms vs malli on " (pr-str c))))))))
    (do (println "SKIP verified-fns-run-at-runtime: no Init env") (is true))))
