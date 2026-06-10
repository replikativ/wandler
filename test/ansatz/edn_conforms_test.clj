(ns ansatz.edn-conforms-test
  "#57 — malli schema as a REFINEMENT predicate over the EDN Value universe. The building
   blocks (type predicates, key equality, per-type key checkers) and a compiled conformance
   predicate all KERNEL-VERIFY (check-constant). This is the principled EDN↔malli bridge: a
   typed view of dynamic EDN is `{v : Value // conforms v schema}`; here we produce the
   `conforms` half, verified. (Per-type key checkers sidestep the Value-returning-recursion
   gap; the runtime EDN↔Value boundary is the next layer.) See [[edn-core-formalization]]."
  (:require [ansatz.core :as a]
            [ansatz.edn :as edn]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- checks? [nm]
  (when-let [ci (kenv/lookup (a/env) (name/from-string nm))]
    (try (kenv/check-constant (a/env)
           (kenv/mk-def (name/from-string (str "__c_" nm))
                        (kenv/ci-level-params ci) (kenv/ci-type ci) (kenv/ci-value ci)) 50000000)
         true (catch Throwable _ false))))

(deftest schema-as-value-refinement
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (edn/install-core!)
      ;; building blocks verify
      (is (true? (checks? "vint?"))    "type predicate verifies")
      (is (true? (checks? "vmap?"))    "vmap? verifies")
      (is (true? (checks? "vkeq"))     "key equality (String ==) verifies")
      (is (true? (checks? "key-int?")) "Bool-returning key-type checker (recursive) verifies")
      (is (true? (checks? "key-str?")) "key-str? verifies")
      ;; #58: a Value-RETURNING recursion (vget) now verifies (was "Nat.rec mismatch")
      (is (true? (checks? "vget"))     "Value-returning recursive key lookup verifies (#58)")
      ;; compile a malli :map schema → a Value conformance predicate, which KERNEL-VERIFIES
      (binding [a/*verbose* false]
        (eval (edn/schema->conforms-form 'conforms-person [:map [:name :string] [:age :int]]))
        (eval (edn/schema->conforms-form 'conforms-flag   [:map [:on :boolean]])))
      (is (true? (checks? "conforms-person")) "compiled :map conformance predicate verifies")
      (is (true? (checks? "conforms-flag"))   "boolean-field conformance verifies")
      ;; the compiler output shape
      (let [form (edn/schema->conforms-form 'c [:map [:age :int]])]
        (is (= '(ansatz.core/defn c [v :- Value] Bool (and (vmap? v) (key-int? (Value.vkw "age") v))) form)
            "schema → λ v. (vmap? v) ∧ key-int? :age v")))
    (do (println "SKIP schema-as-value-refinement: no Init env") (is true))))

(defn- form-name [form] (str (nth form 1)))  ;; (ansatz.core/defn NAME params …)

;; Compile a schema, eval all forms, assert EVERY generated form check-constants, and
;; differential-test the top predicate against malli/validate on `cases`.
(defn- check-schema! [top schema cases]
  (let [forms (edn/schema->conforms-forms top schema)]
    (binding [a/*verbose* false] (doseq [f forms] (eval f)))
    (doseq [f forms]
      (is (true? (checks? (form-name f)))
          (str (form-name f) " (from " schema ") kernel-verifies")))
    (when-let [validate (try (requiring-resolve 'malli.core/validate) (catch Throwable _ nil))]
      (let [pred (resolve top)]
        (doseq [c cases]
          (is (= (boolean (validate schema c)) (boolean (pred (edn/edn->value c))))
              (str top " vs malli on " (pr-str c))))))))

(deftest nested-vector-optional-schemas
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (edn/install-core!)
      ;; nested map: a field whose schema is itself a :map
      (check-schema! 'conf-nested
        [:map [:name :string] [:addr [:map [:city :string] [:zip :int]]]]
        [{:name "a" :addr {:city "ny" :zip 10}}
         {:name "a" :addr {:city "ny" :zip "x"}}
         {:name "a" :addr {:city "ny"}}
         {:name "a" :addr 5}
         {:name "a"}])
      ;; homogeneous vector of a scalar
      (check-schema! 'conf-vec [:map [:xs [:vector :int]]]
        [{:xs [1 2 3]} {:xs []} {:xs [1 "x" 3]} {:xs 5} {}])
      ;; vector of nested maps (recursion through both layers)
      (check-schema! 'conf-vecmap [:map [:items [:vector [:map [:id :int]]]]]
        [{:items [{:id 1} {:id 2}]} {:items [{:id 1} {:id "x"}]} {:items []}])
      ;; optional field: absent OK, present must match
      (check-schema! 'conf-opt [:map [:name :string] [:age {:optional true} :int]]
        [{:name "a" :age 5} {:name "a" :age "x"} {:name "a"} {:age 5}]))
    (do (println "SKIP nested-vector-optional-schemas: no Init env") (is true))))
