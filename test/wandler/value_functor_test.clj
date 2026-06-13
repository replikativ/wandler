(ns wandler.value-functor-test
  "Arch #8: the ONE total malli→type functor. F(schema) = Subtype Value (λ v. conforms v = true) —
   every schema is a refinement of the universal Value universe carved by its conformance predicate γ.
   This closes the gap the precise lane (ansatz.malli/schema->type-expr) leaves: an UNTAGGED union
   [:or …] / [:enum …] is set-union over the value universe (semantic subtyping), modelled faithfully
   as a disjunctive conformance predicate — NOT a tagged Sum (which would model malli's :orn). So
   :or/:enum, which THROW in the precise lane, get verified kernel-type images here.

   (Recursive conformance — [:vector …]/nested maps — currently fails at WF termination in the conforms
   compiler, a separate pre-existing gap; this functor covers it the moment that's fixed.)"
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.malli :as am]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [wandler.core :as w]
            [ansatz.surface.data :as data]
            [ansatz.surface.schema :as schema]
            [wandler.test-env :as test-env]))

(def ^:private ready (atom false))

(use-fixtures :once
  (fn [f]
    (if @test-env/init-full-env
      (do (reset! a/ansatz-env @test-env/init-full-env)
          (binding [a/*verbose* false] (w/install!) (data/install-core!))
          (reset! ready true)
          (f))
      (do (println "SKIP value-functor: init.ndjson / store absent") (f)))))

(defn- type-verifies? [conf-name schema]
  (let [ty (schema/schema->value-type conf-name schema)
        ax (env/mk-axiom (name/from-string (str "tyck-" (gensym))) [] ty)]
    (env/check-constant (a/env) ax)            ;; throws if the type is ill-formed
    (re-find #"Subtype" (ansatz.kernel.expr/->string ty))))

(deftest functor-is-total-and-closes-the-union-gap
  (when @ready
    (binding [a/*verbose* false]
      ;; the precise lane CANNOT type an untagged union / enum — it throws…
      (is (thrown? Exception (am/schema->type-expr [:or :int :string])))
      (is (thrown? Exception (am/schema->type-expr [:enum :a :b :c])))
      ;; …but the universal functor gives each a well-formed, kernel-VERIFIED type image.
      (is (type-verifies? 'conf-int  :int)                 "scalar")
      (is (type-verifies? 'conf-or   [:or :int :string])   ":or  — union gap CLOSED")
      (is (type-verifies? 'conf-enum [:enum :a :b :c])     ":enum — enum gap CLOSED")
      (is (type-verifies? 'conf-bnd  [:int {:min 18}])     "bounded refinement")
      (is (type-verifies? 'conf-map  [:map [:x :int] [:y :string]]) "flat record"))))

(deftest conformance-is-inhabitation
  ;; The one law, computational side: a value that conforms (γ v = true) is exactly an inhabitant of
  ;; F(schema). For the concrete string "hi" against [:or :int :string], law-or (Value.vstr "hi") ≡
  ;; true, so the conformance proof (rfl) IS the inhabitation certificate for Subtype Value law-or.
  (when @ready
    (binding [a/*verbose* false]
      (schema/schema->value-type 'law-or [:or :int :string])   ;; installs law-or : Value → Bool
      (a/prove-theorem 'or-conforms-str []
                       '(= Bool (law-or (Value.vstr "hi")) Bool.true) '[(rfl)])
      (is (some? (env/lookup (a/env) (name/from-string "or-conforms-str")))
          "\"hi\" conforms to [:or :int :string] — its proof inhabits Subtype Value law-or"))))
