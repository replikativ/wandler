(ns ansatz.malli-test
  (:require [ansatz.malli :as am]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- nat-ty [] (e/const' (name/from-string "Nat") []))
(defn- arrow [a b] (e/forall' "_" a b :default))

(defn- malli-available?
  "The metosin/malli library is an OPTIONAL dep (the :malli alias). Tests that
   exercise live registry resolution skip cleanly when it isn't on the classpath,
   so `clj -M:test` and `clj -M:test:malli` never diverge into errors."
  []
  (try (require 'malli.core) true (catch Throwable _ false)))

;; --- EXPORT: CIC type → Malli schema (pure data; no Malli/env needed) ---

(deftest type-expr->malli-base-types
  (binding [am/*warn-unknown?* false]
    (is (= [:and :int [:>= 0]] (am/type-expr->malli (nat-ty))))
    (is (= :int (am/type-expr->malli (e/const' (name/from-string "Int") []))))
    (is (= :boolean (am/type-expr->malli (e/const' (name/from-string "Bool") []))))
    (is (= :string (am/type-expr->malli (e/const' (name/from-string "String") []))))
    ;; only :default params survive to the runtime schema
    (is (= [:=> [:cat [:and :int [:>= 0]]] [:and :int [:>= 0]]]
           (am/fn-schema (arrow (nat-ty) (nat-ty)))))))

;; --- IMPORT: Malli schema → kernel record model (pure data) ---

(deftest malli-record-builds-kernel-record
  (let [rec (am/malli-record [:map [:a :int] [:b :string] [:c [:and :int [:>= 0]]]])]
    (is (= [:a :b :c] (:keys rec)))
    (is (= {:a 0 :b 1 :c 2} (:index rec)))
    (is (= 3 (count (:field-types rec))))
    ;; right-nested Prod of the field types, at Type 0 (level 0, not the old ill-typed
    ;; {1,1} — lenient inferType accepted it; #43)
    (is (= "(Prod.{0, 0} Int (Prod.{0, 0} String Nat))"
           (e/->string (:rec-type rec))))
    ;; import then export recovers the (right-nested) tuple shape
    (binding [am/*warn-unknown?* false]
      (is (= [:tuple :int [:tuple :string [:and :int [:>= 0]]]]
             (am/type-expr->malli (:rec-type rec)))))))

;; --- GENERATIVE: property-test the compiled runtime bridge (needs Malli + Init) ---

(defn- malli-available? []
  (boolean (try (requiring-resolve 'malli.generator/function-checker)
                (catch Throwable _ nil))))

(deftest generative-check-of-compiled-runtime
  ;; `check-verified` property-tests the COMPILED runtime against the CIC type via
  ;; Malli generators — exercising `ansatz->clj`, the runtime↔kernel bridge.
  ;;
  ;; On an overflow-free domain (Bool → Bool) it confirms the bridge is faithful.
  ;; NB: it also catches real discrepancies — e.g. for `Nat → Nat` with `+` it
  ;; surfaces a JVM `long` overflow (the kernel `Nat` is unbounded), demonstrating
  ;; the value of the check. We use a Bool function here so the assertion is
  ;; deterministic; the overflow boundary is a known faithful-range limitation.
  (if (and (malli-available?) @test-env/init-full-env)
    (let [saved @a/ansatz-env]
      (try
        (reset! a/ansatz-env @test-env/init-full-env)
        (let [bid (binding [a/*verbose* false]
                    (deref (eval '(ansatz.core/defn am-test-bid [b :- Bool] Bool b))))]
          ;; nil ⇒ all generated inputs satisfied the CIC-derived contract
          (is (nil? (am/check-verified bid {:iterations 100}))))
        (finally (reset! a/ansatz-env saved))))
    (do
      (println "SKIP generative-check-of-compiled-runtime: Malli or init.ndjson absent")
      (is true))))

(deftest registered-types-resolve-through-the-bridge
  ;; A registered domain type flows into the kernel type universe with ZERO per-type
  ;; wiring — the bridge resolves the ref to its form and recurses, so the frontend's
  ;; reach = malli's reach. Inline `:schema {:registry …}` is mode-independent; the
  ;; global default-registry flow is the same resolution (set up once by the user).
  (if (malli-available?)
    (let [order-ref [:schema {:registry {:order [:map [:id :int] [:total [:int {:min 0}]]]
                                         :money [:int {:min 1}]}}
                     :order]
          money-ref  [:schema {:registry {:money [:int {:min 1}]}} :money]]
      (is (re-find #"Prod" (e/->string (am/malli->type-expr order-ref))) "registered record → Prod record")
      (is (re-find #"Subtype" (e/->string (am/malli->type-expr money-ref))) "registered bounded-int alias → Subtype refinement")
      (is (re-find #"List" (e/->string (am/malli->type-expr [:sequential order-ref]))) "[:sequential ref] → List of the record")
      ;; native malli [:int {:min/:max}] now maps to the right refinement
      (is (re-find #"Nat" (e/->string (am/malli->type-expr [:int {:min 0}]))) "[:int {:min 0}] → Nat")
      (is (re-find #"Subtype" (e/->string (am/malli->type-expr [:int {:min 18}]))) "[:int {:min 18}] → Subtype")
      ;; an UNregistered name still errors cleanly (not silently wrong)
      (is (thrown? Exception (am/malli->type-expr :totally-unknown-xyz))))
    (do (println "SKIP registered-types-resolve-through-the-bridge: malli not on classpath")
        (is true))))
