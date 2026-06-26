(ns wandler.refine-test-deferred
  "Dependent-type filter elimination: a filter whose predicate is provably constant
   over the element type is removed (always-true) or empties the pipeline
   (always-false), kernel-proven. Gated on an Init env."
  (:require [wandler.surface.refine :as refine]
            [wandler.reducers.plan :as pl]
            [wandler.reducers :as r]
            [wandler.test-env :as test-env]
            [wandler.surface.malli :as malli]
            [ansatz.core :as a]
            [wandler.surface.records :as rec]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

;; deferred: refined-field filter ELIMINATION (dependent Subtype filter) — eval error post-port (tier follow-up)

(deftest refined-record-field-filter-eliminated
  ;; The keystone: a user-written refined record (age must be >= 18), a filter on
  ;; the refined field reads ergonomically (.val), compiles, verifies, and is
  ;; eliminated via the field's carried refinement. No axioms.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RPerson
                 [:map [:age [:and :int [:>= 18]]] [:score [:and :int [:>= 0]]]]))
        (eval '(ansatz.core/defn r-adult? [p :- RPerson] Bool (>= (:age p) 18))))
      (let [ci (env/lookup (a/env) (name/from-string "r-adult?"))
            body (e/->string (.value ci))
            res (refine/prove-const (a/env) (.value ci) (e/const' (name/from-string "RPerson") []))]
        ;; the refined field read unwrapped to its underlying value
        (is (re-find #"Subtype.val" body))
        ;; the filter is proven always-true via the field's refinement (Tier 3)
        (is (= true (:value res)))
        (is (re-find #"ble_eq_true_of_le" (e/->string (:proof res))))))
    (do (println "SKIP refined-record-field-filter-eliminated: no Init env") (is true))))
