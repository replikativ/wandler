(ns wandler.reducers-test-deferred
  (:require [wandler.reducers :as r]
            [ansatz.core :as ac]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

;; deferred: reducers tier certification plumbing predates the seams — rebase on wandler.algebra at tier revival

(deftest prove-pipeline-auto-certifies-ansatz-defn
  ;; Integration: a function defined with `ansatz.core/defn` (idiomatic `+`,
  ;; `:-` types) tags itself with its kernel constant, so it can be used in a
  ;; pipeline directly — no `certified-fn` wrapper — and still proves end-to-end.
  (if-let [kenv @init-full-env]
    (let [saved @ac/ansatz-env]
      (try
        (reset! ac/ansatz-env kenv)
        (let [triple (ac/define-verified 'rt-triple '[n :- Nat] 'Nat '(+ n (+ n n)))]
          ;; self-certified purely from a/defn metadata
          (is (= 'rt-triple (:name (r/certification triple))))
          (let [proved (r/prove-pipeline @ac/ansatz-env
                                         (r/pipeline (map triple) (map triple)))
                [proof] (r/reducer-proofs proved)]
            (is (= :map-fusion (:rule proof)))
            (is (true? (:kernel-checked? proof)))
            ;; triple twice = ×9
            (is (= [9 18 27] (r/into [] proved [1 2 3])))))
        (finally (reset! ac/ansatz-env saved))))
    (do
      (println "SKIP prove-pipeline-auto-certifies-ansatz-defn: test-data/init.ndjson absent")
      (is true))))
