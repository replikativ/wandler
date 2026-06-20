(ns wandler.clean.surface.records-test
  "Phase 6 (clean tree) — the RECORDS/MALLI vertical of the surface front door. Pins that a malli `:map`
   schema lifts to an Ansatz structure (`def-record`) and that idiomatic Clojure record ops — standard
   `assoc` / keyword access / `update` — over a schema'd record compile inside a verified `a/defn` body
   and authoritatively `check-constant`-verify. Clean-tree port of `wandler.surface.{records,malli,refine}`
   (IR-agnostic copy-clean; only ansatz.* deps), severing the old-wandler dependency at cutover."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [wandler.test-env :as test-env]
            [wandler.clean.surface.core :as surf]
            [wandler.clean.surface.records :as rec]))

(defn- verifies? [s]
  (let [ci (kenv/lookup (a/env) (nm/from-string s))]
    (boolean (and ci (try (kenv/check-constant-replace (a/env) ci) true (catch Throwable _ false))))))

(deftest clean-records-malli-vertical
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (surf/install!)
      (binding [a/*verbose* false]
        ;; a malli :map schema → an Ansatz structure with the schema's field order
        (eval '(wandler.clean.surface.records/def-record CleanAcct
                 [:map [:owner :string]
                  [:balance [:and :int [:>= 0]]]
                  [:bonus [:and :int [:>= 0]]]]))
        ;; idiomatic Clojure record ops — standard assoc + keyword access (NOT nat-assoc)
        (eval '(ansatz.core/defn clean-set-bonus [a :- CleanAcct] CleanAcct (assoc a :bonus 100)))
        (eval '(ansatz.core/defn clean-get-bal  [a :- CleanAcct] Nat (:balance a)))
        (eval '(ansatz.core/defn clean-bump     [a :- CleanAcct] CleanAcct
                 (update a :balance Nat.succ))))
      (testing "def-record lifted the malli :map to an Ansatz structure with the schema field order"
        (let [sreg (-> (requiring-resolve 'ansatz.core/structure-registry) deref deref)]
          (is (= ["owner" "balance" "bonus"] (:fields (get sreg "CleanAcct"))))))
      (testing "standard assoc / keyword access / update over the record kernel-verify (check-constant)"
        (is (verifies? "clean-set-bonus") "assoc rebuilds via the constructor, kernel-verified")
        (is (verifies? "clean-get-bal")   "keyword access projects the field, kernel-verified")
        (is (verifies? "clean-bump")      "update maps a field through a fn, kernel-verified"))
      (testing "assoc rebuilds through the structure constructor, touching the right field"
        (let [body (e/->string (.value (kenv/lookup (a/env) (nm/from-string "clean-set-bonus"))))]
          (is (re-find #"CleanAcct\.mk" body))
          (is (re-find #"100" body)))))
    (do (println "SKIP clean-records-malli-vertical: no Init env") (is true))))
