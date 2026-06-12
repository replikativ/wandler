(ns wandler.bridge-test
  "The OPTIONAL engine bridge (wandler.bridge): an engine's logical IR α-lifts to the Ansatz kernel
   IR, is optimized ONCE with the CERTIFIED laws, and γ-lowers back to the engine — demonstrated
   with a MOCK engine. This is the mechanism the datahike/stratum adapters plug into; no real engine
   is needed here, proving Ansatz stays standalone."
  (:require [ansatz.core :as a]
            [wandler.bridge :as bridge]
            [wandler.laws.relational :as rl]
            [wandler.kmap :as kmap]
            [wandler.optimize.plan :as plan]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

;; ── a MOCK engine: a filter over an equi-join of two named relations ──────────
;; α (:lift): the engine's IR → the Ansatz kernel term  filter (p∘fst) (Map.join kf lf xs ys).
(defn- mock-lift [_ir]
  (let [nat (e/const' (nm "Nat") []) prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat)
        deceq (e/const' (nm "instDecidableEqNat") [])
        p (e/fvar 2) xs (e/fvar 3) ys (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6)
        predfst (e/lam "pr" prodNN (e/app p (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)]
    (e/app* (e/const' (nm "List.filter") [z]) prodNN predfst
            (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq kf lf xs ys))))

;; γ (:lower): an Ansatz plan → a mock physical executor s-expression.
(defn- mock-lower [pl]
  (case (:op pl)
    :source [:scan]
    :filter [:filter (mock-lower (:input pl))]
    :join   [:hash-join (mock-lower (:left pl)) (mock-lower (:right pl))]
    :map    [:project (mock-lower (:input pl))]
    [(:op pl)]))

(deftest certified-optimize-across-the-bridge
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (rl/install!)   ; the relational laws (filter→join pushdown) — the certificate alphabet
      (bridge/register-engine! :mock {:detect? (constantly true) :lift mock-lift :lower mock-lower})
      (is (contains? (bridge/available-engines) :mock) "mock engine registered + available")
      ;; α-lift the engine IR, optimize ONCE in the certified kernel IR, get the optimized plan back
      (let [lctx {2 {:name "p"  :type (e/forall' "_" (e/const' (nm "Nat") []) (e/const' (nm "Bool") []) :default)}
                  3 {:name "xs" :type (e/app (e/const' (nm "List") [z]) (e/const' (nm "Nat") []))}
                  4 {:name "ys" :type (e/app (e/const' (nm "List") [z]) (e/const' (nm "Nat") []))}
                  5 {:name "kf" :type (e/forall' "_" (e/const' (nm "Nat") []) (e/const' (nm "Nat") []) :default)}
                  6 {:name "lf" :type (e/forall' "_" (e/const' (nm "Nat") []) (e/const' (nm "Nat") []) :default)}}
            {:keys [plan verified? changed?]} (bridge/optimize-plan (a/env) mock-lift :the-ir :lctx lctx)]
        ;; the cross-engine optimization is kernel-CERTIFIED
        (is (true? verified?) "optimized plan ≡ original is kernel-certified")
        (is (true? changed?) "the optimizer rewrote the cross-engine plan")
        ;; the filter→join PUSHDOWN fired: the optimized plan is now a JOIN whose LEFT input is the
        ;; filter (filtering xs BEFORE the join) — the structural evidence of the pushdown.
        (is (= :join (:op plan)) "top of the optimized plan is the join")
        (is (= :filter (:op (:left plan))) "the filter was pushed DOWN into the join's left input")
        ;; γ-lower the optimized plan back to the engine's physical form
        (is (= [:hash-join [:filter [:scan]] [:scan]] (bridge/lower :mock plan))
            "γ-lowered exec: hash-join with the filter pre-applied to the left scan")))
    (do (println "SKIP bridge test: no Init env") (is true))))

(deftest engines-stay-optional
  ;; load-optional-engines! must never throw even when no engine is on the classpath
  (is (set? (bridge/load-optional-engines!)) "optional engine loading is safe when engines absent"))
