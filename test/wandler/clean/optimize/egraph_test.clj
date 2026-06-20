(ns wandler.clean.optimize.egraph-test
  "Phase 5.3 (clean tree) — the e-graph equality-saturation search layer
   (`wandler.clean.optimize.egraph`). Pins that the machinery loads against the clean certify/cost
   leaves, saturates with the prelude `wsum_*` hoist laws + clean cost-rewrites, and that every plan it
   extracts carries a `check-constant`-verified proof. Also pins the driver integration: `optimize-cost`
   with `:use-egraph? true` runs saturation as the search fallback (and the structured physical
   strategies still fire first). The e-graph is an UNTRUSTED oracle — soundness is the verified proof."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [wandler.test-env :as test-env]
            [wandler.clean.laws.bucket :as bucket]
            [wandler.clean.optimize :as opt]
            [wandler.clean.optimize.egraph :as egraph]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (binding [a/*verbose* false] (bucket/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))
(def ^:private z lvl/zero)
(defn- kc [s] (e/const' (nm/from-string s) []))

(defn- map-map-term
  "List.map id (List.map id xs) — a fusable streaming term, no join, the saturation's simp move fuses it."
  []
  (let [Nat (kc "Nat")
        idf (e/lam "x" Nat (e/bvar 0) :default)
        xs  (e/fvar 7003)
        lctx {7003 {:name "xs" :type (e/app (e/const' (nm/from-string "List") [z]) Nat)}}
        inner (e/app* (e/const' (nm/from-string "List.map") [z z]) Nat Nat idf xs)
        term  (e/app* (e/const' (nm/from-string "List.map") [z z]) Nat Nat idf inner)]
    [term lctx]))

(deftest egraph-laws-installed
  (when (ready?)
    (testing "the clean hoist law set (prelude wsum linearity) is present in the env"
      (doseq [s egraph/hoist-laws]
        (is (some? (kenv/lookup (a/env) (nm/from-string s))) (str s " installed"))))))

(deftest saturate-and-extract-certifies
  (when (ready?)
    (testing "saturation over a fusable term extracts a changed plan whose composed proof verifies"
      (let [[term lctx] (map-map-term)
            r (egraph/saturate-and-extract (a/env) term :lctx lctx)]
        (is (:changed? r) "the e-graph found a cheaper equivalent plan (the fused form)")
        (is (:verified? r) "the COMPOSED proof (orig = extracted) kernel check-constant-verifies")
        (is (not (.equals ^Object term (:term r))) "the plan changed")))))

(deftest driver-use-egraph
  (when (ready?)
    (testing "optimize-cost :use-egraph? runs saturation as the search fallback, still verified"
      (let [[term lctx] (map-map-term)
            r (opt/optimize-cost (a/env) term :lctx lctx :use-egraph? true)]
        (is (:changed? r))
        (is (:verified? r) "the e-graph-selected plan certifies")
        ;; under the ported (old-faithful) driver, confluent map∘map fusion wins in the base pass before
        ;; the e-graph adds anything, so :rewrites is [] — the :use-egraph? path is exercised + verified,
        ;; but the e-graph only changes the plan when it beats base fusion (see saturate-and-extract-certifies).
        (is (= [] (:rewrites r)) "base fusion already deforests map∘map; the e-graph adds nothing here")))
    (testing "structured physical strategies still fire FIRST even with :use-egraph? on"
      ;; the separable-weight factor query — the factor recognizer should win before the e-graph fallback.
      (let [[term lctx comm] ((requiring-resolve 'wandler.clean.optimize.physical-test/nat-agg-join-query))
            r (opt/optimize-cost (a/env) term :lctx lctx :comm comm :use-egraph? true
                                 :sizes {7001 1000 7002 1000})]
        (is (:changed? r))
        (is (:verified? r))
        (is (= :agg-join-factor (first (:rewrites r)))
            "the structured factor strategy is preferred over equality saturation")))))
