(ns wandler.reducers.plan-test
  (:require [wandler.reducers.plan :as pl]
            [wandler.reducers :as r]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(def ^:private init-full-env test-env/init-full-env)

(defn- nat-const [] (e/const' (name/from-string "Nat") []))
(defn- succ-cfn [] (r/certified-fn {:name 'Nat.succ
                                    :kernel-term (e/const' (name/from-string "Nat.succ") [])
                                    :runtime inc}))
(defn- add-cfn [] (r/certified-fn {:name 'Nat.add
                                   :kernel-term (e/const' (name/from-string "Nat.add") [])
                                   :runtime +}))

(deftest soac-map-fold-fusion-is-verified
  ;; Integration: a `sum (map succ (map succ xs))` plan fuses both maps into the
  ;; fold consumer with kernel-checked `List.foldl_map` proofs, runs natively, and
  ;; agrees with plain Clojure. Skips when init.ndjson is absent.
  (if-let [kenv @init-full-env]
    (let [p (pl/plan (pl/producer (nat-const))
                     [(pl/map-step (succ-cfn)) (pl/map-step (succ-cfn))]
                     (pl/fold-consumer (add-cfn) 0))
          fused (pl/fuse kenv p)
          report (pl/explain fused)
          xs [1 2 3 4 5]]
      ;; both maps fused away
      (is (= [] (:transforms report)))
      (is (= :fold (:consumer report)))
      ;; two kernel-checked fusion proofs
      (is (= 2 (count (:proofs report))))
      (is (every? :kernel-checked? (:proofs report)))
      (is (every? #(= "List.foldl_map" (:theorem %)) (:proofs report)))
      ;; the proof type is the equality the rewrite relies on
      (is (re-find #"List\.foldl|List\.map" (:theorem-type (first (:proofs report)))))
      ;; execution agrees with native Clojure: sum of (inc∘inc) over xs
      (is (= (transduce (comp (map inc) (map inc)) + 0 xs)
             (pl/run fused xs)))
      (is (= (pl/run p xs) (pl/run fused xs))))
    (do
      (println "SKIP soac-map-fold-fusion-is-verified: test-data/init.ndjson absent")
      (is true))))

(deftest analyze-extracts-purity-and-types
  ;; The property-extraction pass: purity/totality are guaranteed by construction
  ;; (kernel terms), types are inferred. Needs only a Nat-bearing env.
  (if-let [kenv @init-full-env]
    (let [p (pl/plan (pl/producer (nat-const))
                     [(pl/map-step (succ-cfn))]
                     (pl/fold-consumer (add-cfn) 0))
          a (:analysis (pl/analyze kenv p))
          mfn (:fn (first (:transforms a)))]
      (is (true? (:pure? mfn)))
      (is (true? (:total? mfn)))
      (is (= "(∀ : Nat, Nat)" (e/->string (:type mfn)))))
    (is true)))
