(ns ansatz.verified-test
  (:require [ansatz.verified :as v]
            [ansatz.reducers :as r]
            [ansatz.core :as ac]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(def ^:private init-full-env test-env/init-full-env)

(defn- succ-cfn []
  (r/certified-fn {:name 'Nat.succ
                   :kernel-term (e/const' (name/from-string "Nat.succ") [])
                   :runtime inc}))

(deftest verified-transducer-surface-fuses-and-matches-clojure
  ;; The drop-in surface reads like a Clojure transducer pipeline, fuses the maps
  ;; into the fold with kernel-checked proofs, and matches native Clojure.
  (if-let [kenv @init-full-env]
    (let [saved @ac/ansatz-env]
      (try
        (reset! ac/ansatz-env kenv)
        (let [succ (succ-cfn)
              xform (v/comp (v/map succ) (v/map succ) (v/map succ))
              report (v/explain xform)
              xs [1 2 3 4 5 6 7]]
          ;; all three maps fused into the consumer
          (is (= [] (:transforms report)))
          (is (= 3 (count (:proofs report))))
          (is (every? :kernel-checked? (:proofs report)))
          ;; result matches plain Clojure transducers
          (is (= (transduce (comp (map inc) (map inc) (map inc)) + 0 xs)
                 (v/sum xform xs))))
        (finally (reset! ac/ansatz-env saved))))
    (do
      (println "SKIP verified-transducer-surface-fuses-and-matches-clojure: init.ndjson absent")
      (is true))))

(deftest verified-record-surface-compiles-and-proves-fusion
  ;; The record half of the umbrella surface: define a schema-typed record, write
  ;; an idiomatic threaded pipeline, get a verified fused fn + a fusion proof.
  (if-let [kenv @init-full-env]
    (let [saved @ac/ansatz-env]
      (try
        (reset! ac/ansatz-env kenv)
        (binding [ac/*verbose* false]
          (eval '(ansatz.verified/def-record VRow
                   [:map [:a [:and :int [:>= 0]]] [:b [:and :int [:>= 0]]] [:c [:and :int [:>= 0]]]]))
          (eval '(ansatz.verified/defn vbump [r :- VRow] VRow
                   (-> r (assoc :a 1) (assoc :b 2) (assoc :a 9)))))
        ;; the verified fn exists and its fusion-equivalence theorem was admitted
        (is (some? (ansatz.kernel.env/lookup @ac/ansatz-env (name/from-string "vbump"))))
        (is (re-find #"Eq\." (str (v/fusion-proof 'vbump))))
        (finally (reset! ac/ansatz-env saved))))
    (do (println "SKIP verified-record-surface-compiles-and-proves-fusion: no Init env")
        (is true))))
