(ns wandler.transducer-test
  "Item A — transducer ingestion. A Clojurian writes idiomatic transducer code
   — (into [] (comp (map f) (filter p)) xs), (transduce xf rf init xs),
   (sequence xf xs), (remove p) — and gets the SAME fused, kernel-certified term
   as the explicit nested form. A transducer stack is just a different surface for
   the nested SOAC IR we already fuse; it desugars to it and rides the existing
   optimizer + certification. See [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [wandler.clean.surface.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- kernel-checks?
  "AUTHORITATIVE: re-typecheck the registered declaration's value against its
   type via the Java kernel check-constant, under a FRESH name (the original is
   already present) carrying the constant's level params. Not the lenient inferType."
  [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (try
      (env/check-constant
       (a/env)
       (env/mk-def (name/from-string (str "__chk_" nm))
                   (env/ci-level-params ci) (env/ci-type ci) (env/ci-value ci))
       50000000)
      true
      (catch Throwable _ false))))

(deftest transducer-ingestion
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        ;; (1) into + comp(map,filter): map +1 then keep <=10
        (eval '(ansatz.core/defn td-into [xs :- (List Nat)] (List Nat)
                 (into [] (comp (map (fn [x] (Nat.add x 1)))
                                (filter (fn [x] (Nat.ble x 10)))) xs)))
        ;; (2) transduce: same pipeline, summed — fuses to ONE foldl
        (eval '(ansatz.core/defn td-trans [xs :- (List Nat)] Nat
                 (transduce (comp (map (fn [x] (Nat.add x 1)))
                                  (filter (fn [x] (Nat.ble x 10)))) Nat.add 0 xs)))
        ;; (3) sequence: a single map stage
        (eval '(ansatz.core/defn td-seq [xs :- (List Nat)] (List Nat)
                 (sequence (map (fn [x] (Nat.mul x 2))) xs)))
        ;; (4) remove: keep x where NOT (x <= 5)
        (eval '(ansatz.core/defn td-rem [xs :- (List Nat)] (List Nat)
                 (into [] (remove (fn [x] (Nat.ble x 5))) xs))))
      ;; all four kernel-certify (the optimizer re-checks each fusion rewrite)
      (is (true? (kernel-checks? "td-into"))  "into+comp certifies")
      (is (true? (kernel-checks? "td-trans")) "transduce certifies")
      (is (true? (kernel-checks? "td-seq"))   "sequence certifies")
      (is (true? (kernel-checks? "td-rem"))   "remove certifies")
      ;; and compute the right thing (vector input)
      (is (= [2 6 10 4] ((resolve 'td-into)  [1 5 9 20 3])) "into: map+1 then <=10")
      (is (= 22         ((resolve 'td-trans) [1 5 9 20 3])) "transduce: sum of (2 6 10 4)")
      (is (= [2 4 6]    ((resolve 'td-seq)   [1 2 3]))      "sequence: *2")
      (is (= [8 9]      ((resolve 'td-rem)   [1 8 3 9]))    "remove: drop <=5")
      ;; the transduce pipeline also runs fully primitive over a long[] (one scan)
      (is (= 22 ((resolve 'td-trans) (long-array [1 5 9 20 3]))) "transduce over long[]"))
    (do (println "SKIP transducer-ingestion: no Init env") (is true))))
