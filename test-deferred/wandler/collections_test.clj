(ns wandler.collections-test
  "Everyday collection ops (count/reduce/mapv/filterv) over List compile, verify,
   and run. Gated on an Init env."
  (:require [ansatz.core :as a]
            [wandler.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- verified? [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (let [tc (doto (TypeChecker. (a/env)) (.setFuel 50000000))]
      (.isDefEq tc (.inferType tc (.value ci)) (.type ci)))))

(deftest collection-ops-verify-and-run
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn c-sum   [xs :- (List Nat)] Nat (reduce + 0 xs)))
        (eval '(ansatz.core/defn c-count [xs :- (List Nat)] Nat (count xs)))
        (eval '(ansatz.core/defn c-inc   [xs :- (List Nat)] (List Nat) (mapv inc xs))))
      ;; all kernel-verified
      (is (true? (verified? "c-sum")))
      (is (true? (verified? "c-count")))
      (is (true? (verified? "c-inc")))
      ;; and the compiled runtime computes the right thing
      (is (= 15N ((resolve 'c-sum) (list 1 2 3 4 5))))
      (is (= 5 ((resolve 'c-count) (list 1 2 3 4 5))))
      (is (= [11 21] ((resolve 'c-inc) (list 10 20)))))
    (do (println "SKIP collection-ops-verify-and-run: no Init env") (is true))))

(deftest inline-anonymous-fns-verify-and-run
  ;; Untyped inline fns — (fn [x] …) and the reader #(…) — with the param type
  ;; inferred from the collection's element type.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn ia-map   [xs :- (List Nat)] (List Nat) (mapv #(+ % 1) xs)))
        (eval '(ansatz.core/defn ia-fn    [xs :- (List Nat)] (List Nat) (mapv (fn [x] (+ x 1)) xs)))
        (eval '(ansatz.core/defn ia-fold  [xs :- (List Nat)] Nat (reduce (fn [acc x] (+ acc x)) 0 xs))))
      (is (true? (verified? "ia-map")))
      (is (true? (verified? "ia-fn")))
      (is (true? (verified? "ia-fold")))
      (is (= [2 3 4] ((resolve 'ia-map) (list 1 2 3))))
      (is (= 10N ((resolve 'ia-fold) (list 1 2 3 4)))))
    (do (println "SKIP inline-anonymous-fns-verify-and-run: no Init env") (is true))))

(deftest long-array-pipeline-unboxed
  ;; The unboxed backend: a fused map-pipeline over a primitive long[] runs with ZERO
  ;; boxing (amapl + the induced ^long IFn$LL arity) and RETURNS a long[] — breaking the
  ;; mapv boxing ceiling. Same kernel proof; the user opts in by passing a long-array.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn la1 [xs :- (List Nat)] (List Nat) (mapv #(+ % 1) xs)))
        (eval '(ansatz.core/defn la3 [xs :- (List Nat)] (List Nat) (mapv #(+ % 3) (mapv #(* % 2) (la1 xs))))))
      (let [out ((resolve 'la3) (long-array [10 20 30]))]
        ;; primitive long[] in → long[] out, correct values (10→11→22→25 …)
        (is (instance? (class (long-array 0)) out) "returns a primitive long[]")
        (is (= [25 45 65] (vec out)) "fused pipeline over long[] computes the right thing"))
      ;; vector input still works (amapl falls back to mapv) — backwards compatible
      (is (= [25 45 65] ((resolve 'la3) [10 20 30]))))
    (do (println "SKIP long-array-pipeline-unboxed: no Init env") (is true))))

(deftest long-array-fold-unboxed
  ;; A map→fold aggregation over a primitive long[] fuses (foldl_map) to ONE primitive
  ;; scan via afoldl — zero boxing AND zero allocation (scalar result). This is where the
  ;; unboxed backend wins biggest (~50x in benchmarks). Same kernel proof.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn sumdbl [xs :- (List Nat)] Nat (reduce + 0 (mapv #(* % 2) xs)))))
      ;; 2*(1+2+3) = 12, identical for long[] and vector inputs
      (is (= 12 ((resolve 'sumdbl) (long-array [1 2 3]))) "fold over long[] computes the right scalar")
      (is (= 12N ((resolve 'sumdbl) [1 2 3])) "vector input still works"))
    (do (println "SKIP long-array-fold-unboxed: no Init env") (is true))))

(deftest double-array-map-unboxed
  ;; The unboxed backend extends to Float/Real: a Float map pipeline over a primitive
  ;; double[] runs with ZERO boxing (amapl's double[] branch + the induced ^double IFn$DD
  ;; arity) and RETURNS a double[]. (Float folds/filters await Float-literal codegen — CIC
  ;; has no float literals — so map is the testable slice today.)
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn d-sq [xs :- (List Float)] (List Float) (mapv (fn [x] (mul Float x x)) xs))))
      (let [out ((resolve 'd-sq) (double-array [2.0 3.0 4.0]))]
        (is (instance? (class (double-array 0)) out) "returns a primitive double[]")
        (is (= [4.0 9.0 16.0] (vec out)) "fused Float map over double[] is unboxed + correct"))
      ;; vector input still works (amapl falls back to mapv) — backwards compatible
      (is (= [4.0 9.0 16.0] ((resolve 'd-sq) [2.0 3.0 4.0]))))
    (do (println "SKIP double-array-map-unboxed: no Init env") (is true))))

(deftest long-array-filter-unboxed
  ;; filter+map+fold over a primitive long[] runs fully primitive (afilter via IFn$LO,
  ;; then amapl/afoldl) — completes the unboxed SOAC trio. ~37x on aggregation pipelines.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn fsum [xs :- (List Nat)] Nat
                 (reduce + 0 (mapv #(* % 2) (filterv (fn [x] (Nat.ble 100 x)) xs))))))
      ;; keep x>=100, double, sum: 2*(150+200) = 700; the 50 is filtered out
      (is (= 700 ((resolve 'fsum) (long-array [50 150 200]))) "filter+map+fold over long[] is correct")
      (is (= 700N ((resolve 'fsum) [50 150 200])) "vector input still works"))
    (do (println "SKIP long-array-filter-unboxed: no Init env") (is true))))
