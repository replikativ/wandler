(ns wandler.parallel-fold-test
  "Item B — verified-monoid → parallel fork-join fold. A foldl whose combine op is
   a kernel-PROVEN associative monoid (Nat.add/Nat.mul) with `init` its identity
   lowers to clojure.core.reducers/fold over a persistent vector: the associativity
   proof is exactly the certificate fork-join needs to re-associate the reduction.
   The long[] path stays unboxed single-thread; non-monoid folds stay sequential.
   See [[verified-aggregation]], [[semiring-sum-product-planner]]."
  (:require [ansatz.core :as a]
            [wandler.clean.surface.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [wandler.runtime :as ap]   ;; *parallel-fold* codegen knob (carved from ansatz.core)
            [clojure.test :refer [deftest is]]))

(defn- runtime-form
  "The Clojure codegen form for a registered declaration's (naive) kernel term —
   used to assert which fold combinator was emitted."
  [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (a/ansatz->clj (a/env) (env/ci-value ci) [])))

(defn- emits? [sym nm]
  (boolean (some #{sym} (flatten (runtime-form nm)))))

(defn- kernel-checks? [nm]
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (try
      (env/check-constant
       (a/env)
       (env/mk-def (name/from-string (str "__chk_" nm))
                   (env/ci-level-params ci) (env/ci-type ci) (env/ci-value ci))
       50000000)
      true
      (catch Throwable _ false))))

(deftest verified-monoid-parallel-fold
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn pf-sum  [xs :- (List Nat)] Nat (reduce + 0 xs)))
        (eval '(ansatz.core/defn pf-prod [xs :- (List Nat)] Nat (reduce * 1 xs)))
        ;; fused sum-of-map: foldl_map collapses, and the + step is still a monoid
        (eval '(ansatz.core/defn pf-sumdbl [xs :- (List Nat)] Nat
                 (reduce + 0 (mapv #(* % 2) xs))))
        ;; non-monoid: left operand of + is (acc*2), not bare acc → stays sequential
        (eval '(ansatz.core/defn pf-horner [xs :- (List Nat)] Nat
                 (reduce (fn [acc x] (Nat.add (Nat.mul acc 2) x)) 0 xs)))
        ;; wrong identity: + with init 1 is NOT the monoid identity → stays sequential
        (eval '(ansatz.core/defn pf-sum1 [xs :- (List Nat)] Nat (reduce + 1 xs))))
      ;; (1) codegen: proven monoids → apfoldl; non-monoid / wrong-identity → afoldl
      (is (true?  (emits? 'wandler.runtime/apfoldl "pf-sum"))    "sum monoid → parallel apfoldl")
      (is (true?  (emits? 'wandler.runtime/apfoldl "pf-prod"))   "product monoid → parallel apfoldl")
      (is (true?  (emits? 'wandler.runtime/apfoldl "pf-sumdbl")) "fused sum-of-map → parallel apfoldl")
      (is (true?  (emits? 'wandler.runtime/afoldl  "pf-horner")) "non-monoid → sequential afoldl")
      (is (false? (emits? 'wandler.runtime/apfoldl "pf-horner")) "non-monoid is NOT parallelized")
      (is (false? (emits? 'wandler.runtime/apfoldl "pf-sum1"))   "wrong identity is NOT parallelized")
      ;; (2) all kernel-certify (the monoid proof is in Init; the decl type-checks)
      (is (true? (kernel-checks? "pf-sum"))    "sum certifies")
      (is (true? (kernel-checks? "pf-sumdbl")) "fused sum certifies")
      ;; (3) correctness — vector AND primitive long[] (long[] stays unboxed)
      (is (= 15 ((resolve 'pf-sum)    [1 2 3 4 5]))            "sum vector")
      (is (= 15 ((resolve 'pf-sum)    (long-array [1 2 3 4 5]))) "sum long[]")
      (is (= 24 ((resolve 'pf-prod)   [1 2 3 4]))             "product")
      (is (= 12 ((resolve 'pf-sumdbl) [1 2 3]))               "fused sum-of-map")
      (is (= 12 ((resolve 'pf-sumdbl) (long-array [1 2 3])))  "fused sum-of-map long[]")
      ;; (4) parallel result EQUALS sequential on a large vector (the soundness payoff)
      (let [big (vec (range 200000))
            par ((resolve 'pf-sum) big)
            seq (binding [ap/*parallel-fold* false] (reduce + 0 big))]
        (is (= par seq) "fork-join sum over 200k matches sequential"))
      ;; (5) UNBOXED-PARALLEL long[] path: a fused IFn$LLL step over a long[] above the
      ;; fork threshold (131072) runs zero-boxing AND parallel; result must be exact.
      (let [n 200000
            arr (long-array (range n))
            expect (* 2 (quot (* (dec n) n) 2))]          ; sum of 2*x, x∈[0,n)
        (is (= expect ((resolve 'pf-sumdbl) arr)) "unboxed-parallel long[] fold is exact")))
    (do (println "SKIP verified-monoid-parallel-fold: no Init env") (is true))))
