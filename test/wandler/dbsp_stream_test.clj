(ns wandler.dbsp-stream-test
  "The DBSP stream-operator algebra (rung 3): streams = Nat→Int with delay/D/I/incremental, the
   fundamental theorems D∘I=id and I∘D=id, and the chain rule (Q1∘Q2)^Δ=Q1^Δ∘Q2^Δ — all kernel-
   certified. Plus a concrete reduction check that D and I actually compute as inverses on a sample
   stream. See wandler.exec.dbsp-stream, ../dbsp-theory."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.exec.dbsp-stream :as ds]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private intT (e/const' (nm "Int") []))
(def ^:private natT (e/const' (nm "Nat") []))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (ds/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest stream-operator-algebra-present-and-verified
  (when (ready?)
    (testing "delay/D/I/incremental + the fundamental theorems + the chain rule are admitted"
      (doseq [n ["Stream.delay" "Stream.D" "Stream.I" "Stream.incremental"
                 "Stream.D_I" "Stream.I_D" "Stream.incremental_comp" "Stream.incremental_linear"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present"))))))

(deftest D-and-I-compute-as-inverses-on-a-sample-stream
  (when (ready?)
    (testing "on s = (λn. Int.ofNat n): D(I s) 3 ≡ s 3 and I(D s) 3 ≡ s 3 by kernel reduction"
      (let [s (e/lam "n" natT (e/app (e/const' (nm "Int.ofNat") []) (e/bvar 0)) :default)
            three (e/lit-nat 3)
            DI (e/app* (e/const' (nm "Stream.D") []) (e/app (e/const' (nm "Stream.I") []) s) three)
            ID (e/app* (e/const' (nm "Stream.I") []) (e/app (e/const' (nm "Stream.D") []) s) three)
            s3 (e/app s three)
            st (tc/mk-tc-state (a/env))]
        (is (tc/is-def-eq st DI s3) "D(I s) 3 reduces to s 3")
        (is (tc/is-def-eq st ID s3) "I(D s) 3 reduces to s 3")))))
