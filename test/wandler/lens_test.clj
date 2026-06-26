(ns wandler.lens-test
  "The backward/lens brick (wandler.inference.lens): the certified product-lens round-trip laws + runtime lenses
   that compose hierarchically — the well-behaved corner of inversion (PROGRAMMING_MODEL.md §12)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.inference.lens :as lens]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (lens/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest lens-laws-certified
  (when (ready?)
    (testing "the product lens round-trip laws are PROVEN in the kernel (not admitted)"
      (doseq [n ["Lens.fst_PutGet" "Lens.fst_GetPut"]]
        (let [ci (kenv/lookup (a/env) (nm n))]
          (is (some? ci) (str n " present + kernel-verified"))
          (is (not (.isAxiom ci)) (str n " proven (projection-computes / structure-eta), not admitted")))))))

(deftest lenses-round-trip-and-compose
  (testing "runtime lenses obey GetPut/PutGet and compose hierarchically"
    (is (= {:get-put true :put-get true} (lens/round-trips? lens/fst-lens [1 2] 9)) "fst lens round-trips")
    (is (= {:get-put true :put-get true} (lens/round-trips? (lens/key-lens :age) {:name "Ann" :age 30} 31))
        "field lens (:age / assoc) round-trips")
    (testing "hierarchical composition: focus :city inside :addr"
      (let [l (lens/lens-comp (lens/key-lens :addr) (lens/key-lens :city))
            s {:name "Ann" :addr {:city "NYC" :zip 10001}}]
        (is (= "NYC" ((:get l) s)) "composed get reaches the nested field")
        (is (= {:name "Ann" :addr {:city "LA" :zip 10001}} ((:put l) "LA" s)) "composed put rebuilds through both")
        (is (= {:get-put true :put-get true} (lens/round-trips? l s "LA")) "the composite lens round-trips")))))

(deftest delta-lenses-inverse-of-diff
  (testing "field delta-lens obeys delta-PutGet (Diskin)"
    (is (true? (lens/dround-trip? (lens/field-dlens :age) {:name "Ann" :age 30} 31))))
  (testing "z-filter delta-lens is the INVERSE of the ∂ filter — edit the view, propagate to the source"
    (let [pred :keep
          src  {{:id 1 :keep true} 1 {:id 2 :keep false} 1}
          dl   (lens/zfilter-dlens pred)
          view ((:get dl) src)
          dview {{:id 3 :keep true} 1}                    ; insert a matching row into the VIEW
          ds   ((:put-delta dl) dview src)                ; propagate to the SOURCE
          src' (merge-with + src ds)
          view' ((:get dl) src')]
      (is (= {{:id 1 :keep true} 1} view) "view = filtered source")
      (is (= dview ds) "the source-change = the view-change (rows pass the filter by construction)")
      (is (= (merge-with + view dview) view') "applying ΔS reflects Δview in the view — the delta-lens law"))))
