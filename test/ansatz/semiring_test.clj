(ns ansatz.semiring-test
  "The SEMIRING core (ansatz.semiring): `Rel A S` over a semiring `S` — one algebra, many domains — plus
   the CERTIFIED POPS recursion-safety gate (`Bool.absorptive`, a kernel theorem where the datahike/
   Scallop design has only a documentation matrix)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.semiring :as sr]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (sr/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest absorption-certificate
  (when (ready?)
    (testing "Bool absorption is a PROVEN kernel theorem (the recursion-safety gate), not an axiom"
      (let [ci (kenv/lookup (a/env) (nm "Bool.absorptive"))]
        (is (some? ci) "Bool.absorptive present + kernel-verified")
        (is (not (.isAxiom ci)) "proven (∨ a (∧ a b) = a, by cases on a), not admitted")))))

(deftest kernel-semiring-structure
  (when (ready?)
    (testing "the Semiring is a kernel-typed STRUCTURE with Bool & Nat instances (B1)"
      (doseq [n ["Semiring" "Semiring.mk" "Semiring.add" "Semiring.zero" "Semiring.Bool" "Semiring.Nat"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present + kernel-verified")))
      (is (not (.isAxiom (kenv/lookup (a/env) (nm "Semiring.Bool")))) "the Bool instance is a checked def, not an axiom")
      (is (not (.isAxiom (kenv/lookup (a/env) (nm "Semiring.Nat")))) "the Nat (counting) instance is a checked def"))))

(deftest faq-laws-certified
  (when (ready?)
    (testing "FAQ variable-elimination soundness is PROVEN for Bool (factorization + order-independence)"
      (doseq [n ["Semiring.bool_or_comm" "Semiring.bool_and_comm" "Semiring.bool_distrib"]]
        (let [ci (kenv/lookup (a/env) (nm n))]
          (is (some? ci) (str n " present + kernel-verified"))
          (is (not (.isAxiom ci)) (str n " proven by cases, not admitted"))))
      (is (= "Semiring.bool_distrib" (:distributivity (sr/faq-certificate sr/existence)))
          "the FAQ factorization for existence is certified by a kernel theorem")
      (is (= :algebra (:level (sr/faq-certificate sr/existence))) "existence FAQ is certified at the ALGEBRA level")
      (is (= :execution (:level (sr/faq-certificate sr/counting)))
          "counting FAQ is certified at the EXECUTION level by the optimizer's proven Nat factorization laws (ansatz.faq-plan)"))))

(deftest recursion-gate
  (testing "the CERTIFIED POPS gate — which semirings may recurse (datahike's matrix, as a kernel theorem)"
    (let [g (sr/recursion-safe? sr/existence)]
      (is (true? (:safe? g)) "Boolean / classical datalog recurses safely")
      (is (= "Bool.absorptive" (:proof g)) "…and it is backed by a KERNEL PROOF, not documentation")
      (is (= :certified (:status g))))
    (is (false? (:safe? (sr/recursion-safe? sr/counting))) "counting is NOT absorptive — must not recurse")
    (is (= :unsafe (:status (sr/recursion-safe? sr/counting))))
    (is (= :provable-pending (:status (sr/recursion-safe? sr/min-max-prob))) "fuzzy is provable, proof pending")))

(deftest faq-one-query-many-semirings
  (testing "FAQ variable elimination — SAME query structure + elimination order, different semiring/domain"
    (let [keep  [:x :y]
          order [:m]                                   ; eliminate the intermediate node (the PLAN)
          ;; same structure (1→{2,3}→9); annotations live in each semiring
          fc1 (sr/factor [:x :m] {{:x 1 :m 2} 1 {:x 1 :m 3} 1})   fc2 (sr/factor [:m :y] {{:m 2 :y 9} 1 {:m 3 :y 9} 1})
          ft1 (sr/factor [:x :m] {{:x 1 :m 2} 5 {:x 1 :m 3} 2})   ft2 (sr/factor [:m :y] {{:m 2 :y 9} 1 {:m 3 :y 9} 4})
          fb1 (sr/factor [:x :m] {{:x 1 :m 2} true {:x 1 :m 3} true}) fb2 (sr/factor [:m :y] {{:m 2 :y 9} true {:m 3 :y 9} true})]
      (is (= {{:x 1 :y 9} 2}    (:rel (sr/faq sr/counting  keep order [fc1 fc2]))) "counting: 2 two-hop paths 1→9")
      (is (= {{:x 1 :y 9} 6}    (:rel (sr/faq sr/tropical  keep order [ft1 ft2]))) "tropical(min,+): shortest = min(5+1,2+4)=6")
      (is (= {{:x 1 :y 9} true} (:rel (sr/faq sr/existence keep order [fb1 fb2]))) "existence: 1→9 reachable")
      (testing "the elimination order is a PLAN (cost, not correctness): any order gives the same answer"
        (is (= (:rel (sr/faq sr/counting keep order [fc1 fc2]))
               (:rel (sr/faq sr/counting keep (sr/elimination-order keep [fc1 fc2]) [fc1 fc2])))
            "join-order = elimination-order: order affects cost, not result (commutative semiring)")))))

(deftest datalog-recursion-gated-by-pops
  (testing "transitive closure as a fixpoint — GATED by the certified POPS recursion-safety"
    (let [E-bool (sr/factor [:from :to] {{:from 1 :to 2} true {:from 2 :to 3} true {:from 3 :to 4} true})
          E-trop (sr/factor [:from :to] {{:from 1 :to 2} 1 {:from 2 :to 3} 1 {:from 3 :to 4} 1})
          reach  (sr/fixpoint sr/existence E-bool (sr/compose-step sr/existence E-bool))   ; reachability
          short  (sr/fixpoint sr/tropical  E-trop (sr/compose-step sr/tropical  E-trop))]  ; shortest path
      (is (= 6 (count (:rel reach))) "reachability: 6 reachable pairs in the chain 1→2→3→4")
      (is (true? (get (:rel reach) {:from 1 :to 4})) "1 reaches 4 transitively")
      (is (= 3 (get (:rel short) {:from 1 :to 4})) "tropical: shortest 1→4 = 3 hops")
      (is (= 1 (get (:rel short) {:from 2 :to 3})) "tropical: shortest 2→3 = 1")
      (testing "the gate REFUSES a non-absorptive semiring (counting recursion would diverge)"
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsafe|absorptive"
              (sr/fixpoint sr/counting E-trop (sr/compose-step sr/counting E-trop)))
            "counting recursion rejected by the certified POPS gate (Bool.absorptive)")))))

(deftest surface-query-over-semirings
  (testing "ONE datalog query, executed over different semirings via the FAQ planner (the front door)"
    (let [query  {:find [:x :y] :where [[:edge :x :m] [:edge :m :y]]}      ; 2-hop join, eliminate :m
          edge-w (fn [w] (sr/relation [:a :b] {[1 2] (w 0) [1 3] (w 1) [2 9] (w 2) [3 9] (w 3)}))]
      (is (= {{:x 1 :y 9} 2}    (:rel (sr/q query sr/counting  {:edge (edge-w (constantly 1))})))   "counting: 2 two-hop paths 1→9")
      (is (= {{:x 1 :y 9} 6}    (:rel (sr/q query sr/tropical  {:edge (edge-w [5 2 1 4])})))        "tropical: shortest = min(5+1,2+4)=6")
      (is (= {{:x 1 :y 9} true} (:rel (sr/q query sr/existence {:edge (edge-w (constantly true))}))) "existence: 1→9 reachable")
      (testing "and the SAME query, provenance semiring → WMC → an inference"
        (let [pe (sr/relation [:a :b] {[1 2] #{#{:e12}} [1 3] #{#{:e13}} [2 9] #{#{:e29}} [3 9] #{#{:e39}}})
              formula (get (:rel (sr/q query sr/provenance {:edge pe})) {:x 1 :y 9})]
          (is (= #{#{:e12 :e29} #{:e13 :e39}} formula) "provenance: the two derivations")
          (is (< (Math/abs (- (sr/wmc {:e12 0.9 :e29 0.8 :e13 0.5 :e39 0.4} formula) 0.776)) 1e-9)
              "WMC: P(1→9) = 0.776"))))))

(deftest provenance-and-inference
  (testing "inference = the provenance algebra (ours) → WMC (a trusted oracle)"
    (let [E1 (sr/factor [:x :m] {{:x 1 :m 2} #{#{:e12}} {:x 1 :m 3} #{#{:e13}}})   ; facts tagged by id
          E2 (sr/factor [:m :y] {{:m 2 :y 9} #{#{:e29}} {:m 3 :y 9} #{#{:e39}}})
          formula (get (:rel (sr/faq sr/provenance [:x :y] [:m] [E1 E2])) {:x 1 :y 9})
          probs   {:e12 0.9 :e29 0.8 :e13 0.5 :e39 0.4}
          expect  (- 1.0 (* (- 1 (* 0.9 0.8)) (- 1 (* 0.5 0.4))))]  ; two independent 2-hop paths
      (is (= #{#{:e12 :e29} #{:e13 :e39}} formula) "provenance: the two 2-hop paths, as a DNF")
      (is (< (Math/abs (- (sr/wmc probs formula) expect)) 1e-9)
          "WMC gives the marginal P(reachable) = 1−(1−p12·p29)(1−p13·p39), NOT the naive sum-of-products")
      (is (false? (:safe? (sr/recursion-safe? sr/provenance)))
          "provenance is NOT recursion-safe (DNF blows up) — the gate matches the datahike matrix"))))

(deftest one-algebra-many-semirings
  (testing "the SAME relational operators compute different domains by swapping the semiring"
    (let [custs-count {{:id 1} 1 {:id 2} 1}
          custs-bool  {{:id 1} true {:id 2} true}
          ords-count  {{:cid 1 :n 1} 1 {:cid 1 :n 2} 1 {:cid 9 :n 3} 1}]
      (testing "counting semiring (ℕ): the join computes cardinalities"
        (let [j (sr/rel-join sr/counting :cid :id ords-count custs-count)]
          (is (= 2 (reduce + (vals j))) "two orders match customer 1; order 9 has no match")))
      (testing "existence semiring (Bool): the SAME rel-join computes set membership"
        (let [j (sr/rel-join sr/existence :cid :id {{:cid 1} true {:cid 9} true} custs-bool)]
          (is (= 1 (count j)) "only the matching pair survives")
          (is (every? true? (vals j)) "its annotation is ⊤")))
      (testing "rel-sum marginalizes over the semiring (FAQ ⊕): group orders by cid, count them"
        (let [by-cid (sr/rel-sum sr/counting #(:cid (first %)) (sr/rel-join sr/counting :cid :id ords-count custs-count))]
          (is (= {1 2} by-cid) "customer 1 accumulates weight 2"))))))
