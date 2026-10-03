(ns wandler.asserted-laws-test
  "Asserted algebraic laws on a FOREIGN op feed the planner: 'the proof OR the asserted
   axiom is the licence.' A foreign associative op declares its monoid laws (via
   `^{:laws {:assoc true :identity e}}` metadata → trusted axioms), and a fold over it
   auto-parallelizes (apfoldl) exactly as a verified monoid would — the asserted laws are
   the trust boundary. The optimizer reasons around the opaque op via its declared
   algebra, never by knowing what it computes."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.algebra :as alg]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(deftest foreign-monoid-auto-parallelizes
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (w/install!)
      (binding [a/*verbose* false]
        ;; a foreign associative op over Nat, monoid laws asserted via metadata
        (eval '(wandler.algebra/foreign ^{:laws {:assoc true :identity 0}} mysum2
                                        [a :- Nat, b :- Nat] Nat (fn [a b] (+ a b))))
        (eval '(ansatz.core/defn tot2 [xs :- (List Nat)] Nat (reduce mysum2 0 xs))))
      ;; the three monoid laws were admitted (as trusted axioms)
      (is (every? #(some? (kenv/lookup (a/env) (name/from-string %)))
                  ["mysum2_assoc" "mysum2_zero_add" "mysum2_add_zero"])
          "asserted monoid laws present in env")
      ;; the fold over the FOREIGN op lowered to the PARALLEL apfoldl
      (let [cf (pr-str (a/ansatz->clj (a/env)
                                      (.value (kenv/lookup (a/env) (name/from-string "tot2"))) []))]
        (is (re-find #"apfoldl" cf) "fold over foreign monoid auto-parallelized"))
      ;; and computes correctly
      (is (= 15 (long ((resolve 'tot2) '(1 2 3 4 5)))))
      ;; a foreign op WITHOUT asserted laws must NOT parallelize (no licence)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/foreign mysum3 [a :- Nat, b :- Nat] Nat (fn [a b] (+ a b))))
        (eval '(ansatz.core/defn tot3 [xs :- (List Nat)] Nat (reduce mysum3 0 xs))))
      (let [cf (pr-str (a/ansatz->clj (a/env)
                                      (.value (kenv/lookup (a/env) (name/from-string "tot3"))) []))]
        (is (not (re-find #"apfoldl" cf))
            "foreign op with NO declared laws is NOT parallelized (no licence) — correct")))
    (println "asserted-laws: no env, skipping")))

(deftest verified-monoid-laws-are-proven
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (w/install!)
      ;; a VERIFIED op: defmonoid PROVES its monoid laws (kernel-checked, not trusted)
      (binding [a/*verbose* false]
        (eval '(wandler.algebra/defmonoid psum2 [a :- Nat, b :- Nat] Nat (Nat.add a b) :identity 0))
        (eval '(ansatz.core/defn ptot2 [xs :- (List Nat)] Nat (reduce psum2 0 xs))))
      ;; the laws are PROVEN theorems (not axioms)
      (let [ci (kenv/lookup (a/env) (name/from-string "psum2_assoc"))]
        (is (some? ci) "assoc law present")
        (is (not (.isAxiom ci)) "assoc is PROVEN (a real theorem), not a trusted axiom"))
      ;; and the fold auto-parallelizes off the proven laws
      (let [cf (pr-str (a/ansatz->clj (a/env)
                                      (.value (kenv/lookup (a/env) (name/from-string "ptot2"))) []))]
        (is (re-find #"apfoldl" cf) "fold over proven monoid auto-parallelizes"))
      (is (= 15 (long ((resolve 'ptot2) '(1 2 3 4 5)))))
      ;; a NON-monoid (Nat.sub): the proof must FAIL → not registered → sequential
      (binding [a/*verbose* false]
        (eval '(wandler.algebra/defmonoid psub2 [a :- Nat, b :- Nat] Nat (Nat.sub a b) :identity 0))
        (eval '(ansatz.core/defn stot2 [xs :- (List Nat)] Nat (reduce psub2 0 xs))))
      (let [cf (pr-str (a/ansatz->clj (a/env)
                                      (.value (kenv/lookup (a/env) (name/from-string "stot2"))) []))]
        (is (not (re-find #"apfoldl" cf))
            "non-monoid (Nat.sub) couldn't be PROVEN a monoid → not parallelized — correct & safe")))
    (println "verified-monoid: no env, skipping")))

(deftest properties-grounded-in-std-typeclasses
  ;; The re-grounding: an op's algebraic properties are the canonical Lean proof-carrying
  ;; typeclasses (`Std.Associative`/`Std.Commutative`/`Std.IdempotentOp`). The licence gate
  ;; keys on proof-presence; `install!` materializes the canonical instances for interop.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (w/install!)
      ;; (1) the seed Init monoids are licensed on a fresh env, AND install materialized their
      ;;     canonical Std.Associative / Std.Commutative instances (citeable by List.foldl_assoc)
      (is (= '+' (alg/monoid-licence (a/env) "Nat.add" 0)) "Nat.add monoid licence fires")
      (let [saved @alg/monoids]
        (try
          (doseq [missing [:left-id :right-id]]
            (swap! alg/monoids update "Nat.add" dissoc missing)
            (is (nil? (alg/monoid-licence (a/env) "Nat.add" 0))
                "both identity proofs are required")
            (reset! alg/monoids saved))
          (finally (reset! alg/monoids saved))))
      (is (true? (alg/associative? (a/env) "Nat.add")) "Nat.add associative")
      (is (true? (alg/commutative? (a/env) "Nat.add")) "Nat.add commutative")
      (is (some? (kenv/lookup (a/env) (name/from-string "instStd.Associative_Nat.add")))
          "canonical Std.Associative instance materialized")
      (is (some? (kenv/lookup (a/env) (name/from-string "instStd.Commutative_Nat.add")))
          "canonical Std.Commutative instance materialized")
      ;; (2) a foreign op may ASSERT commutativity + idempotence → the matching Std instances,
      ;;     and the predicates report them (the reorder / dedup licences)
      (binding [a/*verbose* false]
        (eval '(wandler.algebra/foreign ^{:laws {:comm true :idem true}} fmax2
                                        [a :- Nat, b :- Nat] Nat (fn [a b] (max a b)))))
      (is (true? (alg/commutative? (a/env) "fmax2")) "asserted commutativity reported")
      (is (true? (alg/idempotent?  (a/env) "fmax2")) "asserted idempotence reported")
      (is (some? (kenv/lookup (a/env) (name/from-string "instStd.IdempotentOp_fmax2")))
          "canonical Std.IdempotentOp instance built from the asserted law"))
    (println "properties-grounded: no env, skipping")))
