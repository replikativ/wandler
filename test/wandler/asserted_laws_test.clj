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
