;; The ONE registry of kernel-law-gated algebraic licences (cohesion audit item 2).
;;
;; "Verification licenses the fast representation": an op may be re-associated
;; (parallel fork-join fold), commuted, or factored exactly when the kernel env
;; CONTAINS the proofs of the laws that justify it. This namespace is where an
;; op's runtime form, identity, and required law names live — registered once,
;; consulted by codegen (wandler.runtime's apfoldl gate) and, as further
;; structures land (semirings for the inference tier), by the optimizer.
;;
;; The licence check is deliberately conservative: no laws in the env, no licence.
(ns wandler.algebra
  (:require [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]))

(defonce ^{:doc "Kernel op const-name → {:clj <2-arg Clojure op>, :id <identity literal>,
                 :laws [associativity + identity theorem names]}. The seed covers the
                 Init arithmetic monoids; domains register their own with register-monoid!."}
  monoids
  (atom
   {"Nat.add" {:clj '+ :id 0 :laws ["Nat.add_assoc" "Nat.zero_add" "Nat.add_zero"]}
    "Nat.mul" {:clj '* :id 1 :laws ["Nat.mul_assoc" "Nat.one_mul" "Nat.mul_one"]}
    "Int.add" {:clj '+ :id 0 :laws ["Int.add_assoc" "Int.zero_add" "Int.add_zero"]}
    "Int.mul" {:clj '* :id 1 :laws ["Int.mul_assoc" "Int.one_mul" "Int.mul_one"]}}))

(defn register-monoid!
  "Register a monoid licence: `op-const-name` (the kernel op, e.g. \"Foo.combine\"),
   with :clj (the runtime 2-arg op symbol or form), :id (the identity literal, compared
   against the fold's init), and :laws (the associativity + identity theorem NAMES whose
   presence in the env is the licence). Idempotent."
  [op-const-name spec]
  {:pre [(contains? spec :clj) (contains? spec :id) (seq (:laws spec))]}
  (swap! monoids assoc op-const-name spec))

(defn monoid-licence
  "The parallel-fold licence for kernel op `op-name` with fold init `init-clj`:
   the Clojure combine op iff the op is registered, `init-clj` is its identity, AND
   every required law is present in `env` (kernel-proven — the proof is the licence).
   nil otherwise."
  [env op-name init-clj]
  (when-let [spec (get @monoids op-name)]
    (when (and (= init-clj (:id spec))
               (every? #(some? (kenv/lookup env (name/from-string %))) (:laws spec)))
      (:clj spec))))
