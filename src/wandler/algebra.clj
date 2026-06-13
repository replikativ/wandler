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
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel TypeChecker]))

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

;; ── asserted algebraic laws for FOREIGN ops (the trust-boundary planner licence) ──
;; "the proof OR the asserted axiom is the licence": a verified op PROVES its monoid
;; laws; a foreign op ASSERTS them. Either way `monoid-licence` finds the law names in
;; the env and the parallel fold fires. `assert-monoid!` admits the assoc + identity laws
;; as AXIOMS (trusted) and registers the op — so a fold over a foreign associative op
;; auto-parallelizes, with the asserted laws as the entire trust boundary.

(defn- carrier-level
  "The universe `u` for `Eq.{u} M …` — i.e. M : Sort u, so the sort level of M's TYPE
   directly (Nat : Sort 1 → u = 1). (Distinct from List.{u}, where elements are Sort (u+1).)"
  [env M]
  (e/sort-level (.inferType (TypeChecker. env) M)))

(defn- eq-prop
  "`Eq.{u} M lhs rhs` (a Prop)."
  [u M lhs rhs]
  (e/app* (e/const' (name/from-string "Eq") [u]) M lhs rhs))

(defn- assoc-stmt
  "∀ (a b c : M), Eq M (⊕ (⊕ a b) c) (⊕ a (⊕ b c))."
  [u M op]
  (let [a (e/bvar 2) b (e/bvar 1) c (e/bvar 0)
        lhs (e/app* op (e/app* op a b) c)
        rhs (e/app* op a (e/app* op b c))]
    (e/forall' "a" M (e/forall' "b" M (e/forall' "c" M (eq-prop u M lhs rhs) :default) :default) :default)))

(defn- lid-stmt
  "∀ (a : M), Eq M (⊕ e a) a   (e closed)."
  [u M op id]
  (e/forall' "a" M (eq-prop u M (e/app* op id (e/bvar 0)) (e/bvar 0)) :default))

(defn- rid-stmt
  "∀ (a : M), Eq M (⊕ a e) a   (e closed)."
  [u M op id]
  (e/forall' "a" M (eq-prop u M (e/app* op (e/bvar 0) id) (e/bvar 0)) :default))

(defn assert-monoid!
  "TRUST that foreign op `op-name` (a kernel const ⊕ : M → M → M, e.g. an a/foreign) is an
   associative monoid with identity `id-expr : M` (a closed kernel term) and runtime 2-arg
   op `clj-op`, fold init `id-literal`. Admits the assoc + left/right-identity laws as
   AXIOMS (trusted, named `<op>_assoc`/`<op>_zero_add`/`<op>_add_zero`) and registers the
   monoid, so `(reduce ⊕ id xs)` auto-parallelizes (apfoldl). The asserted laws are the
   trust boundary. Idempotent. Mutates the global env."
  [op-name M clj-op id-literal id-expr]
  (let [env @a/ansatz-env
        u (carrier-level env M)
        op (e/const' (name/from-string op-name) [])
        admit (fn [nm stmt]
                (when-not (kenv/lookup @a/ansatz-env (name/from-string nm))
                  (swap! a/ansatz-env kenv/check-constant (kenv/mk-axiom (name/from-string nm) [] stmt)))
                nm)
        names [(admit (str op-name "_assoc")    (assoc-stmt u M op))
               (admit (str op-name "_zero_add") (lid-stmt u M op id-expr))
               (admit (str op-name "_add_zero") (rid-stmt u M op id-expr))]]
    (register-monoid! op-name {:clj clj-op :id id-literal :laws names})
    op-name))

(defmacro foreign
  "Declare a trusted FOREIGN function (a/foreign) and lift any algebraic laws from its
   name metadata `^{:laws {…}}` into the planner. Currently understood: a monoid via
   `:assoc true` + `:identity <e>` (e a Nat/Int literal), which asserts the assoc +
   identity laws (trusted axioms) so a fold over the op auto-parallelizes.
     (w/foreign ^{:laws {:assoc true :identity 0}} mysum [a :- Nat, b :- Nat] Nat
       (fn [a b] (+ a b)))
   Properties the user asserts are the trust boundary; everything else is exactly a/foreign."
  [fn-name params ret-type impl]
  (let [laws (:laws (meta fn-name))
        nm   (vary-meta fn-name dissoc :laws)
        op   (str fn-name)]
    `(let [v# (a/foreign ~nm ~params ~ret-type ~impl)]
       ~(when (and (map? laws) (:assoc laws) (contains? laws :identity))
          `(assert-monoid! ~op
                           (e/const' (name/from-string ~(str ret-type)) [])
                           '~nm
                           ~(:identity laws)
                           (e/lit-nat ~(:identity laws))))
       v#)))

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
