;; The ONE registry of kernel-law-gated algebraic licences (cohesion audit item 1).
;;
;; "Verification licenses the fast representation": an op may be re-associated
;; (parallel fork-join fold), commuted (reorder), or contracted (dedup) exactly
;; when the kernel env CONTAINS a proof of the law that justifies it. This namespace
;; is where an op's runtime form, identity, and proven algebraic properties live —
;; registered once, consulted by codegen (wandler.runtime's apfoldl gate) and, as
;; further structures land, by the optimizer.
;;
;; The properties are grounded in Lean's OWN proof-carrying typeclasses
;; (`Std.Associative`/`Std.Commutative`/`Std.IdempotentOp`, Init/Core.lean): the
;; licence is a real `Std.Associative α op` INSTANCE in the env, not an ad-hoc
;; re-stated axiom. The instance's single field IS the proof — `assert-*` admits it
;; as an axiom (trusted), `prove-*` discharges it by tactic (kernel-checked). Either
;; way the canonical instance is citeable by the matching Std lemma (e.g. a fold
;; reassociation by `List.foldl_assoc [Std.Associative α op]`).
;;
;; The licence check is deliberately conservative: no instance in the env, no licence.
(ns wandler.algebra
  (:refer-clojure :exclude [associative?])
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.prelude.algebra :as prelude]
            [ansatz.tactic.instance :as instance])
  (:import [ansatz.kernel TypeChecker]))

(defn register-instance!
  "Register an already-admitted constant in this environment's instance table.
   Ansatz now follows Lean's registry; naming a definition inst* is not registration."
  [iname]
  (swap! a/ansatz-env instance/add-instance (name/from-string iname))
  iname)

(defn install-semiring-instance!
  "Kernel-admit a prelude carrier and register its additive/semiring instances.
   Also registers existing instances restored from a checked law cache."
  [carrier row]
  (let [result (prelude/install-instance! carrier row)]
    (when (= :verified (:status result))
      (register-instance! (:addmonoid result))
      (register-instance! (:semiring result)))
    result))

;; ── statement builders (the Prop each typeclass field proves) ─────────────────────────────

(defn- carrier-level
  "The universe `u` for `Eq.{u} M …` / `Std.Associative.{u} M op` — i.e. M : Sort u, so the
   sort level of M's TYPE directly (Nat : Sort 1 → u = 1). (Distinct from List.{u}, where
   elements are Sort (u+1).)"
  [env M]
  (e/sort-level (.inferType (TypeChecker. env) M)))

(defn- eq-prop
  "`Eq.{u} M lhs rhs` (a Prop)."
  [u M lhs rhs]
  (e/app* (e/const' (name/from-string "Eq") [u]) M lhs rhs))

(defn- assoc-stmt
  "∀ (a b c : M), Eq M (⊕ (⊕ a b) c) (⊕ a (⊕ b c))  — the `Std.Associative.assoc` field."
  [u M op]
  (let [a (e/bvar 2) b (e/bvar 1) c (e/bvar 0)
        lhs (e/app* op (e/app* op a b) c)
        rhs (e/app* op a (e/app* op b c))]
    (e/forall' "a" M (e/forall' "b" M (e/forall' "c" M (eq-prop u M lhs rhs) :default) :default) :default)))

(defn- comm-stmt
  "∀ (a b : M), Eq M (⊕ a b) (⊕ b a)  — the `Std.Commutative.comm` field."
  [u M op]
  (let [a (e/bvar 1) b (e/bvar 0)]
    (e/forall' "a" M (e/forall' "b" M (eq-prop u M (e/app* op a b) (e/app* op b a)) :default) :default)))

(defn- idem-stmt
  "∀ (x : M), Eq M (⊕ x x) x  — the `Std.IdempotentOp.idempotent` field."
  [u M op]
  (let [x (e/bvar 0)]
    (e/forall' "x" M (eq-prop u M (e/app* op x x) x) :default)))

(defn- lid-stmt
  "∀ (a : M), Eq M (⊕ e a) a   (e closed)."
  [u M op id]
  (e/forall' "a" M (eq-prop u M (e/app* op id (e/bvar 0)) (e/bvar 0)) :default))

(defn- rid-stmt
  "∀ (a : M), Eq M (⊕ a e) a   (e closed)."
  [u M op id]
  (e/forall' "a" M (eq-prop u M (e/app* op (e/bvar 0) id) (e/bvar 0)) :default))

;; ── the canonical Std typeclass instances (the proof-carrying licences) ────────────────────

(def ^:private tc-spec
  "property keyword → {:cls Std typeclass, :mk its single-field constructor, :stmt builder}."
  {:assoc {:cls "Std.Associative"  :mk "Std.Associative.mk"  :stmt assoc-stmt}
   :comm  {:cls "Std.Commutative"  :mk "Std.Commutative.mk"  :stmt comm-stmt}
   :idem  {:cls "Std.IdempotentOp" :mk "Std.IdempotentOp.mk" :stmt idem-stmt}})

(defn- inst-name
  "Deterministic name of op's `tc` instance, e.g. (\"Nat.add\" :assoc) → \"instAssociative_Nat.add\"."
  [op-name tc]
  (str "inst" (:cls (tc-spec tc)) "_" op-name))

(defn- prop-stmt [tc u M op] ((:stmt (tc-spec tc)) u M op))

(defn- build-instance!
  "Admit the canonical `Std.<tc> M op` instance into the global env, given a closed `proof`
   term of its field statement (`prop-stmt tc`). Idempotent; returns the instance const-name."
  [tc op-name u M op proof]
  (let [{:keys [cls mk]} (tc-spec tc)
        iname (inst-name op-name tc)
        nm    (name/from-string iname)]
    (when-not (kenv/lookup @a/ansatz-env nm)
      (let [inst (e/app* (e/const' (name/from-string mk) [u]) M op proof)
            ity  (e/app* (e/const' (name/from-string cls) [u]) M op)]
        (swap! a/ansatz-env kenv/check-constant (kenv/mk-def nm [] ity inst))))
    (register-instance! iname)))

;; ── the registry ──────────────────────────────────────────────────────────────────────────

(defonce ^{:doc "Kernel op const-name → entry. An entry carries the runtime op + identity and,
                 per algebraic property, the NAME of its kernel proof — the licence gate is
                 proof-presence in the env:
                   :clj <2-arg op>  :id <identity literal>  :M <carrier const-name>
                   :assoc-pf/:comm-pf/:idem-pf        <proof const-name | absent>
                   :left-id/:right-id                 <identity proof name | absent>
                   :assoc-inst/:comm-inst/:idem-inst  <canonical Std instance | set by install!>
                 Seeded with the Init arithmetic monoids (their proofs ship in Init, so the gate
                 fires on a fresh env, no install needed); domains register their own via
                 assert-/prove-* or register-monoid!. `install!` additionally materializes the
                 canonical `Std.*` instances (interop / future certified-rewrite seam)."}
  monoids
  (atom
   {"Nat.add" {:clj '+' :id 0 :M "Nat" :assoc-pf "Nat.add_assoc" :comm-pf "Nat.add_comm" :left-id "Nat.zero_add" :right-id "Nat.add_zero"}
    "Nat.mul" {:clj '*' :id 1 :M "Nat" :assoc-pf "Nat.mul_assoc" :comm-pf "Nat.mul_comm" :left-id "Nat.one_mul"  :right-id "Nat.mul_one"}
    "Int.add" {:clj '+' :id 0 :M "Int" :assoc-pf "Int.add_assoc" :comm-pf "Int.add_comm" :left-id "Int.zero_add" :right-id "Int.add_zero"}
    "Int.mul" {:clj '*' :id 1 :M "Int" :assoc-pf "Int.mul_assoc" :comm-pf "Int.mul_comm" :left-id "Int.one_mul"  :right-id "Int.mul_one"}}))

(defn register-monoid!
  "Merge an entry into the registry for `op-const-name` (idempotent). Needs at least :clj
   (runtime op), :id (identity literal, matched against the fold init), :assoc-pf (the
   associativity proof name — the licence gate) and :left-id/:right-id identity proof names."
  [op-const-name spec]
  {:pre [(map? spec)]}
  (swap! monoids update op-const-name merge spec))

(def ^:private pf-key {:assoc :assoc-pf :comm :comm-pf :idem :idem-pf})

(defn install!
  "Materialize the canonical `Std.Associative`/`Std.Commutative` instances for the seed Init
   monoids (Nat/Int · add/mul) from their Init proofs, recording :assoc-inst/:comm-inst.
   Idempotent; called by wandler.core/install!. NOT required for the licence gate (that keys on
   proof-presence) — this is the grounding/interop seam. Skips a seed whose proofs are absent
   (a leaner env than full Init)."
  []
  (doseq [[op-name {:keys [M assoc-pf comm-pf left-id right-id]}] @monoids]
    (let [env @a/ansatz-env
          has? #(and % (some? (kenv/lookup env (name/from-string %))))]
      (when (and M (has? assoc-pf) (has? left-id) (has? right-id))
        (let [Mc (e/const' (name/from-string M) [])
              u  (carrier-level env Mc)
              op (e/const' (name/from-string op-name) [])
              ai (build-instance! :assoc op-name u Mc op (e/const' (name/from-string assoc-pf) []))
              ci (when (has? comm-pf)
                   (build-instance! :comm op-name u Mc op (e/const' (name/from-string comm-pf) [])))]
          (register-monoid! op-name (cond-> {:assoc-inst ai} ci (assoc :comm-inst ci)))))))
  :algebra-installed)

;; ── asserted properties for FOREIGN ops (the trust-boundary planner licence) ──
;; "the proof OR the asserted axiom is the licence": a verified op PROVES its laws; a foreign op
;; ASSERTS them. Either way the canonical Std instance lands in the env and the matching licence
;; fires. `assert-*` admits the field statement as an AXIOM (trusted) then builds the instance.

(defn- admit-axiom!
  "Admit `law-name : stmt` as an AXIOM (idempotent); return the const naming it."
  [law-name stmt]
  (when-not (kenv/lookup @a/ansatz-env (name/from-string law-name))
    (swap! a/ansatz-env kenv/check-constant (kenv/mk-axiom (name/from-string law-name) [] stmt)))
  (e/const' (name/from-string law-name) []))

(defn assert-monoid!
  "TRUST that foreign op `op-name` (a kernel const ⊕ : M → M → M, e.g. an a/foreign) is an
   associative monoid with identity `id-expr : M` (a closed kernel term) and runtime 2-arg op
   `clj-op`, fold init `id-literal`. Admits the assoc + left/right-identity laws as AXIOMS
   (named `<op>_assoc`/`_zero_add`/`_add_zero`), builds the canonical `Std.Associative` instance
   from the assoc axiom, and registers the monoid — so `(reduce ⊕ id xs)` auto-parallelizes
   (apfoldl). The asserted laws are the trust boundary. Idempotent. Mutates the global env."
  [op-name M clj-op id-literal id-expr]
  (let [u  (carrier-level @a/ansatz-env M)
        op (e/const' (name/from-string op-name) [])
        an (str op-name "_assoc") ln (str op-name "_zero_add") rn (str op-name "_add_zero")
        assoc-pf (admit-axiom! an (assoc-stmt u M op))]
    (admit-axiom! ln (lid-stmt u M op id-expr))
    (admit-axiom! rn (rid-stmt u M op id-expr))
    (let [ai (build-instance! :assoc op-name u M op assoc-pf)]
      (register-monoid! op-name {:clj clj-op :id id-literal :assoc-pf an :assoc-inst ai :left-id ln :right-id rn}))
    op-name))

(defn assert-property!
  "TRUST that foreign op `op-name` (⊕ : M → M → M) has algebraic property `tc` (:comm or :idem),
   admitting its law as an AXIOM and building the canonical `Std.<tc>` instance. Updates the
   registry entry. The asserted law is the trust boundary. Idempotent."
  [tc op-name M]
  (let [u  (carrier-level @a/ansatz-env M)
        op (e/const' (name/from-string op-name) [])
        suffix ({:comm "_comm" :idem "_idempotent"} tc)
        pn (str op-name suffix)
        pf (admit-axiom! pn (prop-stmt tc u M op))
        i  (build-instance! tc op-name u M op pf)]
    (register-monoid! op-name {(pf-key tc) pn (keyword (str (name tc) "-inst")) i})
    op-name))

;; ── proven properties for VERIFIED ops (kernel-checked, not trusted) ──

(def ^:private monoid-tactic
  "The discharge stack that proves arithmetic monoid/property laws and CORRECTLY FAILS on
   non-monoids (the kernel won't admit a false law). `(simp (symbol op-name))` unfolds the
   verified op to its body (e.g. psum2 → Nat.add) so omega can finish — the arg MUST be a
   SYMBOL: ansatz's tactic DSL resolves a symbol as a name but elaborates a string as a term."
  (fn [op-name] (list (list 'simp (symbol op-name)) (list 'all_goals (list 'try (list 'omega))))))

(defn- try-prove
  "Prove `nm : prop` over `params` with the monoid tactic stack; true on success, false on
   any failure (then no false licence is registered)."
  [op-name nm params prop]
  (try (a/prove-theorem nm params prop (monoid-tactic op-name)) true (catch Throwable _ false)))

(defn prove-monoid!
  "PROVE (not assert) that the VERIFIED op `op-name` is an associative monoid with identity
   `id-form` over carrier `M-form` (surface forms, e.g. Nat / 0), runtime op `clj-op`, fold init
   `id-literal`. Discharges assoc + left/right-identity via the tactic stack, builds the canonical
   `Std.Associative` instance from the PROVEN assoc theorem, and registers iff all three prove
   (the PROOFS are the licence — kernel-checked). Returns true if proven+registered, else false
   (the op then folds sequentially — no false licence)."
  [op-name M-form id-form clj-op id-literal]
  (let [op (symbol op-name)
        an (str op-name "_assoc") ln (str op-name "_zero_add") rn (str op-name "_add_zero")
        ok (and (try-prove op-name (symbol an) (vector 'a :- M-form 'b :- M-form 'c :- M-form)
                           (list '= M-form (list op (list op 'a 'b) 'c) (list op 'a (list op 'b 'c))))
                (try-prove op-name (symbol ln) (vector 'a :- M-form) (list '= M-form (list op id-form 'a) 'a))
                (try-prove op-name (symbol rn) (vector 'a :- M-form) (list '= M-form (list op 'a id-form) 'a)))]
    (if ok
      (let [Mc (e/const' (name/from-string (str M-form)) [])
            u  (carrier-level @a/ansatz-env Mc)
            ai (build-instance! :assoc op-name u Mc (e/const' (name/from-string op-name) [])
                                (e/const' (name/from-string an) []))]
        (register-monoid! op-name {:clj clj-op :id id-literal :assoc-pf an :assoc-inst ai :left-id ln :right-id rn})
        true)
      (do (println "⚠ defmonoid:" op-name "— could not PROVE the monoid laws; folds sequentially"
                   "(declare ^{:laws {:assoc true}} on an a/foreign to ASSERT them instead)")
          false))))

(defn prove-property!
  "PROVE that the VERIFIED op `op-name` has property `tc` (:comm or :idem) over carrier `M-form`,
   building the canonical `Std.<tc>` instance from the proven law. Returns true iff proven+built."
  [tc op-name M-form]
  (let [op (symbol op-name)
        suffix ({:comm "_comm" :idem "_idempotent"} tc)
        nm (str op-name suffix)
        prop (case tc
               :comm (list '= M-form (list op 'a 'b) (list op 'b 'a))
               :idem (list '= M-form (list op 'x 'x) 'x))
        params (case tc :comm (vector 'a :- M-form 'b :- M-form) :idem (vector 'x :- M-form))]
    (if (try-prove op-name (symbol nm) params prop)
      (let [Mc (e/const' (name/from-string (str M-form)) [])
            u  (carrier-level @a/ansatz-env Mc)
            i  (build-instance! tc op-name u Mc (e/const' (name/from-string op-name) [])
                                (e/const' (name/from-string nm) []))]
        (register-monoid! op-name {(pf-key tc) nm (keyword (str (name tc) "-inst")) i})
        true)
      false)))

(defmacro defmonoid
  "Define a VERIFIED op and try to PROVE it is an associative monoid (identity via `:identity`),
   feeding the proven `Std.Associative` instance to the planner so a fold over it auto-parallelizes.
   The proofs are kernel-checked — if the op isn't actually a monoid the proof fails and it folds
   sequentially (never a false licence). The verified counterpart of `(w/foreign ^{:laws …})`.
     (w/defmonoid mysum [a :- Nat, b :- Nat] Nat (Nat.add a b) :identity 0)"
  [fn-name params ret-type body & {:keys [identity] :or {identity 0}}]
  `(let [v# (a/defn ~fn-name ~params ~ret-type ~body)]
     (prove-monoid! ~(str fn-name) '~ret-type '~identity '~fn-name ~identity)
     v#))

(defmacro foreign
  "Declare a trusted FOREIGN function (a/foreign) and lift any algebraic laws from its name
   metadata `^{:laws {…}}` into the planner. Understood: a monoid via `:assoc true` + `:identity
   <e>` (asserts assoc + identity → the canonical `Std.Associative` instance), plus `:comm true`
   and/or `:idem true` (asserts the matching `Std.Commutative`/`Std.IdempotentOp` instances).
     (w/foreign ^{:laws {:assoc true :identity 0}} mysum [a :- Nat, b :- Nat] Nat (fn [a b] (+ a b)))
   Properties the user asserts are the trust boundary; everything else is exactly a/foreign.
   (The exec/streaming engine has a separate runtime-resolution counterpart for black-box leaves —
   `wandler.exec.mode/register-foreign!` — same 'trusted fn at a kernel type' idea, different layer.)"
  [fn-name params ret-type impl]
  (let [laws (:laws (meta fn-name))
        nm   (vary-meta fn-name dissoc :laws)
        op   (str fn-name)
        Mexpr `(e/const' (name/from-string ~(str ret-type)) [])]
    `(let [v# (a/foreign ~nm ~params ~ret-type ~impl)]
       ~(when (and (map? laws) (:assoc laws) (contains? laws :identity))
          `(assert-monoid! ~op ~Mexpr '~nm ~(:identity laws) (e/lit-nat ~(:identity laws))))
       ~(when (and (map? laws) (:comm laws))
          `(assert-property! :comm ~op ~Mexpr))
       ~(when (and (map? laws) (:idem laws))
          `(assert-property! :idem ~op ~Mexpr))
       v#)))

;; ── the licences (consulted by codegen / optimizer) ──

(defn- has-property?
  "Does `op-name`'s property `tc` (:assoc/:comm/:idem) hold in `env`? — i.e. the registry
   records its proof name and that proof const is present (the licence gate is proof-presence)."
  [env op-name tc]
  (boolean (when-let [pf (get-in @monoids [op-name (pf-key tc)])]
             (some? (kenv/lookup env (name/from-string pf))))))

(defn associative? "Is `op-name`'s associativity proof present in `env` (the re-association licence)?"
  [env op-name] (has-property? env op-name :assoc))

(defn commutative? "Is `op-name`'s commutativity proof present in `env` (→ reorder licence)?"
  [env op-name] (has-property? env op-name :comm))

(defn idempotent? "Is `op-name`'s idempotence proof present in `env` (→ dedup licence)?"
  [env op-name] (has-property? env op-name :idem))

(defn monoid-licence
  "The parallel-fold licence for kernel op `op-name` with fold init `init-clj`: the Clojure
   combine op iff the op is registered, `init-clj` is its identity, the associativity proof is
   present in `env` (the re-association licence), AND both identity proofs are present.
   nil otherwise."
  [env op-name init-clj]
  (when-let [spec (get @monoids op-name)]
    (when (and (= init-clj (:id spec))
               (associative? env op-name)
               (every? #(and % (some? (kenv/lookup env (name/from-string %))))
                       (map spec [:left-id :right-id])))
      (:clj spec))))
