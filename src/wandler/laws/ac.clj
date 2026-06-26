(ns wandler.laws.ac
  "AC instance providers for wandler's additive monoids, feeding ansatz's `ac_rfl` tactic.

   `ac_rfl` (the reflection-based AC/monoid normalizer, `ansatz.tactic.ac`) obtains an operator's
   `Std.Associative` / `LawfulIdentity` instances via `instance/synthesize` first, then falls back to
   a per-operator PROVIDER registry — the deterministic analog of `synthInstance` for PSS envs where
   multi-arg `outParam` class synthesis is name-fragile. Here we register providers for the additive
   operators of `WAddMonoid` and `WSemiring` (the aggregation monoids the FAQ frame/linearity laws
   reassociate over), built straight from the structures' projection lemmas — exactly the same lemmas
   `wandler.semiring-class` uses to construct the instances, so the kernel checks them line up.

   Only the ADDITIVE operators are registered: the fragment's `mul` is non-associative by design, and
   multiplicative distribution is carried by `foldl_const_mul_pull`, not AC normalization."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.ac :as ac]))

(def ^:private o (lvl/succ lvl/zero))
(defn- c [s ls] (e/const' (nm/from-string s) ls))
(defn- args-of [op] (second (e/get-app-fn-args op)))

(defn- register-monoid-provider!
  "Register an AC provider for an additive monoid whose operator head-const is `add-name` and whose
   projection lemmas `assoc`/`zero`/`zero_add`/`add_zero` each take `(S inst)`. The carrier is `Sort
   1` (so all class levels are 1). `:assoc` builds `Std.Associative.mk`; `:identity` recognizes the
   monoid's `zero` as the neutral and builds the `Std.LawfulIdentity` instance from `zero_add`/
   `add_zero` (its parent marker/lawful sub-instances assembled inline)."
  [add-name assoc zero zero-add add-zero-lemma]
  (ac/register-ac-op! add-name
    {:assoc (fn [carrier op]
              (let [[S inst] (args-of op)]
                (e/app* (c "Std.Associative.mk" [o]) carrier op (e/app* (c assoc []) S inst))))
     :identity (fn [carrier op atom]
                 (let [[S inst] (args-of op)
                       zero-e (e/app* (c zero []) S inst)]
                   (when (.equals ^Object atom ^Object zero-e)
                     (let [leftId  (e/app* (c "Std.LeftIdentity.mk" [o o]) carrier carrier op zero-e)
                           rightId (e/app* (c "Std.RightIdentity.mk" [o o]) carrier carrier op zero-e)
                           ident   (e/app* (c "Std.Identity.mk" [o]) carrier op zero-e leftId)
                           lli (e/app* (c "Std.LawfulLeftIdentity.mk" [o o]) carrier carrier op zero-e
                                       leftId (e/app* (c zero-add []) S inst))
                           lri (e/app* (c "Std.LawfulRightIdentity.mk" [o o]) carrier carrier op zero-e
                                       rightId (e/app* (c add-zero-lemma []) S inst))]
                       (e/app* (c "Std.LawfulIdentity.mk" [o]) carrier op zero-e ident lli lri)))))}))

(defn register!
  "Register the AC providers for `WAddMonoid.add` and `WSemiring.add` (idempotent). Call before any
   proof that uses `ac_rfl` over these operators."
  []
  (register-monoid-provider! "WAddMonoid.add"
    "WAddMonoid.add_assoc" "WAddMonoid.zero" "WAddMonoid.zero_add" "WAddMonoid.add_zero")
  (register-monoid-provider! "WSemiring.add"
    "WSemiring.add_assoc" "WSemiring.zero" "WSemiring.zero_add" "WSemiring.add_zero")
  :registered)
