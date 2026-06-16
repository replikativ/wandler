(ns wandler.laws.semiring
  "The semiring CARRIER REGISTRY — carrier const-name → its ops + the axiom-PROOF const-names the generic
   frame-family laws require. The optimizer's recognizers/emitters (wandler.optimize.physical) read the
   carrier `S` off a fold op's binder type and look the entry up here; the emitter instantiates the
   `_generic` law with the entry's ops + proofs. Each carrier registers its OWN row from where its kernel
   laws are admitted: Nat/Bool in wandler.laws.relational, ℕ∞ tropical in wandler.laws.tropical. Adding a
   semiring = `register!` one row (with that carrier's Init-proven distributive/annihilator/monoid lemma
   names) next to its laws. Soundness still rests entirely on check-constant in the optimizer — a bad row
   can't pass the kernel gate, it just fails to fire."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defonce ^:private registry (atom {}))

(defn register!
  "Register carrier `carrier-name` (a kernel const name, e.g. \"Nat\"/\"Bool\"/\"ENat\") with its entry
   {:add :mul :zero  + the axiom-proof names :hAA :hZA :hAZ :hMA :hMZ :hZM}. Idempotent (last wins)."
  [carrier-name entry]
  (swap! registry assoc carrier-name entry)
  carrier-name)

(defn entry
  "The semiring entry for carrier type `S` (a kernel const), or nil if S is not a registered carrier."
  [S]
  (when (e/const? S) (@registry (name/->string (e/const-name S)))))

(defn const
  "Build the kernel const term for entry field `kw` (e.g. :add → Nat.add / Bool.or / ENat.min)."
  [ent kw]
  (e/const' (name/from-string (get ent kw)) []))

(defn registered
  "The set of currently-registered carrier names (for diagnostics)."
  []
  (set (keys @registry)))
