(ns wandler.laws.fusion
  "Phase 3 — the DEFORESTATION ALGEBRA (clean tree). The fusion laws the optimizer rewrites pipelines
   with: collapsing multi-stage map/filter/foldl/flatMap chains to a single pass.

   The core deforestation laws are FREE — they ship in Lean's `Init` (present in the full Init store),
   so the clean tree CITES them by their exact Lean names rather than re-proving (mirrors how
   lean-wandler's reducer fuses definitionally and lean-reducers leans on the stdlib):

     List.map_map        map g ∘ map f      = map (g ∘ f)
     List.filter_filter  filter q ∘ filter p = filter (p && q)
     List.foldl_map      foldl f b ∘ map g  = foldl (f ∘ g·) b
     List.map_flatMap    map h ∘ flatMap f  = flatMap (map h ∘ f)        (and List.flatMap_map)
     List.filterMap_eq_map / filterMap_filter  — the building blocks of the single-pass map∘filter

   `install!` does NOT re-prove these (they are trusted Init); it VERIFIES the deforestation algebra is
   present so a missing/edited store fails fast (the Phase-0 harness gate over the fusion dependency).
   The OWNED single-pass `map∘filter → filterMap` certificate is an OPTIMIZER concern (a codegen rewrite,
   not a foundational law) and lands with the clean optimizer (Phase 5), built from `filterMap_eq_map`
   + `filterMap_filter` above. Requires the full Init store."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

(def deforestation-laws
  "The free Init deforestation lemmas the clean optimizer fuses with."
  ["List.map_map" "List.filter_filter" "List.foldl_map"
   "List.map_flatMap" "List.flatMap_map"
   "List.filterMap_eq_map" "List.filterMap_filter"])

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn available?
  "Is the full deforestation algebra present in the current env? → {:ok? bool :missing [names]}."
  []
  (let [missing (vec (remove has? deforestation-laws))]
    {:ok? (empty? missing) :missing missing}))

(defn install!
  "Verify the deforestation algebra is present (the fusion laws are free from Init — nothing to prove).
   Returns :installed when all present; throws with the missing names otherwise (fail-fast on a
   missing/edited store)."
  []
  (let [{:keys [ok? missing]} (available?)]
    (when-not ok?
      (throw (ex-info (str "fusion: deforestation laws absent from the env (need the full Init store): "
                           missing)
                      {:missing missing})))
    :installed))
