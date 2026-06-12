;; Regenerate docs/SURFACE.md from the vocabulary registry:
;;   clj -M -e '(load-file "dev/gen_surface_md.clj")'
(require '[wandler.surface.vocabulary :as v] '[clojure.string :as str])
(let [rows (v/vocabulary-table)
      by-ns (group-by (fn [[_ m]] (:ns m)) rows)
      sb (StringBuilder.)]
  (.append sb "# The wandler surface vocabulary\n\n")
  (.append sb "> GENERATED from `wandler.surface.vocabulary` — edit there, then `clj -M -e '(load-file \"dev/gen_surface_md.clj\")'`.\n\n")
  (.append sb "The wandler surface is a **type-directed staged elaborator over a closed verb\nvocabulary** (lean4's `elab_rules`, not abstract interpretation): every verb below\nelaborates to a kernel denotation, optimizes under certified rewriting, and lowers\nto the listed runtime form. It is compositional *inside* this vocabulary — verbs\nnest arbitrarily — and explicit about its edge: anything outside it is an honest\nnamed error, never silent miscompilation. `:tier` other than `core` is pre-release\nsurface.\n\n")
  (doseq [[ns- entries] (sort-by (comp str key) by-ns)]
    (.append sb (str "## `" ns- "`\n\n"))
    (.append sb "| verb | signature | dispatch | kernel denotation | runtime lowering | tier |\n|---|---|---|---|---|---|\n")
    (doseq [[sym m] (sort-by (comp str key) entries)]
      (.append sb (str "| `" sym "` | `" (:sig m) "` | " (:dispatch m) " | `" (:denotation m) "` | " (:lowering m) " | " (name (:tier m)) " |\n")))
    (.append sb "\n"))
  (spit "docs/SURFACE.md" (str sb))
  (println "wrote docs/SURFACE.md with" (count rows) "verbs"))
