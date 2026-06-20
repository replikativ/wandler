(ns wandler.clean.surface.core
  "Phase 6 (clean tree) — THE SURFACE FRONT DOOR. Aggregates the clean surface vocabulary so a single
   require installs everything a user needs to write ordinary Clojure collection + relational queries
   inside a verified `a/defn` body and have them elaborate to kernel `List.*`/`Map.*` terms (which the
   clean optimizer then certifies + lowers).

   Clean-tree port of the old per-module `wandler.surface.*` (collections + relational), severing the
   dependency on old wandler so this tree stands alone at cutover (Phase 7). Each module is IR-agnostic
   (it only emits kernel Exprs via `ansatz.surface.api`/`ansatz.core`; the optimization LAWS live in
   `wandler.clean.laws.*` and the runtime lowering is shared). Requiring this namespace triggers each
   module's load-time `(install!)`; `install!` here re-runs them idempotently for explicit control.

   Load order: `wandler.clean.surface.relational` emits `Map.join`/`Map.group_by`/`AList.*` constants,
   so the kmap kernel prelude must already be in the env (installed by `wandler.clean.laws.bucket/install!`
   or the old `wandler.kmap`). Collection verbs need nothing beyond Init."
  (:require [wandler.clean.surface.common]
            [wandler.clean.surface.collections :as collections]
            [wandler.clean.surface.relational :as relational]
            ;; the dynamic EDN `Value` universe is an ANSATZ capability (shared) — the clean tree installs
            ;; it, it does not re-port it. Opt-in (heavyweight: defines the Value inductive + ops).
            [ansatz.surface.data :as data]
            ;; the shared runtime codegen lowering registry (List.*/Map.* → Clojure) — auto-installs at
            ;; load, so surface-elaborated `a/defn` bodies EXECUTE. Self-contained: don't rely on another
            ;; namespace having loaded it. (Clean runtime is a deferred Phase-2-remainder; until cutover
            ;; the clean surface rides the existing wandler.runtime, as wandler.exec.mode already does.)
            [wandler.runtime]))

(defn install!
  "Idempotently (re-)install the clean surface vocabulary into the process-global elaborator registries.
   Collection verbs first (relational reuses `coll/list-elem`/`compile-fn`), then relational. Safe to
   call repeatedly — registration overwrites. Returns nil."
  []
  (collections/install!)
  (relational/install!)
  nil)

(defn install-value!
  "OPT-IN: bring up the dynamic EDN `Value` front door — define the `Value` type + core ops on the
   current env (`ansatz.surface.data/install-core!`) and register the native-Clojure-over-`Value`
   surface verbs (`get`/`contains?`/`keys`/`vals`/`int?`/`map?`/… ; `data/install-surface!`). Lets
   ordinary dynamic Clojure map/coll code run over kernel-verified `Value` (via `edn->value`/`value->edn`).
   Heavyweight (defines an inductive) — kept separate from `install!`. Requires Init in the env. Returns
   the updated env."
  []
  (let [env (data/install-core!)]
    (data/install-surface!)
    env))
