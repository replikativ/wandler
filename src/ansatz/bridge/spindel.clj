(ns ansatz.bridge.spindel
  "OPTIONAL Forkable over a live spindel FRP system — the O(1) copy-on-write fork the streaming JIT
   speculates on for an EFFECTFUL source (a running spindel graph), vs. the trivial value-copy
   `ansatz.fork/atom-cell` used for a pure coalgebra. Follows the ansatz.bridge doctrine: NO hard
   dependency. Every spindel fn is `requiring-resolve`d, so this namespace LOADS with or without
   spindel on the classpath — absent spindel just makes `detect?` false and `spindel-cell` throw a
   clear error. Put ../spindel on the classpath via the `:spindel` deps alias to use it.

   Maps onto spindel's `org.replikativ.spindel.engine.context`:
     snapshot ← snapshot-context   fork ← fork-context (OverlayBackend, O(1) CoW)   restore! ← restore-snapshot"
  (:require [ansatz.fork :as fork]))

(def ^:private ctx-ns "org.replikativ.spindel.engine.context")
(defn- rr [fn-name] (try (requiring-resolve (symbol ctx-ns fn-name)) (catch Throwable _ nil)))

(defn detect?
  "True iff a spindel context backend is on the classpath."
  []
  (boolean (rr "fork-context")))

(deftype SpindelCell [ctx-atom]
  fork/Forkable
  (snapshot [_]   ((rr "snapshot-context") @ctx-atom))
  (fork     [_]   (SpindelCell. (atom ((rr "fork-context") @ctx-atom))))
  (restore! [this s] (reset! ctx-atom ((rr "restore-snapshot") s)) this)
  (current  [_]   @ctx-atom))

(defn spindel-cell
  "Wrap a live spindel ExecutionContext as an `ansatz.fork/Forkable`. fork = spindel's O(1) CoW
   OverlayBackend fork; snapshot/restore = spindel's serializable ImmutableBackend. Requires
   ../spindel on the classpath (else throws)."
  [ctx]
  (when-not (detect?)
    (throw (ex-info "spindel not on the classpath — add the :spindel deps alias (../spindel)" {})))
  (SpindelCell. (atom ctx)))
