(ns wandler.fork
  "The FORK/SNAPSHOT substrate the streaming JIT speculates on — an abstract cell of stream/system
   state that supports NON-DESTRUCTIVE speculation: snapshot it, fork an independent copy, run
   candidate plans on the fork, commit the winner. Ansatz has NO hard dependency on any fork backend
   (same doctrine as wandler.bridge): the trivial `atom-cell` impl here makes the JIT testable
   standalone, and `wandler.bridge.spindel` provides an O(1) copy-on-write impl over a live spindel
   FRP system when `../spindel` is on the classpath.

   For a PURE coalgebra (seed is an immutable value) speculation is free — `unfold-take` a sample from
   the seed disturbs nothing — so `atom-cell` suffices. Fork matters only for an EFFECTFUL live system
   (mutable node state), which is exactly what spindel's OverlayBackend forks in O(1)."
  (:refer-clojure :exclude [fork]))

(defprotocol Forkable
  "A cell of speculatable state."
  (snapshot [this]   "→ an opaque immutable snapshot of the current state")
  (fork     [this]   "→ a new, independent Forkable initialized from this one's state (CoW where able)")
  (restore! [this s] "set this cell's state from a snapshot `s`; returns this")
  (current  [this]   "→ the current state value"))

(deftype AtomCell [a]
  Forkable
  (snapshot [_]   @a)
  (fork     [_]   (AtomCell. (atom @a)))
  (restore! [this s] (reset! a s) this)
  (current  [_]   @a))

(defn atom-cell
  "A trivial in-memory Forkable over a Clojure atom. fork = independent copy (full copy, not CoW —
   fine for values / the test path). The spindel adapter replaces this with structural-sharing CoW."
  [init]
  (AtomCell. (atom init)))

(defn speculate
  "Run `f` against a FORK of `cell` (so the live cell is untouched), returning `(f fork-cell)`.
   The caller decides whether to `restore!` the live cell from the fork's result — speculation is
   non-destructive by construction. This is the kernel of fork-based JIT (and, with the same shape,
   SMC resample / MCMC propose in the inference agenda — try on a fork, commit the winner)."
  [cell f]
  (f (fork cell)))
