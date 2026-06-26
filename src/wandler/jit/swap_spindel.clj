(ns wandler.jit.swap-spindel
  "Spindel (reactive) PSwapNode adapter — the reactive corner of the mode lattice, on the substrate
   that BUILDS ON partial-cps (spindel spin bodies are partial-cps continuations, so this swap is the
   wandler.jit.async-seq swap + a reactive invalidation hook).

   The seam the exploration flagged: spindel's cold path reads a spin's body, but reactive RE-runs
   execute continuation closures that don't reference it — so swapping the body alone is silently
   ignored until the continuations are invalidated. We express that coupling through spindel's PUBLIC
   dirty mechanism: the node owns a `version` signal, and `swap-op!` installs the new operator AND
   bumps the version, so any spin that `(track …)`s the version re-runs with the new operator. Because
   every wandler-compiled operator is kernel-certified ≡ the one it replaces, the re-run produces the
   SAME value (glitch-free downstream) — only faster. The content-addressed spin-id keeps the node,
   cache, observers, and deps; only the operator changes; the dependency graph is never rebuilt.

   Requires the optional `:spindel` dep — do not require this ns on the default classpath.

   `swap-op!` must run with the execution context bound; it binds the node's captured `ctx` itself, so
   it is safe to call from outside a spin body."
  (:require [org.replikativ.spindel.core :as sp]
            [wandler.jit.swap :as swap]))

(defrecord SpindelNode [cell version ctx]
  swap/PSwapNode
  (current    [_]   (:fn @cell))
  (swap-op!   [_ f] (let [r (:fn (swap! cell (fn [c] {:fn f :gen (inc (:gen c))})))]
                      (sp/with-context ctx (swap! version inc))   ; couple install + invalidation
                      r))
  (generation [_]   (:gen @cell)))

(defn spindel-node
  "A reactive PSwapNode in execution context `ctx`, holding operator `init-fn` and a fresh `version`
   signal. Wire it into a spin via `(track (version-signal node))` + `((swap/current node) input)`:
   the spin re-runs (with the new operator) whenever `swap-op!` fires."
  [ctx init-fn]
  (->SpindelNode (atom {:fn init-fn :gen 0}) (sp/signal ctx 0) ctx))

(defn version-signal
  "The node's `version` signal — `(track …)` it inside the spin body so a swap forces a re-run."
  [^SpindelNode n]
  (:version n))
