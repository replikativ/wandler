(ns wandler.exec.jit
  "Verified hot-swap JIT for streaming pipelines (docs/COST_MODEL_REDESIGN, the JIT story).

   THE PROPERTY that makes this different from every other JIT: every plan wandler compiles is
   kernel-PROVEN equal to the original (translation validation). So replacing the running code mid-stream
   CANNOT change the answer -- only the speed. No deopt guards, no speculation rollback: a hot-swap is a
   `reset!`. Profiling STEERS the swap; the kernel GUARANTEES the result.

   THE LOOP: stream -tap(sampled)-> profile {size, selectivity, ndv, drift}; on stabilize/drift,
   d/dt(optimize-measured(profile, batch-term)) [= original] -recompile-> swap-cell.reset!; each window
   calls @cell; results identical across every swap (the proof guarantees it).

   How a STREAM is optimized with the BATCH planner: the planner optimizes the FINITE per-step (window
   / delta) List term against sampled full-stream cardinalities; the d/dt (differentiation) pass re-embeds
   the optimized plan as a sequential, coinductive operator (d/dt commutes with the optimizer,
   kernel-certified). The planner never sees the infinite stream.

   This ns ships the KEYSTONE (swap-cell) and the SELF-DRIVING LOOP (jit-stream): a sampled tap feeds the
   cost-parameter estimator, the trigger re-plans + recompiles + hot-swaps."
  (:require [ansatz.kernel.expr :as e]))

(defn swap-cell
  "A hot-swappable code cell. Holds the current compiled fn in an atom; `:call` invokes it through ONE
   indirection; `:swap!` atomically replaces it (returns the new fn); `:current` reads it; `:generation`
   counts swaps (for telemetry / hysteresis). Sound to swap mid-stream because every wandler-compiled
   plan is kernel-certified ≡ the original — the swap changes speed, never results."
  [init-fn]
  (let [cell (atom {:fn init-fn :gen 0})]
    {:cell       cell
     :call       (fn [& args] (apply (:fn @cell) args))
     :swap!      (fn [new-fn] (:fn (swap! cell (fn [c] {:fn new-fn :gen (inc (:gen c))}))))
     :current    (fn [] (:fn @cell))
     :generation (fn [] (:gen @cell))}))

(defn drive-windows
  "Run a windowed stream THROUGH a swap-cell: apply `(:call cell)` to each window in `windows` in order,
   optionally invoking `(on-window idx)` between windows (where a tap/replan would fire a `:swap!`).
   Returns the vector of per-window results. The coinductive driver is fixed; only the per-window
   operator in the cell is hot-swapped — so the stream keeps flowing across recompilations."
  ([cell windows] (drive-windows cell windows (fn [_])))
  ([cell windows on-window]
   (let [call (:call cell)]
     (reduce (fn [acc [idx w]] (let [r (call w)] (on-window idx) (conj acc r)))
             [] (map-indexed vector windows)))))

(defn- close-lctx
  "λ-abstract a per-window kernel `term` over its single source fvar `source-id` (type from `lctx`)."
  [term lctx source-id]
  (e/lam (or (:name (lctx source-id)) "w") (:type (lctx source-id)) (e/abstract1 term source-id) :default))

(defn jit-stream
  "THE self-driving verified JIT loop over a windowed stream. `term` is a per-window kernel over a single
   source fvar `source-id` (`lctx` gives its type). Compiles `term` to an initial operator in a swap-cell,
   drives `windows` through it; a sampled TAP accumulates evidence; after `warmup` windows the TRIGGER
   re-estimates the cost knobs from the sample (`cost-params`: measured :ndv/:sizes/:selectivity ⊕ priors),
   re-optimizes `term` against them, and — if the re-plan kernel-certifies AND is cheaper — recompiles and
   HOT-SWAPS the operator. Subsequent windows run the swapped operator. Every operator is certified ≡
   `term`, so the swap is sound: results are identical across it, only speed changes.

   Returns {:results [per-window] :swaps n :plan final-term :cost-before :cost-after}. Opts: :key-of (the
   join-key λ for :ndv evidence), :priors (refinement priors), :warmup (windows before the trigger, dflt 1)."
  [env term lctx source-id windows & {:keys [key-of priors warmup] :or {warmup 1}}]
  (let [pcost   (requiring-resolve 'wandler.optimize.cost/pipeline-cost)
        optc    (requiring-resolve 'wandler.optimize/optimize-cost)
        a->clj  (requiring-resolve 'ansatz.core/ansatz->clj)
        cparams (requiring-resolve 'wandler.jit.estimate/cost-params)
        compile (fn [t] (eval (a->clj env (close-lctx t lctx source-id) [])))
        cell    (swap-cell (compile term))
        sample  (atom []), results (atom []), swaps (atom 0)
        plan    (atom term)]
    (doseq [[idx w] (map-indexed vector windows)]
      (swap! results conj ((:call cell) w))
      (swap! sample into w)
      (when (= idx (dec (long warmup)))                 ; TRIGGER: re-plan once warmup evidence is in
        (let [params (cparams env term (cond-> {:sample @sample :source-id source-id}
                                         key-of (assoc :key-of key-of)
                                         priors (assoc :priors priors)))
              r (apply optc env term :lctx lctx (mapcat identity (select-keys params [:sizes :selectivity :ndv])))]
          (when (and (:verified? r) (:changed? r)
                     (< (double (pcost (:term r) params)) (double (pcost term params))))
            (reset! plan (:term r))
            ((:swap! cell) (compile (:term r)))
            (swap! swaps inc)))))
    {:results @results :swaps @swaps :plan @plan
     :cost-before (double (pcost term {})) :cost-after (double (pcost @plan {}))}))
