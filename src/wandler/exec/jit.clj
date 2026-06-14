(ns wandler.exec.jit
  "Verified hot-swap JIT for streaming pipelines (docs/COST_MODEL_REDESIGN, the JIT story).

   THE PROPERTY that makes this different from every other JIT: every plan wandler compiles is
   kernel-PROVEN equal to the original (translation validation). So replacing the running code mid-stream
   CANNOT change the answer — only the speed. No deopt guards, no speculation rollback: a hot-swap is a
   `reset!`. Profiling STEERS the swap; the kernel GUARANTEES the result.

   THE LOOP (the pieces, composed elsewhere):
     stream ──tap(sampled)──▶ profile {size, selectivity, ndv, drift}     (parallel, cheap)
        │                          │  on stabilize/drift
        ▼                          ▼
     swap-cell ◀──reset!── recompile ◀── ∂(optimize-measured(profile, batch-term))   [≡ original]
        │
        ▼ each window calls @cell
     results ── identical across every swap (the proof guarantees it)

   How a STREAM is optimized with the BATCH planner: the planner optimizes the FINITE per-step (window
   / delta) `List` term against sampled full-stream cardinalities; the `∂` pass re-embeds the optimized
   plan as a sequential, coinductive operator (∂ commutes with the optimizer, kernel-certified). The
   planner never sees the infinite stream.

   This ns ships the KEYSTONE — the swap-cell. The sampled tap + drift-triggered replan layer on top.")

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
