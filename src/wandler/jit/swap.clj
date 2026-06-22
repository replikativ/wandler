(ns wandler.jit.swap
  "The MODE-INDEXED hot-swap mechanism + the SUBSTRATE-AGNOSTIC adaptive policy — the spine of the
   verified JIT (see docs/COST_MODEL_REDESIGN, [[verified-stream-jit]], [[modal-mode-lattice]]).

   The recontextualization: a swap is the SAME operation in every substrate (batch / async-seq /
   spindel / DBSP), because each reifies its per-step operator as a REPLACEABLE VALUE behind one
   indirection, has a QUIESCENT BOUNDARY where no element is in flight, and holds state whose TYPE the
   kernel proof preserves (so migration across a swap is IDENTITY, never reconstruction). We split that
   into two layers:

     • `PSwapNode` — the MECHANISM: a swappable operator cell, one impl per substrate (mode-indexed).
       `AtomNode` (this ns) is the batch impl; `generator-node` is the async-seq (partial-cps
       GeneratorSeq) impl; spindel (Spin.spin-fn cell + continuation invalidation) and DBSP (stage fn +
       carried ∫) are follow-on impls behind the same protocol.

     • `run-adaptive` — the POLICY: the mode-AGNOSTIC guarded-adaptive driver. It only speaks
       `PSwapNode` + Mealy-step operators, so it works in every substrate unchanged. It mirrors
       HotSpot's speculation-with-deopt, but our 'speculation' is a kernel-PROVED equivalence whose
       HYPOTHESIS is checked by a runtime guard, and our 'deopt' is calling the other certified operator
       (no frame/state reconstruction — same type). The one thing the proof does NOT give us is
       anti-thrash, so we add HotSpot's trap-history: after `cutoff` guard violations, PIN to the
       original permanently and stop guarding.

   Operators are MEALY STEPS `(state, input) -> [state', output]` so state threads across inputs AND
   across a swap (a stateless map ignores `state`; a running aggregate / DBSP integrator carries it).
   The certified operator PAIR (original + optimized, optimized sound only when the guard holds) comes
   from `wandler.adaptive`; this ns is the mechanism + policy that DRIVES that pair over a stream.")

;; ── the mechanism: a swappable operator behind one indirection (mode-indexed) ─────────────────────
(defprotocol PSwapNode
  (current    [node]   "The operator (Mealy step) currently installed.")
  (swap-op!   [node f] "Atomically install operator `f`; return `f`. Sound mid-stream because every
                        wandler-compiled operator is kernel-certified ≡ the one it replaces.")
  (generation [node]   "Number of swaps performed (telemetry / hysteresis)."))

;; batch adapter — the existing swap-cell as a record. One atom, one indirection.
(defrecord AtomNode [cell]
  PSwapNode
  (current    [_]   (:fn @cell))
  (swap-op!   [_ f] (:fn (swap! cell (fn [c] {:fn f :gen (inc (:gen c))}))))
  (generation [_]   (:gen @cell)))

(defn atom-node
  "A batch swap node holding `init-fn` (a Mealy step). The batch corner of the mode lattice."
  [init-fn]
  (->AtomNode (atom {:fn init-fn :gen 0})))

;; async-seq adapter — partial-cps GeneratorSeq shape: a `generator-fn` read THROUGH the cell, so a
;; swap between pulls takes effect on the next element. (Dependency-free here; the partial-cps binding
;; is `make-generator-seq` over the same cell — its `anext` is exactly this pull boundary.)
(defrecord GeneratorNode [cell]
  PSwapNode
  (current    [_]   (:fn @cell))
  (swap-op!   [_ f] (:fn (swap! cell (fn [c] {:fn f :gen (inc (:gen c))}))))
  (generation [_]   (:gen @cell)))

(defn generator-node [init-gen-fn] (->GeneratorNode (atom {:fn init-gen-fn :gen 0})))

;; ── the policy: substrate-agnostic guarded-adaptive driving ───────────────────────────────────────
(defn run-adaptive
  "Drive `inputs` through swap-`node` (starting with `optimized` installed) under the guarded-adaptive
   policy. `opts`:
     :original  — the always-correct certified operator (Mealy step).
     :optimized — the certified-cheaper operator, sound ONLY when `:guard` holds (e.g. group-by
                  elimination under an abduced unique key). Installed initially.
     :guard     — `(input) -> bool`: discharges the optimized operator's hypothesis on this input.
     :state0    — initial Mealy state (default nil).
     :cutoff    — guard-violation count after which we PIN to original permanently (anti-thrash, dflt 3).
   Per input: guard holds → run optimized; guard fails → run ORIGINAL on the SAME input (the guard is a
   pre-check, so fallback is lossless — no element dropped/duplicated), count a violation; at `cutoff`
   violations swap the node to original and stop guarding. State threads across inputs AND across the
   pin (identity migration — both operators are certified ≡ over the same state type).

   Returns {:outputs :final-state :pinned? :violations :opt-runs :orig-runs :generation}."
  [node {:keys [original optimized guard state0 cutoff] :or {cutoff 3}} inputs]
  (swap-op! node optimized)
  (loop [ins inputs, st state0, outs (transient [])
         viol 0, opt 0, orig 0, pinned? false]
    (if (empty? ins)
      {:outputs (persistent! outs) :final-state st :pinned? pinned?
       :violations viol :opt-runs opt :orig-runs orig :generation (generation node)}
      (let [in (first ins)]
        (if pinned?
          (let [[st' out] ((current node) st in)]          ; pinned: original only, no guard cost
            (recur (rest ins) st' (conj! outs out) viol opt (inc orig) true))
          (if (guard in)
            (let [[st' out] (optimized st in)]             ; fast path: hypothesis holds
              (recur (rest ins) st' (conj! outs out) viol (inc opt) orig false))
            (let [[st' out] (original st in)               ; deopt: run original on the SAME input
                  viol'     (inc viol)
                  pin?      (>= viol' cutoff)]
              (when pin? (swap-op! node original))         ; anti-thrash: pin + stop guarding
              (recur (rest ins) st' (conj! outs out) viol' opt (inc orig) pin?))))))))

;; ── async-seq driving: pull outputs lazily, swap takes effect between pulls ────────────────────────
(defn pull-seq
  "Lazily pull a sequence of outputs from a `generator-node` whose operator is a generator step
   `(state) -> [output state']` (or nil at end). Each element reads the CURRENT operator, so a
   `swap-op!` performed between pulls takes effect on the NEXT element — the partial-cps
   `(await (anext s))` boundary, where the prior element is fully resolved and the tail state is a
   transparent transferable value. Already-yielded elements are never disturbed by a swap."
  [node state]
  (lazy-seq
    (when-let [[out state'] ((current node) state)]
      (cons out (pull-seq node state')))))
