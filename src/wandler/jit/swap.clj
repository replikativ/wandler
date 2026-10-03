(ns wandler.jit.swap
  "Operator swap mechanisms and a guarded adaptive driver.

   Operators are Mealy steps `(state, input) -> [state', output]`. The caller must establish
   equivalence under the guards, compatible state representations, and a safe swap boundary.
   These APIs accept executable functions and do not check certificates. Input-local hypotheses
   use `:guard`; hypotheses involving carried state additionally require `:state-guard`.")

;; ── the mechanism: a swappable operator behind one indirection (mode-indexed) ─────────────────────
(defprotocol PSwapNode
  (current    [node]   "The operator (Mealy step) currently installed.")
  (swap-op!   [node f] "Atomically install operator `f`; return `f`. The caller must establish
                        equivalence, state compatibility, and a safe boundary; this API checks no proof.")
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
     :guard     — optional `(input) -> bool` for input-local hypotheses.
     :state-guard — optional `(state, input) -> bool` for hypotheses involving carried state.
                    At least one guard is required; when both are given, both must hold.
     :state0    — initial Mealy state (default nil).
     :cutoff    — guard-violation count after which we PIN to original permanently (anti-thrash, dflt 3).
   Per input: all supplied guards hold → run optimized; otherwise run ORIGINAL on the SAME input (the guard is a
   pre-check, so fallback is lossless — no element dropped/duplicated), count a violation; at `cutoff`
   violations swap the node to original and stop guarding. State threads across inputs AND across the
   pin. Sharing a state type alone does not establish compatibility: the caller must ensure the
   original can interpret every reachable optimized state, and the state guard discharges every
   carried-state hypothesis before re-entering optimized after a fallback.

   Returns {:outputs :final-state :pinned? :violations :opt-runs :orig-runs :generation}."
  [node {:keys [original optimized guard state-guard state0 cutoff] :or {cutoff 3}} inputs]
  (when-not (or guard state-guard)
    (throw (ex-info "adaptive execution requires an input or state guard" {})))
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
          (if (and (if guard (guard in) true)
                   (if state-guard (state-guard st in) true))
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
