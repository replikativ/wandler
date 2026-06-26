(ns wandler.jit.swap-dbsp
  "DBSP (differential) PSwapNode adapter — Case A: the RECOMPUTE-FREE swaps, where the target circuit's
   integrator state is a subset of the source's. The differential corner of the mode lattice.

   A live DBSP node owns an INTEGRATOR ∫ (a `join-node`'s `[L R V]`, a `linear-node`'s running `out`) and
   applies a certified differential step per delta. Two facts make a mid-stream swap clean:

     • The OUTPUT delta stream is identical under two certified-≡ circuits: δQ(n) = Q(Iₙ)−Q(Iₙ₋₁) is a
       function of Q and the inputs only, so Q≡Q' ⇒ δQ=δQ' at every step. The running view (`out`) therefore
       carries verbatim and downstream sees NO glitch.

     • The integrator splits into SOURCE integrators (the accumulated inputs — topology-independent, carry
       verbatim) and DERIVED integrators (materialized sub-results — topology-specific). Case A is exactly
       the swaps where the target needs NO derived integrator the source lacks:
         A1  leaf-operator swap inside a node (kf→kf', ops fn→fn', extensionally ≡): the integrator
             ([L R V] / out) is carried VERBATIM — the derived view stays correct because the leaf is ≡.
         A2  state-REDUCING node replacement (group-by-elim / filter-elim / fusion: join/group_by node →
             linear node): carry the OUTPUT into the new node, DROP the old derived integrator; the new
             node needs ⊆ state (stateless map / a leaner chain), so nothing is rematerialized.

   Case B (a target that introduces a NEW derived integrator — join reorder, index build) needs a
   batch REMATERIALIZE of that integrator from the carried sources, cost-gated; it is a separate piece.

   The per-step operator is read from a `wandler.jit.swap/PSwapNode` cell at each delta, so a `swap-op!`
   between deltas lands on the next delta. The integrator atoms are owned by the node and never touched
   by `swap-op!` — that is what makes ∫ carry across the swap. In-repo (DBSP is core wandler)."
  (:require [wandler.exec.zset :as zs]
            [wandler.jit.swap :as swap]))

(defn- apply-ops
  "Run a linear leaf-op chain over a Z-set `v` (filter/map keep it a Z-set; sum folds to a number) — the
   linear differential (DBSP Thm 5.4 / Mode.diff_async_dist). Mirrors wandler.exec.live/apply-ops."
  [v ops]
  (reduce (fn [v [op a]] (case op :filter (zs/z-filter a v) :map (zs/z-map a v) :sum (zs/z-sum a v)))
          v ops))

;; ── A1: leaf-operator swap inside a node — integrator carried verbatim ─────────────────────────────
(defn swappable-linear-node
  "A live linear node (filter/map/sum chain) whose `ops` are read from swap-`opnode` at each push. A
   `swap-op!` installs new leaf fns WITHOUT touching the running accumulator `:out`, so ∫ is carried.
   The output type (hence `sum?`) is invariant under a certified-≡ swap; fixed from the initial ops."
  [opnode]
  (let [sum? (boolean (some #(= :sum (first %)) (swap/current opnode)))
        out  (atom (if sum? 0 {})) subs (atom [])]
    {:push! (fn [d]
              (let [od (apply-ops d (swap/current opnode))
                    nv (if (number? od) (+ @out od) (zs/z-add @out od))]
                (reset! out nv)
                (doseq [g @subs] (g od))
                od))
     :out out
     :subscribe (fn [g] (swap! subs conj g))}))

(defn swappable-join-node
  "A live join node whose `[kf lf]` are read from swap-`opnode` at each push. The bilinear integrator
   `[L R V]` is owned by the node and carried verbatim across a swap — `kf`/`lf` must be certified ≡, so
   the carried view `V` stays the correct join of the (unchanged) running inputs `L`,`R`."
  [opnode]
  (let [state (atom [{} {} {}]) out (atom {}) subs (atom [])]
    {:push! (fn [delta]
              (let [[kf lf] (swap/current opnode)
                    [_ _ V] (swap! state #(zs/join-step kf lf % delta))
                    dv      (zs/z-add V (zs/z-negate @out))]
                (reset! out V)
                (doseq [g @subs] (g dv))
                V))
     :out out
     :subscribe (fn [g] (swap! subs conj g))
     :state state}))                               ; exposed so a swap/migration can inspect ∫

;; ── A2: state-reducing node replacement — carry the output, drop the old derived integrator ────────
(defn carry-output!
  "State-REDUCING swap (Case A2): hand the OLD node's running view to a NEW node so the view is
   continuous (downstream sees no glitch — δQ'=δQ by Q≡Q'), then the old derived integrator is dropped.
   Re-subscribes the old node's downstream edges to the new node. SOUND ONLY when the new node needs ⊆
   the old node's state (the target materializes no new intermediate — the elimination/fusion
   direction). Returns `new`."
  [old new]
  (reset! (:out new) @(:out old))                  ; carry the integrated output (the only shared state)
  new)

;; ── Case B: REMATERIALIZE a new derived integrator from the carried sources ────────────────────────
(defn rematerialize-join
  "Case B: build a join node whose derived view `V'` is REMATERIALIZED by a from-scratch batch z-join
   over the carried SOURCE integrators `L`,`R` (rather than carried), via the new `[kf lf]` in `opnode`.
   Sound for ANY query-≡ swap that changes the materialized intermediate (join reorder, re-key) — where
   carrying V (Case A) would corrupt, because the past contributions were keyed by the OLD op. Cost =
   O(|L|·|R|), charged ONCE at the swap (gate with `rematerialize-cost`). Returns a swappable-join-node
   primed at `[L R V']`, ready to continue incrementally. `L`,`R` are the source integrators of the node
   being replaced (`(let [[L R _] @(:state old)] …)`)."
  [opnode L R]
  (let [[kf lf] (swap/current opnode)
        node    (swappable-join-node opnode)
        V'      (zs/z-join kf lf L R)]
    (reset! (:state node) [L R V'])                ; rematerialize the derived view from the sources
    (reset! (:out node) V')
    node))

(defn rematerialize-cost
  "Work-unit estimate for rematerializing a join intermediate: the from-scratch z-join is O(|L|·|R|)."
  [L R] (* (max 1 (count L)) (max 1 (count R))))

(defn rematerialize-worth-it?
  "Case-B cost gate: adopt the rematerializing swap iff the ONE-TIME rematerialize cost is repaid by the
   per-delta saving over the expected remaining deltas (the amortization run-adaptive uses, with a
   non-zero swap cost). `saving-per-delta`, `remaining-deltas` are profile estimates."
  [L R saving-per-delta remaining-deltas]
  (< (rematerialize-cost L R) (* (max 0.0 (double saving-per-delta)) (max 0 (long remaining-deltas)))))

;; ── end-to-end: express a DBSP step as a run-adaptive MEALY step (the integrator IS the threaded state) ─
;; `wandler.jit.swap/run-adaptive` threads its `state` across every operator swap and, on a guard
;; violation, runs the OTHER operator on the SAME state. For a DBSP step the threaded state is the
;; integrator, so run-adaptive's state-threading IS the integrator carry — the guarded adaptive loop
;; (guard / lossless fallback / anti-thrash pin) drives a differential circuit with NO new policy code.
;; These helpers are the functional dual of the atom-backed swappable-*-node above.
(defn join-mealy
  "An incremental join as a run-adaptive Mealy step over the integrator `[L R V]`:
   `(state, [δL δR]) → [state', V']`. Drive a certified-≡ pair (e.g. a robust kf vs a refinement-fast
   kf) with `run-adaptive` + a per-delta guard to get the guarded adaptive loop over a DBSP join."
  [kf lf]
  (fn [state delta] (let [s' (zs/join-step kf lf state delta)] [s' (nth s' 2)])))

(defn linear-mealy
  "A linear filter/map/sum chain as a run-adaptive Mealy step over the running accumulator:
   `(state, δ) → [state', δ-out]`. `state0` is `0` for a `:sum` chain, `{}` otherwise."
  [ops]
  (fn [state delta]
    (let [od (apply-ops delta ops)
          nv (if (number? od) (+ state od) (zs/z-add state od))]
      [nv od])))
