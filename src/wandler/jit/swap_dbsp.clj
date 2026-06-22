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
