(ns wandler.jit.async-seq
  "The REAL partial-cps adapter for the verified-JIT swap spine (wandler.jit.swap) — the async corner
   of the mode lattice, on the genuine CPS substrate that spindel itself builds on.

   partial-cps reifies a stream step as a `PAsyncSeq` whose `anext` returns an async expression
   yielding `[value rest-seq] | nil`; the suspension boundary `(await (anext s))` is a quiescent point
   where the prior element is fully resolved and the tail is a transparent, transferable value. We make
   the per-step generator read its operator from a `wandler.jit.swap/PSwapNode` AT EACH `anext`, so a
   `swap-op!` performed between pulls takes effect on the next element — a verified hot-swap at the real
   partial-cps boundary, with already-yielded elements untouched and the generator state carried across.

   This is the foundation the spindel adapter sits on: spindel's spin bodies ARE partial-cps
   continuations, so its swap = this swap + a generation-boundary continuation-invalidation hook."
  (:require [is.simm.partial-cps.sequence :as pseq]
            [is.simm.partial-cps.async :as pa]
            [wandler.jit.swap :as swap]))

(defn run-sync
  "Realize a partial-cps async expression `aexpr` (a `(fn [resolve reject] …)`) to a value
   synchronously. Our generators are pure (no real I/O suspension), so the success continuation fires
   immediately; rethrows on the error continuation."
  [aexpr]
  (let [box (atom ::pending)]
    (aexpr (fn [v] (reset! box [:ok v])) (fn [e] (reset! box [:err e])))
    (let [r @box]
      (when (= r ::pending)
        (throw (ex-info "async expr did not resolve synchronously (real suspension not supported here)" {})))
      (if (= (first r) :err) (throw (second r)) (second r)))))

(defn swappable-aseq
  "A partial-cps `PAsyncSeq` whose per-step generator reads the operator from swap-`node` at EACH
   `anext` — so a swap between pulls lands on the next element. The operator is a pure step
   `(state) -> [value next-state] | nil`; `node` is a `wandler.jit.swap/PSwapNode` (e.g. `generator-node`)
   holding that step. `init-state` seeds the generator."
  [node init-state]
  (pseq/make-generator-seq
    (fn [state] (pa/async ((swap/current node) state)))   ; read the CURRENT op per anext = the swap boundary
    init-state))

(defn realize
  "Pull `aseq` to a finite Clojure vector, synchronously, invoking `(between idx)` after each element
   (the inter-pull point where a `swap-op!` may fire and will be honored on the next element). One-arg
   form uses a no-op hook."
  ([aseq] (realize aseq (fn [_])))
  ([aseq between]
   (loop [s aseq, acc [], i 0]
     (if-let [[v rst] (run-sync (pseq/anext s))]
       (do (between i) (recur rst (conj acc v) (inc i)))
       acc))))
