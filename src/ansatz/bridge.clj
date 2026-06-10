(ns ansatz.bridge
  "OPTIONAL α/γ bridge between external query engines (datahike, stratum, …) and the Ansatz kernel
   IR, via the plan lens (ansatz.plan). Ansatz has NO hard dependency on any engine — an engine is
   described by an adapter map registered with `register-engine!`, and the optional adapter
   namespaces (ansatz.bridge.<engine>) `requiring-resolve` the engine, so if it isn't on the
   classpath the adapter simply doesn't load and the bridge stays empty.

   The flow — optimize a cross-engine query ONCE, in the certified kernel IR:

       engine logical IR ──(α: adapter :lift)──▶ ansatz PLAN ──plan->term──▶ kernel TERM
                                                                                  │
                                                              optimize-cost (CERTIFIED rewrites:
                                                              fusion / pushdown / semijoin / …)
                                                                                  │
       engine physical exec ◀──(γ: adapter :lower)── ansatz PLAN ◀──term->plan──◀ kernel TERM'
                                                                            (+ proof TERM = TERM')

   The middle is engine-agnostic: a plan that mixes datahike `q`, stratum scans, and Clojure
   transducers optimizes across the seams with a kernel certificate, then γ-lowers per executor.

   An adapter is a map:
     :detect?  (fn [] → bool)              — is the engine present? (guards optional loading)
     :lift     (fn [engine-ir] → kernel term) — α: engine IR → ansatz kernel IR (a CIC term)
     :lower    (fn [plan] → exec-form)         — γ: ansatz plan → engine physical executor call
     :estimate (fn [plan] → {pred→rate})    — optional: feeds optimize's :selectivity hook"
  (:require [ansatz.plan :as plan]
            [ansatz.optimize :as opt]))

(defonce ^:private engines (atom {}))

(defn register-engine!
  "Register an engine adapter under key `k` (e.g. :datahike). Idempotent (last wins)."
  [k adapter]
  (swap! engines assoc k adapter)
  k)

(defn engine [k] (get @engines k))
(defn registered-engines [] (set (keys @engines)))
(defn available-engines []
  (set (for [[k a] @engines :when (try ((:detect? a)) (catch Throwable _ false))] k)))

(def ^:private optional-adapter-nss
  "Adapter namespaces tried at load — each requires its engine, so it only loads if present."
  '[ansatz.bridge.datahike ansatz.bridge.stratum])

(defn load-optional-engines!
  "Try to load each optional engine adapter (ansatz.bridge.<engine>). An adapter ns requires its
   engine, so a missing engine just means its adapter doesn't load — Ansatz stays standalone.
   Returns the set of engines that loaded + registered."
  []
  (doseq [ns-sym optional-adapter-nss]
    (try (require ns-sym) (catch Throwable _ nil)))
  (registered-engines))

;; ── the certified optimize-across-the-bridge step ────────────────────────────
(defn optimize-plan
  "α-lift an engine IR via `lift`, optimize the resulting kernel term with the CERTIFIED cost search,
   and return {:plan optimized-plan, :verified?, :changed?}. The engine then γ-lowers `:plan`. The
   optimization is kernel-certified (verified-rewrite?), so: given the engine honors its API
   contract (its α-axioms), the optimized cross-engine plan ≡ the original."
  [env lift ir & {:keys [lctx selectivity sizes]}]
  (let [term (lift ir)                                              ; α: engine IR → kernel term
        res  (opt/optimize-cost env term :lctx lctx                 ; CERTIFIED cost-directed rewrite
                                :selectivity selectivity            ; (relational pushdown/semijoin/…)
                                :sizes sizes)]                      ; per-source cardinality (engine :estimate)
    {:plan      (plan/term->plan (:term res))                       ; the optimized plan, for γ
     :verified? (:verified? res)
     :rewrites  (:rewrites res)
     :changed?  (boolean (seq (:rewrites res)))}))

(defn lower
  "γ-lower an ansatz `plan` to engine `k`'s physical executor form."
  [k plan]
  ((:lower (engine k)) plan))
