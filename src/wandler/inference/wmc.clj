(ns wandler.inference.wmc
  "The pluggable WMC (Weighted Model Counting) SEAM — the trusted-oracle boundary that turns a provenance
   formula (an L0-proven DNF over independent fact-ids, from wandler.inference.semiring) into a probability. Backends
   register here; the rest of the stack never knows which counter ran.

     :enumeration — exact, 2^n, ALWAYS present. The reference oracle (delegates to wandler.inference.semiring/wmc).
     :logicng     — pure-JVM knowledge compilation (BDD weighted DP), via wandler.inference.wmc.logicng (opt-in, :logicng alias).
     (:ganak/:d4  — native SOTA counters via a subprocess over `dnf->weighted-cnf`, a later step.)

   TRUST MODEL: the formula is L0 (proven provenance); the count is L2 (trusted). But a compiled backend is
   DIFFERENTIALLY cross-checked against the exact :enumeration reference on small formulas (≤ 18 facts) — so a
   wiring bug surfaces immediately. Same discipline as the malli bridge. See finset-findist-monad,
   correlated_query_test (why WMC is necessary), and the engine-bridge pattern in ansatz.bridge."
  (:require [wandler.inference.semiring :as sr]
            [clojure.string :as str]))

(defonce ^:private backends (atom {}))
(defn register-backend! "Register a WMC backend `{:detect? :wmc}` under key `k` (idempotent, last wins)." [k m] (swap! backends assoc k m) k)
(defn registered [] (set (keys @backends)))
(defn available  [] (set (for [[k m] @backends :when (try ((:detect? m)) (catch Throwable _ false))] k)))

(defn facts "the distinct fact-ids in a provenance DNF (a set of sets), in a stable order." [dnf]
  (vec (sort-by str (distinct (mapcat seq dnf)))))

;; ── :enumeration backend — the exact reference (always present) ───────────────────────────────────
(defn wmc-enumerate "Exact WMC by model enumeration (2^n) — the reference oracle." [probs dnf] (sr/wmc probs dnf))
(register-backend! :enumeration {:detect? (constantly true) :wmc wmc-enumerate})

;; ── serializer for NATIVE counters (Ganak/d4) — the MCC weighted-CNF format ───────────────────────
(defn dnf->weighted-cnf
  "Serialize WMC(DNF) for a native weighted model counter in the MCC weighted-CNF (DIMACS) format. Uses the
   COMPLEMENT, since a positive DNF is not CNF but its negation is: ¬(⋁ⱼ conjⱼ) = ⋀ⱼ (⋁ ¬lit) is directly
   CNF, and with normalized per-fact weights `WMC(DNF) = 1 − WMC(¬DNF)`. Returns
   {:dimacs <str>, :vars <fact→var-idx>, :complement? true} — the counter's result R gives WMC = 1 − R."
  [probs dnf]
  (let [fs (facts dnf) idx (zipmap fs (map inc (range)))
        wlines (mapcat (fn [fc] (let [v (idx fc) p (double (probs fc))]
                                  [(str "c p weight " v " " p " 0") (str "c p weight -" v " " (- 1.0 p) " 0")])) fs)
        clauses (for [conj dnf] (str (str/join " " (map #(str "-" (idx %)) conj)) " 0"))]
    {:dimacs (str/join "\n" (concat ["c t wmc"                ; MCC-2024 tracking-type line (Ganak/SharpSAT-TD/d4v2)
                                     (str "p cnf " (count fs) " " (count dnf))] wlines clauses))
     :vars idx :complement? true}))

;; ── load optional backends (each requires its engine; absent ⇒ just skipped) ──────────────────────
(defn load-backends! []
  (doseq [ns '[wandler.inference.wmc.logicng]] (try (require ns) (catch Throwable _ nil)))
  (registered))

(defn wmc
  "WMC of a provenance `dnf` under independent fact probabilities `probs`. Picks the best available backend
   (prefers a compiled one over :enumeration) unless `:backend` is given. With `:check?` (default true) a
   compiled backend is cross-checked against the exact :enumeration reference on small formulas (≤ 18 facts)."
  [probs dnf & {:keys [backend check?] :or {check? true}}]
  (load-backends!)
  (let [avail (available)
        b (or backend (first (sort (disj avail :enumeration))) :enumeration)
        r (double ((:wmc (@backends b)) probs dnf))]
    (when (and check? (not= b :enumeration) (<= (count (facts dnf)) 18))
      (let [ref (double (wmc-enumerate probs dnf))]
        (when (> (Math/abs (- ref r)) 1e-6)
          (throw (ex-info "WMC backend disagrees with exact enumeration"
                          {:backend b :backend-result r :exact ref :dnf dnf})))))
    r))
