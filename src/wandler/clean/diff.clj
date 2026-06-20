(ns wandler.clean.diff
  "THE differential harness — the gate every clean-tree (`wandler.clean.*`) phase reports to.

   The clean reimplementation is a STRANGLER: old wandler (green) stays the working reference/oracle
   while each module is rebuilt clean and proven equivalent before the old one is retired. For every
   ported subject we run it through BOTH sides and assert the three parities
   (docs/WANDLER_REIMPL_PLAN.md §0.2):

     (a) PLAN   — identical optimized plan (fused SOAC stages + the laws applied + kernel-certified)
     (b) RESULT — identical executed result on sample inputs
     (c) PROOF  — the clean module's theorem/certificate `check-constant`-verifies (authoritative)

   This namespace is a PURE library (no clojure.test dependency): each primitive returns a report map
   `{:ok? bool …}`; test namespaces assert on the reports. (c) is live from Phase 1 (the clean laws
   already exist); (a)/(b) take real old-vs-clean subjects as the runtime + optimizer modules land in
   Phases 2+. Until then they are exercised against old wandler itself (fused-vs-naive, compiled-vs-
   reference) — the same machinery, proven and ready.

   Old wandler API the harness rides: `wandler.core/explain` (the plan-report), the codegen'd var
   `((resolve fn-name) input)` (the executed result), and `wandler.core/*optimize*` (toggle fused/naive)."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [wandler.core :as w]
            [wandler.clean.optimize :as copt]
            [wandler.clean.optimize.cost :as ccost]))

;; ── (c) PROOF parity — active now ───────────────────────────────────────────────────────────
(defn verifies?
  "Authoritative kernel re-check: does the clean constant `name-str` `check-constant`-verify under
   `kenv`? Uses check-constant-replace (re-runs the Java kernel on type+value), NOT the lenient
   inferer. nil/absent → false."
  [kenv name-str]
  (let [ci (env/lookup kenv (nm/from-string name-str))]
    (boolean (and ci (try (env/check-constant-replace kenv ci) true (catch Throwable _ false))))))

(defn proof-gate
  "Verify every clean law/certificate in `names`. → {:ok? bool, :results {name bool}, :failed [names]}."
  [kenv names]
  (let [results (into {} (map (fn [n] [n (verifies? kenv n)])) names)
        failed  (vec (keep (fn [[n ok]] (when-not ok n)) results))]
    {:ok? (empty? failed) :results results :failed failed}))

;; ── (a) PLAN parity — for Phase 5 (exercised against old wandler today) ──────────────────────
(defn plan-of
  "The optimizer plan-report for a defined pipeline (`wandler.core/explain`)."
  [fn-name] (w/explain fn-name))

(defn clean-plan-report
  "A `w/explain`-shaped plan-report from the CLEAN optimizer (`optimize-cost`) over an elaborated body
   `term` — so a clean subject can be plan-compared the same way an old subject is. Keys mirror
   `wandler.core/explain`: `:verified?` (the composed proof check-constant-verifies), `:rewrites` (the
   laws the clean driver fired), `:stages-after` (SOAC pipeline of the optimized plan), `:passes-before`/
   `:passes-after` (SOAC stage counts). Pass the same `optimize-cost` opts (`:lctx`/`:sizes`/`:comm`/…)."
  [env term & opts]
  (let [r (apply copt/optimize-cost env term opts)
        before (ccost/soac-stages term)
        after  (ccost/soac-stages (:term r))]
    {:verified?     (boolean (:verified? r))
     :rewrites      (vec (:rewrites r))
     :stages-after  after
     :passes-before (count before)
     :passes-after  (count after)
     :term          (:term r)}))

(defn plan-parity
  "Two plan-reports (`wandler.core/explain` output) agree iff identical fused stages + applied
   rewrites (the laws that fired) + both kernel-certified. → {:ok? bool, :diff {:old … :new …} | nil}."
  [old new]
  (let [ks [:stages-after :rewrites :verified?]
        o (select-keys old ks) n (select-keys new ks)]
    {:ok? (= o n) :diff (when (not= o n) {:old o :new n})}))

;; ── (b) RESULT parity — for Phase 2+ (exercised against old wandler today) ───────────────────
(defn result-parity
  "Run `old-fn` and `new-fn` on each input; agree iff every output is `=` (seq-normalized for
   sequential outputs, so a vector and a list of the same elements match). → {:ok? bool,
   :mismatches [{:input :old :new}]}."
  [old-fn new-fn inputs]
  (let [norm (fn [v] (if (sequential? v) (seq v) v))
        ms (keep (fn [x]
                   (let [o (old-fn x) n (new-fn x)]
                     (when-not (= (norm o) (norm n)) {:input x :old o :new n})))
                 inputs)]
    {:ok? (empty? ms) :mismatches (vec ms)}))

;; ── the combined gate ───────────────────────────────────────────────────────────────────────
(defn differential
  "Run one subject through both sides and assert every applicable parity. Spec keys (all optional —
   only the parities whose inputs are present are checked):
     :label                 — subject name (for the report)
     :old-fn :new-fn :inputs — (b) RESULT parity
     :old-plan :new-plan     — (a) PLAN parity
     :kenv :laws             — (c) PROOF parity
   → {:label, :ok? bool, :result …, :plan …, :proof …}."
  [{:keys [label old-fn new-fn inputs old-plan new-plan kenv laws]}]
  (let [r  (when (and old-fn new-fn)     (result-parity old-fn new-fn inputs))
        p  (when (and old-plan new-plan) (plan-parity old-plan new-plan))
        pr (when (and kenv (seq laws))   (proof-gate kenv laws))]
    {:label label
     :ok? (and (or (nil? r) (:ok? r)) (or (nil? p) (:ok? p)) (or (nil? pr) (:ok? pr)))
     :result r :plan p :proof pr}))
