;; Wandler — the verified data-transformation runtime, built on the ansatz CIC kernel.
;;
;; You write ordinary Clojure pipelines in `a/defn`; wandler elaborates them to kernel
;; terms (lean4 elab_rules-shaped TERM elaborators through `ansatz.surface.api`),
;; OPTIMIZES them by certified rewriting (every adopted rewrite carries a kernel proof
;; `optimized ≡ original` — translation validation, checked by the same kernel that
;; admits Mathlib), and LOWERS them to fast Clojure through the codegen seam.
;;
;; Integration is three seams in ansatz, all additive (no carve, no fork):
;;   SEAM 1  term/macro elaborator registries  — the collection/relational surface
;;   SEAM 2  a/optimize-hook                   — the certified optimizer (this ns wires it)
;;   SEAM 3  a/codegen-registry                — the runtime lowering (ansatz.runtime)
(ns wandler.core
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.collections :as coll]
            [ansatz.runtime :as rt]
            [ansatz.optimize :as opt]))

(defonce ^{:doc "fn-name → the optimizer report for its last definition (the explain source)."}
  reports (atom {}))

(defn- optimize-hook
  "The SEAM 2 filler: cost-directed certified optimization of an a/defn body.
   Keeps the rewrite only if the kernel certified it; records the report for explain."
  [env fn-name term]
  (let [n (loop [t term, k 0] (if (e/lam? t) (recur (e/lam-body t) (inc k)) k))
        res (try (opt/optimize-body env term n)
                 (catch Throwable t
                   {:term term :verified? false :changed? false
                    :error (.getMessage t)}))]
    (swap! reports assoc fn-name res)
    (:term res)))

(defn explain
  "The optimizer report for a verified fn: was a rewrite adopted, which laws fired,
   and the pipeline shape before/after. `:verified?` means the kernel CERTIFIED the
   adopted term equal to the original definition."
  [fn-name]
  (when-let [r (get @reports (str fn-name))]
    {:verified? (:verified? r)
     :changed? (:changed? r)
     :rewrites (vec (:rewrites r))
     :stages-before (:stages-before r)
     :stages-after (:stages-after r)
     :passes-before (:passes-before r)
     :passes-after (:passes-after r)}))

(defn install!
  "Install the wandler runtime into ansatz's three seams (idempotent). Call after the
   kernel env is loaded — (a/init! \"init\") or richer — then define pipelines with a/defn."
  []
  (coll/install!)
  (rt/install!)
  (reset! a/optimize-hook optimize-hook)
  :installed)
