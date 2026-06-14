(ns wandler.jit.pgo
  "Verified plan cache / profile-guided optimization (PGO) -- the plan-once-then-run model.

   Decide the plan ONCE, outside any stateful execution flow: optimize a `term` against the OBSERVED
   workload (measured / declared cost params), certify the rewrite, compile it, and return a STORABLE,
   AUDITABLE artifact. Re-execution reuses the stored plan -- no warmup, no in-flight swap, no state
   migration (the plan is fixed before anything runs).

   Why this beats ordinary PGO: a normal profile-guided compiler stores an UNVERIFIED profile and HOPES
   the guided recompile is correct (with deopt guards to bail). Here the stored plan is a kernel-PROVEN
   `original = optimized` -- a proven-correct, auditable optimization artifact. `replay` can re-check the
   certificate before trusting it. The PGO win: the plan is tuned to the OBSERVED data (the params), not
   to defaults; the SOUNDNESS is independent of whether the observation was accurate."
  (:require [ansatz.core :as a]
            [wandler.optimize :as opt]
            [wandler.optimize.certify :as cert]
            [ansatz.kernel.expr :as e]))

(defn- compile-over
  "Compile a `term` over the source fvars in `lctx` to a CURRIED fn (outermost arg = lowest fvar id)."
  [env term lctx]
  (let [lam (reduce (fn [body id]
                      (e/lam (or (:name (lctx id)) (str "s" id)) (:type (lctx id)) (e/abstract1 body id) :default))
                    term (sort > (keys lctx)))]                 ; abstract highest id first → outermost = lowest
    (eval (a/ansatz->clj env lam []))))

(defn jit-compile
  "Compile a VERIFIED, workload-tuned plan for `term` over the sources in `lctx`. `:params` are the cost
   knobs {:sizes :selectivity :ndv} measured from the data (see wandler.jit.estimate/cost-params) or
   declared from refinements. optimize-cost is run against them and each adopted rewrite kernel-certified.
   Returns a storable artifact:
     {:original :optimized :lctx :params :certificate :verified? :rewrites :run}
   where :optimized is PROVEN = :original (the certificate), and :run is the compiled fn over the sources
   (curried, lowest fvar id first). The artifact is what you cache / ship / audit."
  [env term lctx & {:keys [params]}]
  (let [r (apply opt/optimize-cost env term :lctx lctx
                 (mapcat identity (select-keys (or params {}) [:sizes :selectivity :ndv])))
        plan (if (:verified? r) (:term r) term)]
    {:original term :optimized plan :lctx lctx :params params
     :certificate (:proof r) :verified? (boolean (:verified? r)) :rewrites (vec (:rewrites r))
     :run (compile-over env plan lctx)}))

(defn replay
  "Run a jit-compiled artifact over `sources` (in ascending fvar-id order). With `:reverify? true`,
   re-checks the stored certificate against the kernel FIRST (the artifact is auditable -- re-prove
   `original = optimized` before trusting a stored/shipped plan), throwing if it no longer certifies."
  [env artifact sources & {:keys [reverify?]}]
  (when (and reverify? (:certificate artifact))
    (when-not (cert/verified-rewrite? env (:original artifact)
                                      {:term (:optimized artifact) :proof (:certificate artifact)}
                                      :lctx (:lctx artifact))
      (throw (ex-info "stored plan failed re-verification" {:rewrites (:rewrites artifact)}))))
  (reduce (fn [f s] (f s)) (:run artifact) sources))
