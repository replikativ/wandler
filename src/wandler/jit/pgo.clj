(ns wandler.jit.pgo
  "Profile-guided expression optimization with an in-process executable cache.

   Certificates establish equality of kernel expressions. Generated Clojure execution additionally
   trusts the code generator. Artifacts containing `:run` are in-process values, not a serialization
   format. Strict replay checks the expressions and compiles the checked plan locally, ignoring any
   supplied executable closure."
  (:require [ansatz.core :as a]
            [wandler.optimize :as opt]
            [wandler.optimize.certify :as cert]
            [ansatz.kernel.expr :as e])
  (:import [ansatz.kernel TypeChecker]))

(defn- close-over
  "Close source fvars with lambda binders, lowest fvar id outermost."
  [term lctx]
  (reduce (fn [body id]
            (e/lam (or (:name (lctx id)) (str "s" id)) (:type (lctx id))
                   (e/abstract1 body id) :default))
          term (sort > (keys lctx))))

(defn- compile-over
  "Compile a `term` over source fvars in `lctx` to a curried fn, lowest fvar id outermost."
  [env term lctx]
  (eval (a/ansatz->clj env (close-over term lctx) [])))

(defn- check-expressions!
  "Strictly check both closed expressions, including application arguments and binder types."
  [env {:keys [original optimized lctx rewrites]}]
  (try
    (let [checker (doto (TypeChecker. env) (.setFuel 50000000))]
      (.check checker (close-over original lctx))
      (.check checker (close-over optimized lctx)))
    (catch Exception cause
      (throw (ex-info "stored plan failed expression typechecking"
                      {:rewrites rewrites} cause)))))

(defn jit-compile
  "Compile a VERIFIED, workload-tuned plan for `term` over the sources in `lctx`. `:params` are the cost
   knobs {:sizes :selectivity :ndv} measured from the data (see wandler.jit.estimate/cost-params) or
   declared from refinements. optimize-cost is run against them and each adopted rewrite kernel-certified.
   Returns an in-process artifact:
     {:original :optimized :lctx :params :certificate :verified? :rewrites :run}
   where :optimized is PROVEN = :original (the certificate), and :run is the compiled fn over the sources
   (curried, lowest fvar id first). Cache this artifact in-process; audit its expression and proof fields."
  [env term lctx & {:keys [params]}]
  (let [r (apply opt/optimize-cost env term :lctx lctx
                 (mapcat identity (select-keys (or params {}) [:sizes :selectivity :ndv])))
        plan (if (:verified? r) (:term r) term)]
    {:original term :optimized plan :lctx lctx :params params
     :certificate (:proof r) :verified? (boolean (:verified? r)) :rewrites (vec (:rewrites r))
     :run (compile-over env plan lctx)}))

(defn replay
  "Run an in-process artifact over `sources` in ascending fvar-id order. With `:reverify? true`,
   strictly typecheck both expressions and check `original = optimized`, then compile locally instead of
   trusting `:run`. An identity plan can omit a proof; a changed plan cannot. Codegen remains trusted.
   Callers must establish that runtime sources satisfy `:lctx`, including any refinement hypotheses."
  [env artifact sources & {:keys [reverify?]}]
  (let [run (if reverify?
              (do
                (check-expressions! env artifact)
                (when-not (cert/verified-rewrite? env (:original artifact)
                                                  {:term (:optimized artifact) :proof (:certificate artifact)}
                                                  :lctx (:lctx artifact))
                  (throw (ex-info "stored plan failed re-verification" {:rewrites (:rewrites artifact)})))
                (compile-over env (:optimized artifact) (:lctx artifact)))
              (:run artifact))]
    (reduce (fn [f s] (f s)) run sources)))
