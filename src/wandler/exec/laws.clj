(ns wandler.exec.laws
  "Shared idempotent law-installer for the exec/streaming layers (cohesion #4). The
   sentinel + cache + replay skeleton was copied across zset/dbsp/dbsp_recursion/dbsp_stream:
   prove a batch of kernel laws the first time, memoize the resulting ConstantInfos, and on a
   later call (after an env reset) replay them instead of re-proving."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]))

(defn cached-install!
  "Idempotent law install keyed on `sentinel` (a const-name string):
     - if `sentinel` is already in the env, no-op;
     - else if `cache` (an atom) holds the previously-built CIs, REPLAY them into the current env
       (admit each — this is the cheap path after an env reset, no re-proving);
     - else call `build` — a thunk that admits its consts into the env AND returns the vector of
       CIs — and memoize them in `cache`.
   Returns (a/env)."
  [cache sentinel build]
  (when-not (kenv/lookup (a/env) (name/from-string sentinel))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (reset! cache (vec (build)))))
  (a/env))
