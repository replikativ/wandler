(ns wandler.surface.common
  "Shared helpers for the surface elaborators (cohesion: these were redefined across
   ~7 surface namespaces). One home for name/type/level plumbing every elaborator needs."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl])
  (:import [ansatz.kernel TypeChecker]))

(defn nm
  "Kernel name from a string."
  [s] (name/from-string s))

(defn c0
  "A 0-level kernel constant by name (`(e/const' (nm s) [])`)."
  [s] (e/const' (name/from-string s) []))

(defn head-name
  "Head constant name of a kernel type/term expr (e.g. \"Int\" for `Int`, \"List\" for
   `(List Nat)`), or nil if the head isn't a constant."
  [t]
  (let [[h _] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h)) (name/->string (e/const-name h)))))

(defn univ
  "The universe level `u` of a type `t : Sort(u+1)` (e.g. 0 for `Nat`) in `env`."
  [env t]
  (lvl/succ-pred (e/sort-level (.inferType (TypeChecker. env) t))))
