;; A drop-in, verified transducer/reducer surface.
;;
;; Code reads like ordinary Clojure transducers — `(comp (map f) (filter p))`
;; threaded into a terminal — but the pipeline is captured as a SOAC plan
;; (`ansatz.reducers.plan`), rewritten with KERNEL-CHECKED fusion proofs, and run
;; on native Clojure. The kernel terms are only the reasoning shadow; nothing
;; executes on them.
;;
;; The transform functions must be captured (`certified-fn` / `a/defn`) so they
;; carry a kernel term — that is what makes them analyzable and the rewrites
;; provable. Opaque closures are fusion barriers: the pipeline still runs, it
;; just isn't optimized across them.
;;
;; Example:
;;   (require '[ansatz.verified :as v])
;;   (def succ (r/certified-fn {:name 'Nat.succ :kernel-term … :runtime inc}))
;;   (v/sum (v/comp (v/map succ) (v/map succ)) [1 2 3])   ;; ⇒ fused+verified
;;   (v/explain (v/comp (v/map succ) (v/map succ)))        ;; ⇒ the checked proofs

(ns ansatz.verified
  (:refer-clojure :exclude [map filter comp defn])
  (:require [ansatz.reducers :as r]
            [ansatz.reducers.plan :as pl]
            [ansatz.records :as rec]
            [ansatz.core :as ac]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Expr TypeChecker]))

;; ============================================================
;; Composable transform descriptors (data, not functions)
;; ============================================================

(clojure.core/defn map
  "A verified `map` step over a captured function `cfn`."
  [cfn]
  {:steps [(pl/map-step cfn)]})

(clojure.core/defn filter
  "A verified `filter` step over a captured predicate `cfn`."
  [cfn]
  {:steps [{:op :filter :fn cfn}]})

(clojure.core/defn comp
  "Compose verified steps left-to-right (like a composed transducer)."
  [& xforms]
  {:steps (vec (mapcat :steps xforms))})

;; ============================================================
;; Terminals — build the plan, fuse (verified), run natively
;; ============================================================

(defn- fn-term [cfn]
  (let [kt (:kernel-term (r/certification cfn))]
    (if (instance? Expr kt) kt (e/const' (name/from-string (str kt)) []))))

(defn- element-type [env cfn]
  (e/forall-type (.inferType (TypeChecker. env) (fn-term cfn))))

(def ^:private nat-add
  (delay (r/certified-fn {:name 'Nat.add
                          :kernel-term (e/const' (name/from-string "Nat.add") [])
                          :runtime +})))

(defn- ->plan
  "Build a SOAC plan for `xform` feeding a fold `consumer`, using the global
   Ansatz kernel env, then fuse it (verified)."
  [xform consumer]
  (let [env @ac/ansatz-env
        steps (:steps xform)
        elem (element-type env (:fn (first steps)))]
    ;; eliminate provably-constant filters (dependent-type), THEN fuse maps —
    ;; both kernel-checked.
    (pl/fuse env (pl/eliminate-filters env (pl/plan (pl/producer elem) steps consumer)))))

(clojure.core/defn sum
  "Sum a verified pipeline over `coll` — fused into the fold consumer with
   kernel-checked proofs, executed natively. The terminal monoid is `Nat.add`
   (associative with identity, kernel-checked elsewhere)."
  [xform coll]
  (pl/run (->plan xform (pl/fold-consumer @nat-add 0)) coll))

(clojure.core/defn explain
  "Return the kernel-checked rewrites that would be applied to a `sum` of
   `xform`: the fused transforms and each fusion proof."
  [xform]
  (pl/explain (->plan xform (pl/fold-consumer @nat-add 0))))

;; ============================================================
;; Verified record functions — idiomatic Clojure over typed records
;;
;; The other half of the surface: define schema-typed records and write
;; transforms in plain Clojure (`assoc`/`update`/`get-in`/`select-keys`/`->`),
;; compiled to verified kernel terms. A pipeline fuses (overwrite + dead-field
;; elimination) and `v/defn` additionally proves the fusion sound.
;;
;;   (v/def-record Row [:map [:a [:and :int [:>= 0]]] [:b [:and :int [:>= 0]]]])
;;   (v/defn bump [r :- Row] Row (-> r (assoc :a 1) (assoc :b 2) (assoc :a 9)))
;;   (v/fusion-proof 'bump)   ;; ⇒ the kernel-checked  naive = fused  theorem
;; ============================================================

(rec/install!)   ;; register the record-op elaborators on load

(defmacro def-record
  "Define a schema-typed record from a Malli `:map` (see ansatz.records/def-record)."
  [type-name malli-schema]
  `(rec/def-record ~type-name ~malli-schema))

(defmacro defn
  "Define a verified record function in idiomatic Clojure; for a single-record-param
   pipeline also proves `<name>.fusion_eq : naive = fused` (see ansatz.records/defn)."
  [fn-name params ret-type & body]
  `(rec/defn ~fn-name ~params ~ret-type ~@body))

(clojure.core/defn fusion-proof
  "The kernel-checked fusion-equivalence theorem (`naive = fused`) admitted for a
   record function defined with `v/defn`, as a string — or nil if none."
  [fn-name]
  (when-let [ci (kenv/lookup @ac/ansatz-env (name/from-string (str fn-name ".fusion_eq")))]
    (e/->string (.type ci))))

(clojure.core/defn validate
  "Does `data` satisfy record `rname`'s Malli schema (refinements included)? The
   contract boundary — see ansatz.records/validate."
  [rname data] (rec/validate rname data))

(clojure.core/defn conform
  "Contract cast at the boundary: `data` if it satisfies record `rname`'s schema,
   else throw. The trusted gradual-typing seam; downstream verified functions may
   then assume the refinement invariants."
  [rname data] (rec/conform rname data))
