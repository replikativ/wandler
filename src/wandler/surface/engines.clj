(ns wandler.surface.engines
  "SURFACE PATH for external-engine sources: write a real engine query — `datahike.api/q` or
   `stratum.query/q` — INSIDE an `a/defn` combinator pipeline, and it elaborates to a typed kernel
   RELATION-SOURCE leaf. The certified optimizer then plans END-TO-END across the boundary — fuse the
   combinators, factor an aggregation through a join whose side is an engine scan — and codegen lowers
   the leaf back to the REAL engine call, coercing the engine's tuples to the kernel's positional
   record rep.

   The mechanism: the surface dispatch keys term elaborators on the list head (`ansatz.surface.elaborate`),
   so a `(datahike.api/q …)` / `(stratum.query/q …)` head dispatches to the elaborator registered here
   (an alias like `(d/q …)` dispatches too — ansatz resolves the head's canonical name). The engine
   source is an OPAQUE TRUSTED leaf: the optimizer treats any unknown head as a `:source`
   (`wandler.optimize.plan`), so the structure AROUND it stays kernel-certified while the scan's
   contents are the engine's contract. The query + args ride a per-call registry keyed by a small
   integer id baked into the leaf, read back by the lowering.

   Each engine is one ENGINE SPEC (`:head` to intercept, `:arity` of a captured call, `:lower` to a
   runtime form). Adding an engine is adding a spec — the leaf type, the registry, and the dispatch are
   shared. Scope: long-typed result columns → `List (Prod Nat … Nat)` rows (right-nested Prod, the
   record rep). The `:where`-pushdown (run a filter inside the engine's index) is a separate, trusted
   step."
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.level :as lvl]
            [wandler.runtime :as rt]))

(def ^:private z lvl/zero)
(defn- natT [] (e/const' (nm/from-string "Nat") []))
(defn- prod [a b] (e/app* (e/const' (nm/from-string "Prod") [z z]) a b))
(defn- listOf [t] (e/app (e/const' (nm/from-string "List") [z]) t))

(defn- row-type
  "The kernel row type for an N-column long-typed engine result: N=1 → Nat, else a RIGHT-NESTED Prod of
   N Nats (`Prod Nat (Prod Nat …)`), matching the kernel's nested-pair record rep."
  [n]
  (if (<= n 1) (natT) (prod (natT) (row-type (dec n)))))

(def ^:private MAX-ARITY 6)

;; ── the per-call registry: a small id (baked into the leaf) → its engine call ────────────────────────
(defonce ^:private registry (atom {}))   ; id → {:engine :args :n}
(defonce ^:private counter  (atom 0))

(defn- source-const [n] (str "EngineSource.q" n))

;; ── runtime coercion: an engine's FLAT tuple → the kernel's right-nested Prod record rep ──────────────
(defn nest-tuple
  "Right-nest a flat result tuple into the kernel pair rep: [a] → a, [a b] → [a b], [a b c] → [a [b c]], …"
  [t]
  (let [v (vec t)]
    (cond (= 1 (count v)) (first v)
          (= 2 (count v)) v
          :else           [(first v) (nest-tuple (subvec v 1))])))

(defn- unwrap-quote [form]
  (if (and (seq? form) (= 'quote (first form))) (second form) form))

(defn- find-arity
  "Count the find-vars in a datalog `:find` clause (the leading `?vars` before :where/:keys/:in)."
  [q]
  (->> (rest (drop-while #(not= :find %) q))
       (take-while #(not (#{:where :keys :in :with} %)))
       (filter #(and (symbol? %) (.startsWith (name %) "?")))
       count))

(defn- select-keys-order
  "The RESULT-MAP keys, in order, of a stratum `:select` vector: a bare keyword `:c` keys `:c`; an
   `[:as expr :alias]` keys `:alias`. (v1: those two forms.)"
  [qmap]
  (for [s (:select qmap)]
    (cond (keyword? s) s
          (and (vector? s) (= :as (first s))) (last s)
          :else (throw (ex-info "stratum surface source: unsupported :select element (need a keyword or [:as expr :alias])"
                                {:select s})))))

;; ── ENGINE SPECS ────────────────────────────────────────────────────────────────────────────────────
;; Each: :head = the fully-qualified surface symbol to intercept; :arity = (raw-arg-forms → N columns);
;; :lower = (raw-arg-forms → a Clojure form yielding `List (row-type N)` at runtime, rows already nested).
(def ^:private engines
  {:datahike
   {:head  'datahike.api/q
    :arity (fn [[query-form _db]] (find-arity (unwrap-quote query-form)))
    ;; (vec (map nest-tuple (datahike.api/q 'query db)))  — datahike rows are positional vectors
    :lower (fn [[query-form db-form]]
             (list 'clojure.core/vec
                   (list 'clojure.core/map 'wandler.surface.engines/nest-tuple
                         (list 'datahike.api/q (list 'quote (unwrap-quote query-form)) db-form))))}

   :stratum
   {:head  'stratum.query/q
    :arity (fn [[query-map]] (count (select-keys-order (unwrap-quote query-map))))
    ;; (mapv (fn [r] (nest-tuple [(get r :k) (get r :v) …])) (stratum.query/q {…}))  — stratum rows are maps
    :lower (fn [[query-map]]
             (let [cols (vec (select-keys-order (unwrap-quote query-map)))]
               (list 'clojure.core/mapv
                     (list 'fn ['r] (list 'wandler.surface.engines/nest-tuple
                                          (apply list 'clojure.core/vector
                                                 (for [c cols] (list 'clojure.core/get 'r c)))))
                     (list 'stratum.query/q query-map))))}})

(defn- make-elaborator
  "An elaborator for an engine `:head`: capture the raw call args + the column arity under a fresh id,
   and return the typed `EngineSource.qN id` leaf."
  [engine-key {:keys [arity]}]
  (fn [_est args]
    (let [n  (max 1 (arity args))
          _  (when (> n MAX-ARITY)
               (throw (ex-info (str "engine surface source: arity " n " exceeds MAX-ARITY " MAX-ARITY)
                               {:engine engine-key :args args})))
          id (swap! counter inc)]
      (swap! registry assoc id {:engine engine-key :args (vec args) :n n})
      (e/app (e/const' (nm/from-string (source-const n)) []) (e/lit-nat id)))))

(defn- lowering
  "The shared runtime lowering for an `EngineSource.qN` leaf: read its registry entry and dispatch to
   the originating engine's `:lower` (the id rides as the leaf's single compiled arg)."
  [_n]
  (fn [_env ca _args _names]
    (let [{:keys [engine args]} (get @registry (long (first ca)))]
      ((:lower (get engines engine)) args))))

(defn install!
  "Pre-declare the `EngineSource.qN : Nat → List (row-type N)` source axioms (N=1..MAX-ARITY), register
   their shared runtime lowerings, and intercept each engine's query head in the surface. Idempotent.
   Call after the kernel env is loaded + `w/install!`. Additive; no native engine dep is required to
   install (a dep is only needed to actually RUN a query of that engine)."
  []
  (doseq [n (range 1 (inc MAX-ARITY))]
    (let [cn (source-const n) o (nm/from-string cn)]
      (when-not (kenv/lookup (a/env) o)
        (swap! a/ansatz-env kenv/check-constant
               (kenv/mk-axiom o [] (e/forall' "id" (natT) (listOf (row-type n)) :default))))
      (rt/register-lowering! cn (lowering n))))
  (doseq [[engine-key spec] engines]
    (a/register-term-elaborator! (:head spec) (make-elaborator engine-key spec)))
  :installed)
