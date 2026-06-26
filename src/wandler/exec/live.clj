(ns wandler.exec.live
  "The LIVE async executor — drive a certified incremental view from a reactive source, and wire several
   into a DATAFLOW GRAPH. Each node maintains a Z-set view across PUSHED deltas (the proven DBSP
   differential per push), holds its current view in a watchable `:out` atom, and emits its OUTPUT DELTA
   to subscribers — so nodes compose into a DAG where every edge carries the certified incremental change.

   This is the push/reactive counterpart to wandler.exec.zset's pull/lazy `query`: same certified operators
   (`Zproduct_product_rule` for the join, `Mode.diff_async_dist` for the linear stages), driven by events
   instead of a seq. The source can be a Clojure atom (`drive!`), or — over the wandler.exec.fork substrate —
   a live spindel FRP node (`drive-source!` with spindel's subscription). Ansatz has NO hard dependency
   on spindel: the atom path makes the whole graph testable standalone. See docs/STREAMING.md."
  (:require [wandler.exec.zset :as zs]
            [clojure.string]))

(defn- apply-ops
  "Run the linear post-ops of a stage chain over a Z-set `v` (filter/map keep it a Z-set; sum folds to a
   number). On a DELTA this yields the output delta, by linearity (DBSP Thm 5.4 / Mode.diff_async_dist)."
  [v ops]
  (reduce (fn [v [op a]]
            (case op :filter (zs/z-filter a v) :map (zs/z-map a v) :sum (zs/z-sum a v)))
          v ops))

(defn join-node
  "A live JOIN node. Maintains `[L R V]` across pushed `[δL δR]` batches via the certified bilinear
   differential (`zs/join-step`). Returns {:push! :out :subscribe}:
     :push!     (fn [[δL δR]]) — apply the differential step, update :out, emit the view DELTA, return V
     :out       an atom holding the current join view (watchable — a graph node output)
     :subscribe (fn [g]) — register `g` to receive each output Z-set delta (a graph edge)."
  [kf lf]
  (let [state (atom [{} {} {}]) out (atom {}) subs (atom [])]
    {:push! (fn [delta]
              (let [[_ _ V] (swap! state #(zs/join-step kf lf % delta))
                    dv (zs/z-add V (zs/z-negate @out))]   ; V − V_prev = the output change
                (reset! out V)
                (doseq [g @subs] (g dv))
                V))
     :out out
     :subscribe (fn [g] (swap! subs conj g))}))

(defn linear-node
  "A live LINEAR node — a filter/map/sum chain (`ops`, e.g. `[[:filter p] [:sum f]]`). Its input is a
   Z-set DELTA; by linearity its output delta is just `ops(δ)`, so it composes downstream of any node.
   `:out` accumulates the running result (a Z-set, or a number for a `:sum` chain). Same shape as
   `join-node` (:push! :out :subscribe)."
  [ops]
  (let [sum? (some #(= :sum (first %)) ops)
        out (atom (if sum? 0 {})) subs (atom [])]
    {:push! (fn [d]
              (let [od (apply-ops d ops)
                    nv (if (number? od) (+ @out od) (zs/z-add @out od))]
                (reset! out nv)
                (doseq [g @subs] (g od))
                od))
     :out out
     :subscribe (fn [g] (swap! subs conj g))}))

(defn connect!
  "Wire a graph EDGE: subscribe `down` to `up`'s output deltas. For a `down` JOIN node the upstream delta
   feeds one side (`:left` ⇒ `[δ {}]`, `:right` ⇒ `[{} δ]`); for a `down` LINEAR node it feeds directly."
  [up down & {:keys [side join?] :or {side :left join? false}}]
  ((:subscribe up) (fn [d] ((:push! down) (if join? (if (= side :left) [d {}] [{} d]) d)))))

(defn drive!
  "Drive a node from a reactive INPUT atom of deltas: watch it, push each new value into `node`. Returns
   an unsubscribe fn. (A `core.async` tap or a spindel node subscription fit `drive-source!` below.)"
  [in-atom node]
  (let [k (gensym "ansatz-live")]
    (add-watch in-atom k (fn [_ _ _ d] (when (some? d) ((:push! node) d))))
    (fn [] (remove-watch in-atom k))))

(defn drive-source!
  "Drive a node from an ARBITRARY reactive source. `subscribe` takes a callback and returns an
   unsubscribe fn — an atom-watch, a core.async tap, or a live spindel node subscription all fit (the
   spindel integration point: pass spindel's node-subscription as `subscribe`, no hard dependency)."
  [subscribe node]
  (subscribe (fn [d] (when (some? d) ((:push! node) d)))))

;; ── the SURFACE bridge: a clojure.core pipeline → a certified live graph ──────────────────────────
;; ONE vocabulary. The recognized OPERATORS (join/filter/remove/map/reduce) become certified incremental
;; nodes — their ∂ is a proven law, INDEPENDENT of the payload. The element FUNCTIONS are ordinary
;; Clojure: an `a/defn` fn is white-box (:verified, carries an ::kernel-name); anything else — your code,
;; a third-party lib, a closure — is a BLACK BOX, run as-is and reported as `:trusted` (sound when pure;
;; incremental retraction undoes an insertion exactly iff the fn is pure). This is the gradual on-ramp:
;; copy-paste clojure.core, opt into verification by making leaves `a/defn`. The `:report` is the coach.
(defn- white-box? [f] (boolean (:ansatz.core/kernel-name (meta f))))
(defn- trust [f] (if (white-box? f) :verified :trusted))

(defn build-flow
  "Runtime builder for `flow`: join key fns + a recognized linear-op vector `[[:filter f] [:map f]
   [:sum f]]` (element fns are ordinary Clojure). Builds the wired live graph and a gradual REPORT
   classifying each stage's operator certificate and its payload trust. Returns {:push! :out :nodes :report}."
  [kf lf ops]
  (let [jn (join-node kf lf) ln (linear-node ops) _ (connect! jn ln)]
    {:push! (:push! jn) :out (:out ln) :nodes [jn ln]
     :report (into [{:op :join :class :bilinear :certificate "Zproduct_product_rule"
                     :payload (if (and (white-box? kf) (white-box? lf)) :verified :trusted)}]
                   (map (fn [[op f]]
                          {:op op :payload (trust f)
                           :class       (if (= op :sum) :homomorphism :linear)
                           :certificate (if (= op :sum) "Mode.diff_async_dist (homomorphism)"
                                                        "Mode.diff_async_dist (linear)")}))
                   ops)}))

(defn from-stages
  "Build a live graph from mode/∂ STAGES + parallel runtime IMPLS (the codegen'd leaf fns: `[kf lf]` for
   the join stage, one fn per linear stage) and a precomputed `report`. The kernel-grounded counterpart
   of `mode/to-zset-query` — same certified operators, but PUSH-driven. Assumes the first stage is the
   join. Returns the flow handle {:push! :out :nodes :report}."
  [stages impls report]
  (let [[kf lf] (first impls)
        ops (mapv (fn [{:keys [stage]} impl] [stage impl]) (rest stages) (rest impls))
        jn (join-node kf lf) ln (linear-node ops)]
    (connect! jn ln)
    {:push! (:push! jn) :out (:out ln) :nodes [jn ln] :report report}))

(defn report-str
  "Pretty-print a flow's gradual report: per stage the ∂ certificate (★) and whether the payload fn is
   kernel-verified or a trusted black box. Black-box payloads are sound for incremental iff pure."
  [{:keys [report]}]
  (clojure.string/join "\n"
    (for [{:keys [op class certificate payload]} report]
      (format "  %-7s ★ %-34s payload: %s" (name op) certificate
              (case payload :verified "verified (a/defn)" "trusted (black box — assumed pure)")))))

(defmacro flow
  "Build a live incremental dataflow GRAPH from a clojure.core pipeline — the SAME vocabulary as batch:

     (flow (join :cid :id)                       ; first stage: the join key fns
           (filter (fn [[o c]] (premium? c)))    ; ordinary clojure.core operators…
           (map    customer-summary)             ; …parameterised by your (possibly black-box) fns
           (reduce + 0))                         ; a group reduce → incremental sum

   Recognized operators (join/filter/remove/map/reduce-with-+) become certified incremental nodes; the
   element functions run as-is (black box ⇒ trusted, a/defn ⇒ verified — see `:report`). An unrecognized
   operator or a non-group reduce throws a coach-style error (it can't be incrementalized — it's a batch
   barrier). Returns a handle {:push! [δL δR], :out (current view), :report, :nodes}; drive it with `drive!`."
  [join-stage & linear-stages]
  (let [[jhead kf lf] join-stage]
    (when-not (= jhead 'join)
      (throw (ex-info "flow must start with (join kf lf) — the relational base of the graph" {:got jhead})))
    (let [ops (mapv (fn [stage]
                      (let [[h a] stage]
                        (case h
                          filter `[:filter ~a]
                          remove `[:filter (complement ~a)]
                          map    `[:map ~a]
                          reduce (if (= a '+) `[:sum identity]
                                   (throw (ex-info (str "(reduce " a " …) isn't a group — can't incrementalize "
                                                        "(only + / count). It falls back to BATCH; rewrite or annotate a monoid.")
                                                   {:combiner a})))
                          (throw (ex-info (str "unrecognized operator `" h "` — not in the differentiable vocabulary "
                                               "(join/filter/remove/map/reduce). It's an incremental BARRIER (runs as batch).")
                                          {:op h})))))
                    linear-stages)]
      `(build-flow ~kf ~lf [~@ops]))))
