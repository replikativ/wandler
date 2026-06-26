(ns wandler.backend.stratum
  "OPTIONAL stratum execution backend (#76, Integration 2 — transparent reducer offload). Routes a
   wandler group-by/aggregate (and equi-join+aggregate) REDUCER — code NOT written as a query — to
   stratum's in-memory SIMD columnar engine when the cost model says it pays. Loads ONLY under the
   :stratum alias.

   Heavy deps stay out: we require stratum.query (NOT stratum.api), whose load graph is parquet/hadoop-
   free; `(q/q {:from {col->array} ...})` runs purely from JVM arrays, no files.

   COVERAGE (the closed sub-algebra stratum exposes via its public DSL — its agg dispatch is a closed
   `case`, so we map to exactly its built-in ops):
     - aggregates: sum (nat/int/float add), min, max  →  stratum :sum/:min/:max kernels.
     - group-by over ANY key (dict-encoded by value equality; numeric keys skip the dict).
     - equi-join + group + agg (`offload-join-group-sum`) — stratum builds the in-memory hash/bitmap
       join index internally (the transparent ad-hoc index).
   Open/custom monoids are NOT reachable here (would need a stratum-internals accumulator seam).

   COST-GATE: an offload only fires when it should win — high cardinality over enough rows (else the
   columnarization boundary dominates and eager is as good or better). `:ndv` in opts is the cardinality
   estimate (the #69 datahike :estimate handshake hook); absent, we sample. Below threshold → nil → the
   eager reducer runs (result-equal). The verified monoid spec is the equivalence certificate."
  (:require [stratum.query :as sq]
            [wandler.reducers :as r])
  (:import [wandler.reducers Pipeline]
           [java.util HashMap ArrayList]))

;; ── aggregate recognition (closed: maps wandler monoids to stratum's built-in agg ops) ───────────────
(def ^:private agg-table
  {:nat/add :sum :int/add :sum :float/add :sum
   :nat/max :max :int/max :max :float/max :max
   :nat/min :min :int/min :min :float/min :min})

(defn- agg-of
  "stratum agg op for `value-spec` (:sum/:max/:min), or nil to decline. Sources, in order: an explicit
   `:offload/agg` override in opts, a `:stratum/agg` hint in the spec metadata, then the name table."
  [value-spec opts]
  (or (:offload/agg opts)
      (get-in value-spec [:metadata :stratum/agg])
      (get agg-table (:name value-spec))))

;; ── cost-gate ────────────────────────────────────────────────────────────────────────────────────
(def ^:dynamic *policy*
  "Offload only when (rows >= :min-rows) and (estimated distinct keys >= :min-ndv). Below that, the
   columnarization boundary isn't amortized by the SIMD grouping. :sample caps the ndv-estimate scan."
  {:min-rows 100000 :min-ndv 1000 :sample 10000})

(defn- estimate-ndv [coll key-f sample-n]
  (count (into #{} (comp (take sample-n) (map key-f)) coll)))

(defn- should-offload?
  "True when this group-by is worth offloading. `:offload/force?` bypasses (for differential tests);
   `:ndv` supplies the cardinality estimate (#69 handshake), else we sample. Non-counted colls decline
   (can't size / safely re-iterate)."
  [coll key-f opts]
  (or (boolean (:offload/force? opts))
      (let [pol *policy*
            n   (when (counted? coll) (count coll))
            ndv (or (:ndv opts) (estimate-ndv coll key-f (:sample pol)))]
        (boolean (and n (>= n (long (:min-rows pol))) (>= ndv (long (:min-ndv pol))))))))

(defn- empty-pipeline?
  "Offload v1 handles a bare group-by (no transform prefix); a non-trivial pipeline declines → eager.
   (Pushing structured filter/map into stratum's :where is the Integration-1 generalization.)"
  [p]
  (or (nil? p)
      (and (sequential? p) (empty? p))
      (and (instance? Pipeline p) (empty? (:steps p)))))

;; ── helpers: build primitive columns from a collection ───────────────────────────────────────────
(defn- numeric-all? [^ArrayList xs]
  (loop [i 0] (cond (= i (.size xs)) true (integer? (.get xs i)) (recur (inc i)) :else false)))

(defn- value-column
  "long[] if every value is integral, else double[]."
  [^ArrayList vs]
  (let [n (.size vs)]
    (if (numeric-all? vs)
      (let [a (long-array n)]   (dotimes [i n] (aset a i (long   (.get vs i)))) [a true])
      (let [a (double-array n)] (dotimes [i n] (aset a i (double (.get vs i)))) [a false]))))

(defn- key-codec
  "Encode keys (from an ArrayList) into a long[] code column + a decoder. Numeric keys are used
   directly (decoder = identity); otherwise dictionary-encode by value equality in first-seen order."
  [^ArrayList ks]
  (let [n (.size ks)
        arr (long-array n)]
    (if (numeric-all? ks)
      (do (dotimes [i n] (aset arr i (long (.get ks i)))) [arr identity])
      (let [code (HashMap.) decode (ArrayList.)]
        (dotimes [i n]
          (let [k (.get ks i)]
            (aset arr i (long (or (.get code k)
                                  (let [c (.size decode)] (.put code k c) (.add decode k) c))))))
        [arr (fn [c] (.get decode (int c)))]))))

;; ── open-monoid path: ANY lawful monoid via stratum's grouped-fold (tier 3) ──────────────────────
(def ^:private default-threads (max 1 (.. Runtime getRuntime availableProcessors)))

(defn- lawful-monoid? [spec]
  (and (:combine spec) (:unit-fn spec)
       (every? #(contains? (:laws spec) %) [:assoc :left-identity :right-identity])))

(defn- prim-combine
  "A boxing-free `LongBinaryOperator` for the monoid's combine, when the spec metadata names a primitive
   op symbol under `:stratum/prim-op` (e.g. 'clojure.core/bit-or). With both args primitive long, Clojure
   inlines the op (LOR/LADD/…) — no boxing — so stratum's primitive grouped-fold can scatter at near-
   built-in speed. nil → the general Object path. Built once per spec."
  [value-spec]
  (when-let [op (get-in value-spec [:metadata :stratum/prim-op])]
    (eval `(reify java.util.function.LongBinaryOperator
             (applyAsLong [_# a# b#] (~op a# b#))))))

(defn offload-custom-group
  "Offload a group-by with an ARBITRARY (open) lawful monoid to stratum's `grouped-fold` primitive — for
   aggregates OUTSIDE stratum's closed built-in set. Any associative `combine` rides stratum's dense-code
   grouping + parallel partition/merge; the monoid's ASSOCIATIVITY is the parallel-merge certificate.
   Returns `{key -> merged-acc}` (== the eager reducer; the left-identity law makes the unit-start fold
   agree with eager's first-value-seed). Threads default to the core count; the win is at high cardinality
   where eager's persistent-map grouping is slow + single-threaded."
  [value-spec key-f value-f coll & [{:keys [threads] :or {threads default-threads}}]]
  (let [keys (ArrayList.) vals (ArrayList.)]
    (doseq [x coll] (.add keys (key-f x)) (.add vals (value-f x)))
    (let [n     (.size keys)
          codes (long-array n)
          code  (HashMap.) decode (ArrayList.)]
      (dotimes [i n]
        (let [k (.get keys i)]
          (aset codes i (long (or (.get code k)
                                  (let [c (.size decode)] (.put code k c) (.add decode k) c))))))
      (let [g   (.size decode)
            lbo (prim-combine value-spec)
            long-vals? (and lbo (loop [i 0] (cond (= i n) true
                                                  (instance? Long (.get vals i)) (recur (inc i))
                                                  :else false)))
            decode! (fn [^objects res]
                      (persistent! (reduce (fn [m c] (assoc! m (.get decode (int c)) (aget res (int c))))
                                           (transient {}) (range g))))]
        (if long-vals?
          ;; Layer A — primitive boxing-free path (LongBinaryOperator over long[] accumulators)
          (let [varr (long-array n)
                _    (dotimes [i n] (aset varr i (long (.get vals i))))
                gfp  (requiring-resolve 'stratum.query.custom-agg/grouped-fold-prim-long)
                ^longs res (gfp codes varr g (long ((:unit-fn value-spec))) lbo threads)]
            (persistent! (reduce (fn [m c] (assoc! m (.get decode (int c)) (aget res (int c))))
                                 (transient {}) (range g))))
          ;; general Object path (arbitrary accumulators)
          (let [varr (.toArray vals)
                gf   (requiring-resolve 'stratum.query.custom-agg/grouped-fold)]
            (decode! (gf codes varr g {:unit (:unit-fn value-spec)
                                       :combine (:combine value-spec)
                                       :threads threads}))))))))

;; ── group-by + aggregate offload (the transparent reducer hook) ──────────────────────────────────
(defn offload-group-by
  "Try `(group-by value-spec key-f value-f coll)` on stratum. Returns `{key -> agg}` (== the eager
   reducer) or nil to DECLINE (non-trivial pipeline / cost-gate says not worth it). A built-in agg
   (sum/min/max) takes stratum's SIMD `q/q` path; any OTHER lawful monoid takes the open-monoid
   `grouped-fold` path (tier 3), unless disabled with `:offload/custom? false`."
  [pipeline value-spec key-f value-f coll opts]
  (when (and (empty-pipeline? pipeline) (seqable? coll) (should-offload? coll key-f opts))
    (if-let [agg (agg-of value-spec opts)]
      (let [keys (ArrayList.) vals (ArrayList.)]
        (doseq [x coll] (.add keys (key-f x)) (.add vals (value-f x)))
        (let [[karr decode]   (key-codec keys)
              [varr integral?] (value-column vals)
              res  (sq/q {:from {:k karr :v varr} :group [:k] :agg [[agg :v]]})
              vfn  (if integral? long identity)]
          (persistent!
           (reduce (fn [m row] (assoc! m (decode (:k row)) (vfn (get row agg))))
                   (transient {}) res))))
      (when (and (lawful-monoid? value-spec) (not (false? (:offload/custom? opts))))
        (offload-custom-group value-spec key-f value-f coll {:threads (or (:threads opts) default-threads)})))))

;; ── equi-join + group + sum offload (stratum builds the in-memory join index) ────────────────────
(defn offload-join-group-sum
  "Join `facts` ⋈ `dim` on (fact-key x)=(dim-key y), group the joined rows by (dim-group y), and sum
   (fact-val x) per group — on stratum's SIMD engine, which builds the in-memory hash/bitmap join index
   transparently. Returns `{group-key -> sum}`. The join keys share one dictionary across both sides;
   the group key gets its own. This is the star-schema / FAQ shape (cf. #77)."
  [facts dim fact-key dim-key dim-group fact-val & [opts]]
  (let [fk (ArrayList.) fv (ArrayList.)]
    (doseq [x facts] (.add fk (fact-key x)) (.add fv (fact-val x)))
    (let [dk (ArrayList.) dg (ArrayList.)]
      (doseq [y dim] (.add dk (dim-key y)) (.add dg (dim-group y)))
      ;; shared dictionary for the join key across facts + dim (so equal keys get equal codes)
      (let [jcode (HashMap.)
            enc   (fn [k] (long (or (.get jcode k)
                                    (let [c (.size jcode)] (.put jcode k c) c))))
            n-f (.size fk) n-d (.size dk)
            fkarr (long-array n-f) dkarr (long-array n-d)
            _ (dotimes [i n-f] (aset fkarr i (enc (.get fk i))))
            _ (dotimes [i n-d] (aset dkarr i (enc (.get dk i))))
            [fvarr integral?] (value-column fv)
            [dgarr gdecode]   (key-codec dg)
            res (sq/q {:from {:fk fkarr :v fvarr}
                       :join [{:with {:dk dkarr :g dgarr} :on [:= :fk :dk] :type :inner}]
                       :group [:g] :agg [[:sum :v]]})
            vfn (if integral? long identity)]
        (persistent!
         (reduce (fn [m row] (assoc! m (gdecode (:g row)) (vfn (:sum row))))
                 (transient {}) res))))))

(defn- range-pred
  "Build a fused-filter IntPredicate ANDing range checks [lo,hi) over native long[] predicate columns.
   nil when there's nothing to filter. Primitive (no boxing) — evaluated inline in the single fused pass."
  ^java.util.function.IntPredicate [where]
  (when (seq where)
    (let [cols (object-array (map first where))
          los  (long-array (map second where))
          his  (long-array (map #(nth % 2) where))
          m    (count where)]
      (reify java.util.function.IntPredicate
        (test [_ i]
          (loop [k 0]
            (if (= k m)
              true
              (let [^longs c (aget cols k) v (aget c i)]
                (if (and (>= v (aget los k)) (< v (aget his k))) (recur (inc k)) false)))))))))

(defn offload-custom-group-columns
  "Layer A.2 — COLUMNAR custom-monoid grouped aggregate with a FUSED filter, over NATIVE long[] columns
   (the bulk-numeric entry: no row-shaped materialization). `key-codes` = dense group codes 0..G-1, `vals`
   = the value column, `value-spec` = a lawful monoid carrying a `:stratum/prim-op` (a primitive long
   combine). `:where` = [[pred-col lo hi] ...] range filters fused into the SINGLE pass. Returns a long[]
   indexed by group code (the caller owns code↔key). Eliminating the materialized filtered intermediate is
   the fusion win (~3×+ over filter-then-fold); the monoid's associativity licenses the parallel merge.
   This is the path the integration should prefer when bulk numeric columns are already in hand."
  [^longs key-codes ^longs vals n-groups value-spec & [{:keys [where threads] :or {threads default-threads}}]]
  (let [lbo (prim-combine value-spec)]
    (when (nil? lbo)
      (throw (ex-info "columnar custom path needs a :stratum/prim-op long combine" {:spec (:name value-spec)})))
    ((requiring-resolve 'stratum.query.custom-agg/grouped-fold-filtered-long)
     key-codes vals (range-pred where) n-groups (long ((:unit-fn value-spec))) lbo threads)))

(defn register!
  "Register the stratum reducer-offload into wandler.reducers' offload seam. After this, an offloadable
   high-cardinality `group-by`/`frequencies`/`sum-by` runs on stratum; everything else (low cardinality,
   unrecognized agg, non-trivial pipeline) falls back to the eager reducer (result-equal)."
  []
  (r/register-offload! offload-group-by)
  :registered)

(defn unregister! [] (r/clear-offload!))
