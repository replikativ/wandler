(ns wandler.backend.stratum
  "OPTIONAL stratum execution backend (#76, Integration 2 — transparent reducer offload). Transparently
   routes a wandler group-by/aggregate REDUCER — code NOT written as a query — to stratum's in-memory
   SIMD columnar engine when beneficial. Loads ONLY under the :stratum alias.

   Key facts that make this work:
   - `stratum.query/q` is the engine entry and its load graph is PARQUET/HADOOP-FREE — so we get the
     in-memory SIMD engine without the heavy deps (require stratum.query, NOT stratum.api).
   - The data lives as ordinary JVM primitive arrays — `(q/q {:from {col->array} :group [..] :agg [..]})`
     runs purely in-memory, no files.

   Mechanism: columnarize the input (one pass), run the group+agg on stratum, map results back to the
   `{key -> merged-value}` map the eager reducer would produce. An UNRECOGNIZED/declined shape returns
   nil → reducers' eager path runs (result-equal). The verified monoid spec is the equivalence
   certificate; stratum is a trusted fast oracle (same trust model as the datahike/stratum lift bridge).

   Generality: `key-f`/`value-f` run in CLOJURE to build the columns, so they can be ARBITRARY — the
   key is dictionary-encoded by value equality, so any/composite key works; numeric keys skip the dict
   and let stratum's SIMD grouping do the work (where the win is). Only the aggregation monoid must be
   recognized (sum family → :sum; this also covers `frequencies` = sum-of-ones)."
  (:require [stratum.query :as sq]
            [wandler.reducers :as r])
  (:import [wandler.reducers Pipeline]
           [java.util HashMap ArrayList]))

(def ^:private sum-monoids
  "Monoid spec :names that map to stratum's :sum aggregation."
  #{:nat/add :int/add :float/add})

(defn- agg-of [value-spec]
  (when (contains? sum-monoids (:name value-spec)) :sum))

(defn- empty-pipeline?
  "Offload v1 only handles a bare group-by (no transform prefix); a non-trivial pipeline declines → eager.
   (Pushing filter/map into stratum's :where/projection is the Integration-1 generalization.)"
  [p]
  (or (nil? p)
      (and (sequential? p) (empty? p))
      (and (instance? Pipeline p) (empty? (:steps p)))))

(defn offload-group-by
  "Try to run `(group-by value-spec key-f value-f coll)` on stratum's in-memory SIMD engine.
   Returns `{key -> sum}` (== the eager reducer's result) or nil to DECLINE."
  [pipeline value-spec key-f value-f coll opts]
  (when (and (empty-pipeline? pipeline) (agg-of value-spec) (seqable? coll))
    (let [keys (ArrayList.) vals (ArrayList.)]
      (doseq [x coll] (.add keys (key-f x)) (.add vals (value-f x)))
      (let [n             (.size keys)
            numeric-keys? (loop [i 0] (cond (= i n) true
                                            (integer? (.get keys i)) (recur (inc i))
                                            :else false))
            integral?     (loop [i 0] (cond (= i n) true
                                            (integer? (.get vals i)) (recur (inc i))
                                            :else false))
            karr          (long-array n)
            ;; dictionary for non-numeric keys: code -> original key, built in first-seen order
            code          (when-not numeric-keys? (HashMap.))
            decode        (when-not numeric-keys? (ArrayList.))
            varr          (if integral? (long-array n) (double-array n))]
        (dotimes [i n]
          (let [k (.get keys i)]
            (aset karr i (long (if numeric-keys?
                                 (long k)
                                 (or (.get ^HashMap code k)
                                     (let [c (.size ^ArrayList decode)]
                                       (.put ^HashMap code k c) (.add ^ArrayList decode k) c))))))
          (if integral?
            (aset ^longs varr i (long (.get vals i)))
            (aset ^doubles varr i (double (.get vals i)))))
        (let [res  (sq/q {:from {:k karr :v varr} :group [:k] :agg [[:sum :v]]})
              kfn  (if numeric-keys? identity (fn [c] (.get ^ArrayList decode (int c))))
              vfn  (if integral? long identity)]
          (persistent!
           (reduce (fn [m row] (assoc! m (kfn (:k row)) (vfn (:sum row))))
                   (transient {}) res)))))))

(defn register!
  "Register the stratum reducer-offload into wandler.reducers' offload seam. After this, an offloadable
   `group-by`/`frequencies`/`sum-by` runs on stratum; everything else falls back to the eager reducer."
  []
  (r/register-offload! offload-group-by)
  :registered)

(defn unregister! [] (r/clear-offload!))
