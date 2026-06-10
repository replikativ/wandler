;; Verified record-update fusion for Clojure data pipelines.
;;
;; A chain of `assoc` transforms over a schema-typed record — the bread-and-butter
;; of ETL/row pipelines — collapses to a single record builder, dropping writes
;; that are overwritten downstream (dead-write / overwrite elimination). This is
;; the EDN analogue of affine collapse: fuse the per-element functions, then
;; *algebraically* simplify the composite using a property of `assoc`, with a
;; kernel proof.
;;
;; The record schema is supplied as MALLI (`ansatz.malli/malli-record` compiles it
;; to a kernel `Prod` model: field types, key->index, and the record type). Over
;; that tuple model the algebraic laws are DEFINITIONAL:
;;   assoc k v2 (assoc k v1 r) ≡ assoc k v2 r            (overwrite elimination)
;;   assoc k2 v2 (assoc k1 v1 r) ≡ assoc k1 v1 (assoc k2 v2 r)   (disjoint commute)
;; so the composite is `isDefEq` to the optimized builder and the proof is just
;; `funext (fun r => Eq.refl _ (optimized r))`.
;;
;; The kernel `Prod` model is the reasoning shadow; execution runs on native
;; Clojure maps (the optimized fn applies only the surviving assocs).

(ns ansatz.reducers.record
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.malli :as malli])
  (:import [ansatz.kernel Env Expr TypeChecker]))

(defn- nm [s] (name/from-string s))
(def ^:private u1 (lvl/succ lvl/zero))
;; Prod level params = TYPE universe of components (0 for Nat fields), NOT u1 (=1).
;; funext/Eq.refl below DO use u1 (the SORT level of the record type, Sort 1).
(def ^:private u0 lvl/zero)

;; ============================================================
;; Record model + generic field ops over the Prod tuple
;; ============================================================

(defn model
  "Compile a Malli `:map` schema to a kernel record model:
   {:keys :index :field-types :rec-type} (see ansatz.malli/malli-record)."
  [malli-schema]
  (malli/malli-record malli-schema))

(defn- tail-type [ftypes i]
  (if (= (inc i) (count ftypes))
    (nth ftypes i)
    (e/app* (e/const' (nm "Prod") [u0 u0]) (nth ftypes i) (tail-type ftypes (inc i)))))

(defn- pfst [ftypes j r]
  (e/app* (e/const' (nm "Prod.fst") [u0 u0]) (nth ftypes j) (tail-type ftypes (inc j)) r))
(defn- psnd [ftypes j r]
  (e/app* (e/const' (nm "Prod.snd") [u0 u0]) (nth ftypes j) (tail-type ftypes (inc j)) r))
(defn- pmk [ftypes j a b] (e/app* (e/const' (nm "Prod.mk") [u0 u0]) (nth ftypes j) (tail-type ftypes (inc j)) a b))

(defn rget
  "Kernel term projecting field `i` out of record term `r`."
  [ftypes i r]
  (let [n (count ftypes)]
    (loop [j 0 cur r]
      (if (= j i)
        (if (= i (dec n)) cur (pfst ftypes i cur))
        (recur (inc j) (psnd ftypes j cur))))))

(defn rset
  "Kernel term rebuilding record `r` with field `i` set to `v`."
  [ftypes i r v]
  (let [n (count ftypes)]
    (letfn [(build [j cur]
              (if (= j i)
                (if (= i (dec n)) v (pmk ftypes i v (psnd ftypes i cur)))
                (pmk ftypes j (pfst ftypes j cur) (build (inc j) (psnd ftypes j cur)))))]
      (build 0 r))))

;; ============================================================
;; Pipeline ops + the verified collapse
;; ============================================================

(defn assoc-op
  "A record-update step `(assoc r key value)`. `kvalue` is the kernel term for the
   value; `runtime-value` the Clojure value for native execution."
  [key kvalue runtime-value]
  {:op :assoc :key key :kvalue kvalue :runtime-value runtime-value})

(defn select-keys-op
  "A terminal projection `(select-keys r ks)`. Writes to keys not in `ks` are dead
   and are eliminated."
  [ks]
  {:op :select-keys :keys (vec ks)})

(defn- build-record
  "Right-nested `Prod.mk` of `values` at `subtypes` — the inverse of the getters."
  [subtypes values]
  (if (= 1 (count subtypes))
    (first values)
    (e/app* (e/const' (nm "Prod.mk") [u0 u0]) (first subtypes) (tail-type subtypes 1)
            (first values) (build-record (subvec subtypes 1) (subvec values 1)))))

(defn- project
  "Kernel term `(select-keys r ks)` as a sub-record over the `ks` field types."
  [ftypes index ks ks-types r]
  (build-record ks-types (mapv (fn [k] (rget ftypes (get index k) r)) ks)))

(defn- nat-lit
  "Kernel term for a Nat literal (a convenience for Nat-typed fields)."
  [k]
  (e/app* (e/const' (nm "OfNat.ofNat") [lvl/zero]) (e/const' (nm "Nat") []) (e/lit-nat k)
          (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat k))))

(defn nat-assoc
  "Convenience: assoc a Nat-typed field to a constant `n`."
  [key n]
  (assoc-op key (nat-lit n) n))

(defn- apply-ops-kernel
  "Apply a sequence of assoc ops to record term `r`, in order."
  [ftypes index ops r]
  (reduce (fn [acc {:keys [key kvalue]}]
            (rset ftypes (get index key) acc kvalue))
          r ops))

(defn- net-ops
  "The surviving writes after overwrite elimination: last assoc per key wins,
   keeping first-seen key order. Records how many writes were dead."
  [ops]
  (let [last-val (reduce (fn [m op] (assoc m (:key op) op)) {} ops)
        order (distinct (map :key ops))]
    (mapv last-val order)))

(defn collapse
  "Collapse a chain of record `assoc` ops (optionally ending in a `select-keys`
   projection) over a Malli-schema'd record, justified by a kernel proof.

   Two algebraic rewrites, both definitional over the tuple model:
     - overwrite elimination: only the last write per key survives;
     - dead-field / projection pushdown: with a trailing `select-keys ks`, writes
       to keys not in `ks` are dropped.

   Returns {:ops-before :ops-after :net-ops :projected :proof :theorem-type :fn}.
   The proof (`funext` over `Eq.refl`) type-checks against `kernel-env`; `:fn` is
   a native Clojure fn applying only the surviving assocs (+ the projection)."
  ([^Env kernel-env rec-model ops] (collapse kernel-env rec-model ops {}))
  ([^Env kernel-env rec-model ops {:keys [fuel] :or {fuel 50000000}}]
   (let [{:keys [field-types index rec-type]} rec-model
         ft field-types
         tc (doto (TypeChecker. kernel-env) (.setFuel (long fuel)))
         proj (when (and (seq ops) (= :select-keys (:op (last ops)))) (last ops))
         assoc-ops (vec (if proj (butlast ops) ops))
         ks (:keys proj)
         kept? (when proj (set ks))
         ;; dead-field elimination: drop assocs to projected-away keys
         relevant (if proj (filterv #(kept? (:key %)) assoc-ops) assoc-ops)
         net (net-ops relevant)
         [result-type comp-body opt-body opt-fn]
         (if proj
           (let [ks-types (mapv #(nth ft (get index %)) ks)
                 srt (tail-type ks-types 0)
                 net-rt (mapv (juxt :key :runtime-value) net)]
             [srt
              (project ft index ks ks-types (apply-ops-kernel ft index assoc-ops (e/bvar 0)))
              (project ft index ks ks-types (apply-ops-kernel ft index net (e/bvar 0)))
              (fn [m] (clojure.core/select-keys
                       (reduce (fn [acc [k v]] (clojure.core/assoc acc k v)) m net-rt) ks))])
           (let [net-rt (mapv (juxt :key :runtime-value) net)]
             [rec-type
              (apply-ops-kernel ft index assoc-ops (e/bvar 0))
              (apply-ops-kernel ft index net (e/bvar 0))
              (fn [m] (reduce (fn [acc [k v]] (clojure.core/assoc acc k v)) m net-rt))]))
         composite (e/lam "r" rec-type comp-body :default)
         optimized (e/lam "r" rec-type opt-body :default)
         beta (e/lam "_" rec-type result-type :default)
         h (e/lam "r" rec-type (e/app* (e/const' (nm "Eq.refl") [u1]) result-type opt-body) :default)
         proof (e/app* (e/const' (nm "funext") [u1 u1]) rec-type beta composite optimized h)
         thm-type (.check tc proof)]        ; STRICT: re-checks every app arg (so a
                                            ; returned :theorem-type means a real proof)
     {:ops-before (count assoc-ops)
      :ops-after (count net)
      :net-ops net
      :projected (when proj ks)
      :proof proof
      :theorem-type thm-type
      :fn opt-fn})))
