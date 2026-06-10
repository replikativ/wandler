(ns ansatz.faq-plan
  "The bridge from a SEMIRING query (`ansatz.semiring`) to the CERTIFIED kernel optimizer
   (`ansatz.optimize`) — step 1 of the optimizer-term integration (PROGRAMMING_MODEL.md §13).

   A counting/weighted-sum aggregating-join query lowers to a kernel term over `Map.join` + `List.foldl`;
   the optimizer applies its PROVEN Nat factorization laws — `Map.foldl_join_sum_factor` (the pre-aggregated
   FAQ index, O(distinct keys)) and `Map.foldl_join_factor` — to produce a *verified* physical plan that
   EXECUTES. The runtime `ansatz.semiring` FAQ engine and this certified kernel plan are cross-validated to
   agree on the answer: the same query, two engines (untrusted runtime vs. kernel-certified plan), one result.

   So the counting semiring's `faq-certificate` is `:level :execution` — certified by the optimizer's
   kernel theorems — distinct from `existence`'s `:level :algebra` (the runtime FAQ's own soundness laws).
   See [[programming-model-4-structures]]."
  (:require [ansatz.core :as a]
            [ansatz.semiring :as sr]
            [ansatz.optimize :as opt]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

(defn sum-join-term
  "Lower a weighted-sum aggregating join to a kernel term: `Σ (amount = snd∘snd) over Map.join custs ords`,
   where both relations are Nat-keyed 2-field records joined on field 0. This is a SEPARABLE sum (the op
   reads only the build row), so the optimizer's pre-aggregated FAQ index (`Map.foldl_join_sum_factor`)
   applies. Returns `{:term :lctx :listNN :custs-id :ords-id}` — `custs`/`ords` are fvars; feed data via `run`."
  []
  (let [N      (e/const' (nm "Nat") [])
        NN     (e/app* (e/const' (nm "Prod") [z z]) N N)        ; a 2-field record (key, value)
        PJ     (e/app* (e/const' (nm "Prod") [z z]) NN NN)      ; a join pair (custRow, ordRow)
        listNN (e/app (e/const' (nm "List") [z]) NN)
        dec    (e/const' (nm "instDecidableEqNat") [])
        cid    (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)  ; key = field 0
        custs  (e/fvar 7001) ords (e/fvar 7002)
        lctx   {7001 {:name "custs" :type listNN} 7002 {:name "ords" :type listNN}}
        join   (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid custs ords)
        amount (e/lam "p" PJ (e/app* (e/const' (nm "Prod.snd") [z z]) N N            ; snd of the ORDER row
                                     (e/app* (e/const' (nm "Prod.snd") [z z]) NN NN (e/bvar 0))) :default)
        amts   (e/app* (e/const' (nm "List.map") [z z]) PJ N amount join)
        term   (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") [])
                       (e/const' (nm "Nat.zero") []) amts)]
    {:term term :lctx lctx :listNN listNN :custs-id 7001 :ords-id 7002}))

(defn plan
  "Lower + plan a counting/sum aggregating-join query over `sr` (counting). Runs `optimize-cost` (which
   applies the PROVEN factorization laws), and attaches the semiring + its kernel `faq-certificate`. Extra
   opts (`:ndv`, `:memory-budget`, `:sizes`) are threaded to the optimizer to pick the physical strategy.
   Returns the optimizer result + `:semiring`/`:certificate` — `:verified?` is the kernel certificate."
  [sr lowered & {:as opts}]
  (let [r (apply opt/optimize-cost (a/env) (:term lowered)
                 (apply concat (merge {:lctx (:lctx lowered)} opts)))]
    (assoc r :semiring (:name sr) :certificate (sr/faq-certificate sr))))

(defn compile-fn
  "Codegen a lowered/optimized term (over the two source fvars) into a curried 2-arg Clojure fn."
  [{:keys [listNN custs-id ords-id]} t]
  (let [ly (e/lam "ords"  listNN (e/abstract1 t ords-id) :default)
        lx (e/lam "custs" listNN (e/abstract1 ly custs-id) :default)]
    (eval (a/ansatz->clj (a/env) lx []))))

(defn run
  "Execute a (lowered or optimized) term on row data: `custs`/`ords` are vectors of `[key value]` pairs."
  [lowered t custs ords]
  (long (((compile-fn lowered t) custs) ords)))

(defn srq-total
  "The SAME weighted-sum-over-join computed by the RUNTIME semiring engine: `ords ⋈ custs on key`, each
   matching pair's weight = ord-value ⊗ cust-weight(=1), summed (⊕). Cross-checks the certified kernel plan."
  [custs ords]
  (let [cust-rel (into {} (map (fn [[k _]] [{:id k} 1]) custs))                   ; cust weight 1̄
        ord-rel  (into {} (map-indexed (fn [i [k v]] [{:cid k :idx i} v]) ords))  ; ord weight = value
        j (sr/rel-join sr/counting :cid :id ord-rel cust-rel)]
    (reduce + 0 (vals j))))
