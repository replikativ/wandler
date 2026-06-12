(ns wandler.plan
  "A typed LENS onto the relational / SOAC fragment of a kernel term — NOT a new IR, a structured
   VIEW that reads a CIC pipeline term as a plan tree of `{:op …}` nodes. The kernel term remains
   the single source of truth (and the thing the optimizer rewrites + the kernel certifies); this
   just makes its relational shape inspectable.

   `term->plan` recognizes List.map/filter/foldl/foldr/flatMap/filterMap, Map.join/group_by, and the
   SEMIJOIN (a filter whose predicate is a membership scan, List.elem). The leaf is `:source` (a free
   var or literal). `plan->str` renders the tree.

   This is the shared interface for explain/cost AND the planned α/γ BRIDGE to external engines:
   datahike's `LScan/LFilter/LJoin` (query/ir.cljc) and stratum's `LScan/LFilter/LJoin` map to/from
   these exact plan nodes, which map to/from kernel terms — so a cross-engine query optimizes once,
   in the certified kernel IR, then γ-lowers back to each physical executor. See the architecture
   notes / [[end-to-end-planning-design]]."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(def op-layout
  "head-constant → {:op kw + field→arg-index}. Indices are into the VALUE args of
   `(e/get-app-fn-args term)` (universe levels are on the head, not in args). Recursive-input
   fields (:input/:left/:right) are themselves parsed into sub-plans."
  {"List.map"       {:op :map        :fn 2 :input 3}
   "List.filter"    {:op :filter     :pred 1 :input 2}
   "List.filterMap" {:op :filter-map :fn 2 :input 3}
   "List.foldl"     {:op :foldl      :fn 2 :init 3 :input 4}
   "List.foldr"     {:op :foldr      :fn 2 :init 3 :input 4}
   "List.flatMap"   {:op :flat-map   :fn 2 :input 3}
   "Map.group_by"   {:op :group-by   :fn 3 :input 4}
   "Map.join"       {:op :join       :kf 4 :lf 5 :left 6 :right 7}})

(defn- mentions? [e cname]
  (cond
    (e/const? e)  (= cname (name/->string (e/const-name e)))
    (e/app? e)    (or (mentions? (e/app-fn e) cname) (mentions? (e/app-arg e) cname))
    (e/lam? e)    (or (mentions? (e/lam-type e) cname) (mentions? (e/lam-body e) cname))
    (e/forall? e) (or (mentions? (e/forall-type e) cname) (mentions? (e/forall-body e) cname))
    :else false))

(declare term->plan)

(def ^:private child? #{:input :left :right})

(defn- parse-node [spec head args]
  (let [node (reduce-kv (fn [m k idx]
                          (if (= k :op) m
                              (let [v (nth args idx)]
                                (assoc m k (if (child? k) (term->plan v) v)))))
                        {:op (:op spec)} spec)]
    ;; ::raw keeps the head + full arg vector + layout so plan->term can REBUILD the exact term
    ;; (replacing only the child positions with the possibly-rewritten sub-plans) — round-trippable.
    (-> node
        (assoc ::raw {:head head :args (vec args) :layout spec})
        ;; a filter whose predicate scans for membership IS a (nested-loop) semijoin — annotate so
        ;; the explain/cost layer can flag the index-probe rewrite (List.elem_filter_eq_index_probe).
        (cond-> (and (= (:op node) :filter) (:pred node) (mentions? (:pred node) "List.elem"))
          (assoc :semijoin? true)))))

(defn term->plan
  "Parse a kernel pipeline `term` into a plan tree (a map of `{:op …}` nodes). Non-SOAC subterms
   become `{:op :source :term …}` leaves. Total — any term parses (worst case a single source)."
  [term]
  (let [[h args] (e/get-app-fn-args term)
        hn   (when (e/const? h) (name/->string (e/const-name h)))
        spec (get op-layout hn)]
    (if (and spec (> (count args) (reduce max 0 (vals (dissoc spec :op)))))
      (parse-node spec h args)
      {:op :source :term term})))

(defn plan->term
  "The inverse of `term->plan`: rebuild a kernel term from a plan tree. Reconstructs each node from
   its `::raw` head+args, replacing the child positions (:input/:left/:right) with the reconstructed
   sub-plans — so an UNCHANGED plan round-trips to the original term, and a plan whose children were
   rewritten (e.g. by an external planner / γ-lowering) rebuilds the new term. `:source` is its term."
  [plan]
  (if (= (:op plan) :source)
    (:term plan)
    (let [{:keys [head args layout]} (::raw plan)
          args' (reduce-kv (fn [a k idx]
                             (if (child? k) (assoc a idx (plan->term (get plan k))) a))
                           (vec args) layout)]
      (apply e/app* head args'))))

(defn- op-label [node]
  (case (:op node)
    :map "map" :filter (if (:semijoin? node) "filter⟨∈→idx⟩" "filter")
    :filter-map "filterMap" :foldl "foldl" :foldr "foldr" :flat-map "flatMap"
    :group-by "group_by" :join "join" :source "·" (name (:op node))))

(defn ops
  "The ordered op labels of a (linear) plan, innermost source → outermost op — the pipeline 'stages'
   view. For a join (two inputs) both sides are summarized as `join`."
  [plan]
  (loop [p plan, acc ()]
    (cond
      (= (:op p) :source) (vec acc)
      (:input p)          (recur (:input p) (cons (op-label p) acc))
      :else               (vec (cons (op-label p) acc)))))   ; join/leaf: stop

(defn plan->str
  "Render a plan tree as `src → op → op` (a join shows both input pipelines)."
  [plan]
  (letfn [(render [p]
            (case (:op p)
              :source "·"
              :join (str "(" (render (:left p)) ") ⋈ (" (render (:right p)) ") → join")
              (str (render (:input p)) " → " (op-label p))))]
    (render plan)))
