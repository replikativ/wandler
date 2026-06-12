;; Split from the wandler.optimize monolith (cohesion audit item 5): the COST MODEL —
;; SOAC op counts + the cardinality-propagation resource model (datahike's estimate
;; made static). Heuristic by design: cost only steers the search; soundness is certify's.
(ns wandler.optimize.cost
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [wandler.optimize.certify :as cert])
  (:import [ansatz.kernel Env]))


(def cost-rewrites
  "RELATIONAL / REORDERING laws — NOT confluent, so they are NOT in the default
   fusion set (they could loop with their inverse, and whether they help depends on
   COST). The phase-4 cost driver offers these and keeps one only if it both
   verifies AND lowers estimated cost.
     List.filter_map  filter p (map g l) → map g (filter (p∘g) l)  (filter before map)
   Relational pushdowns over Map.group_by / Map.join (filter-pushdown-into-join,
   etc.) register here too — each is just an Eq theorem (Init OR one we prove, like
   the Map.* laws), per the rule-from-theorem (`@[csimp]`) design. Provable via the
   same fvar-first method; List.filter_flatMap is the key supporting Init lemma.

     Map.filter_join_pushdown  filter (p∘fst) (Map.join … xs ys) → Map.join … (filter p xs) ys

   That law is our composed theorem (List.filter_flatMap_cond ∘
   List.filter_map_pair_eq_cond) — present in the env only once admitted; a name
   whose lookup fails is silently skipped by make-simp-lemmas. It is a SOAC-count-
   neutral REORDER, so the search gates on `pipeline-cost` (cardinality), not op
   count: filtering xs BEFORE the join is cheaper, so it is auto-adopted + certified
   (see wandler.filter-join-test).

     List.elem_filter_eq_index_probe  filter (elem · ys) xs →
       filter (isSome (lookup · (group_by id ys))) xs   (nested-loop → hash semijoin)

   The semijoin is NOT cardinality-neutral in the PREDICATE: elem is an O(|ys|) scan
   per element, the probe is O(1) after a one-time O(|ys|) index build. So
   `predicate-extra-cost` charges the scan (in·base) vs the build (base) and the
   search adopts the probe form (see wandler.semijoin-test for the certified law).

     List.elem_not_filter_eq_index_probe  the ANTI-join (NOT IN / set difference):
       filter (not ∘ elem · ys) xs → filter (not ∘ isSome (lookup · (group_by id ys))) xs

   Same predicate-cost story (Bool.not is transparent to the scan/build detection)."
  ["List.filter_map" "Map.filter_join_pushdown"
   "List.elem_filter_eq_index_probe" "List.elem_not_filter_eq_index_probe"
   ;; map+filter → ONE pass: map f (filter p l) = filterMap (λx. if p x then some (f x) else
   ;; none) l. SOAC-count win (2→1), so the cost driver adopts it. Built by
   ;; cert/install-filtermap-fusion-law! (Init-only proof: filterMap_eq_map + filterMap_filter).
   "List.map_filter_filterMap"])


;; ---- cost-directed search layer (untrusted; each kept rewrite is certified) --




(defn soac-cost
  "A static cost estimate: the number of SOAC applications in a term. Each
   List.map/filter/foldl/… is a traversal that (unless it's the single outer
   consumer) allocates an intermediate collection, so FEWER is cheaper — a proxy
   for passes + allocations that the benchmark shows dominates. Cheap, monotone
   under deforestation, and enough to drive the search; a fancier model (selectivity
   tiers à la stratum/datahike) plugs in here."
  [term]
  (let [c (volatile! 0)]
    (letfn [(walk [e]
              (cond
                (e/app? e) (let [[h args] (e/get-app-fn-args e)]
                             (when (and (e/const? h) (cert/soac-names (name/->string (e/const-name h))))
                               (vswap! c inc))
                             (walk h) (run! walk args))
                (e/lam? e) (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                (e/forall? e) (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                :else nil))]
      (walk term))
    @c))


(defn soac-stages
  "Ordered SOAC op short-names in `term` (outermost-first, as encountered), e.g.
   `[\"map\" \"filter\"]` — the pipeline stages, for the plan/explain API."
  [term]
  (let [acc (volatile! [])]
    (letfn [(walk [e]
              (cond
                (e/app? e) (let [[h args] (e/get-app-fn-args e)]
                             (when (and (e/const? h) (cert/soac-names (name/->string (e/const-name h))))
                               (let [n (name/->string (e/const-name h))]
                                 (vswap! acc conj (subs n (inc (.lastIndexOf n "."))))))
                             (walk h) (run! walk args))
                (e/lam? e) (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                (e/forall? e) (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                :else nil))]
      (walk term))
    @acc))








(defn soac-cost-deep
  "`soac-cost`, but a user-helper call is counted by its INLINED body — so the gate
   sees the passes a helper boundary hides (`(map g (step1 xs))` truly costs 2, not 1).
   `seen` guards recursive helpers."
  [^Env env term]
  (let [c (volatile! 0), seen (volatile! #{})]
    (letfn [(walk [e]
              (cond
                (e/app? e) (let [[h args] (e/get-app-fn-args e)]
                             (when (e/const? h)
                               (let [nm (name/->string (e/const-name h))]
                                 (cond
                                   (cert/soac-names nm) (vswap! c inc)
                                   (and (not (cert/kernel-primitive? nm)) (not (@seen nm)))
                                   (when-let [v (some-> (env/lookup env (name/from-string nm)) .getValue)]
                                     (vswap! seen conj nm)
                                     (walk v)))))
                             (walk h) (run! walk args))
                (e/lam? e) (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                (e/forall? e) (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                :else nil))]
      (walk term))
    @c))


;; ── cardinality-propagation cost (datahike's estimate.cljc, made static) ──────
;; soac-cost counts ops; it can't tell a filter that runs BEFORE a join (small
;; input) from one that runs AFTER it (large input) — both are 2 ops. The cost
;; that the cost-search GATE actually needs is the number of elements PROCESSED,
;; which propagates cardinality through the pipeline. Heuristic, so it only
;; affects search QUALITY — every adopted rewrite is still kernel-certified.

(def ^:private soac-info
  "Per SOAC head: 0-based index of the DRIVING input list, a :kind describing how
   it transforms cardinality, the :pred index (filters) and :rhs list (joins)."
  {"List.map"       {:list 3 :kind :map}
   "List.filter"    {:list 2 :kind :filter :pred 1}
   "List.foldl"     {:list 4 :kind :fold}
   "List.foldr"     {:list 4 :kind :fold}
   "List.length"    {:list 1 :kind :fold}   ; count consumer — the order-invariant boundary
   "List.flatMap"   {:list 3 :kind :expand}
   "List.eraseDups" {:list 2 :kind :dedup}
   "List.mergeSort" {:list 1 :kind :sort}
   "Map.group_by"   {:list 4 :kind :group}
   "Map.join"       {:list 6 :kind :join :rhs 7}})


(def ^:private join-build-weight
  "Hash-join cost asymmetry: the INDEXED side (rhs, `group_by lf ys`) pays this per
   element to BUILD the index; the DRIVER side pays 1 per element to probe (O(1) each).
   >1 so indexing the SMALLER side is cheaper — which is exactly the `Map.join_comm`
   reorder, certifiable for count queries via the `Map.join_length_comm` Perm→Eq bridge."
  2.0)


(def ^:private default-selectivity
  "Static fallback pass-rates by the predicate's head comparator (datahike
   estimate.cljc): equality selective, ranges moderate, ≠ keeps most."
  {:eq 0.1 :range 0.33 :neq 0.9 :other 0.5})


(defn- pred-selectivity
  "Estimate a filter predicate's pass-rate from the comparator heading its
   β-reduced body; unknown predicates → 0.5. A measured profile or a
   refinement-derived bound overrides this via pipeline-cost's :selectivity."
  [pred]
  (let [body (loop [b pred] (if (e/lam? b) (recur (e/lam-body b)) b))
        [h _] (e/get-app-fn-args body)
        nm (when (e/const? h) (name/->string (e/const-name h)))]
    (case nm
      ("Eq" "BEq.beq" "Nat.beq" "Nat.decEq" "decide") (:eq default-selectivity)
      ("Nat.ble" "Nat.blt" "Nat.le" "Nat.lt" "LE.le" "LT.lt" "GE.ge" "GT.gt") (:range default-selectivity)
      ("Ne" "ne") (:neq default-selectivity)
      (:other default-selectivity))))


(def ^:private membership-scan-names
  "Predicate ops whose cost is the SIZE of the list they scan (a per-element O(m)
   membership test)."
  #{"List.elem" "List.contains" "List.elemBy" "List.any" "List.all"})


(def ^:private index-build-names
  "Predicate ops that BUILD a probe index — a one-time O(m) cost (loop-invariant,
   hoisted out of the filter), after which each probe is O(1)."
  #{"Map.group_by"})


(defn- predicate-extra-cost
  "Beyond the default O(1), estimate `[per-element-extra one-time-build]` for a
   filter predicate by scanning its body: a membership SCAN (List.elem … over a
   free list) costs `base` PER element; an index BUILD (Map.group_by) is a ONE-
   TIME `base` with O(1) probes thereafter. This is what lets the cardinality cost
   model value the verified semijoin — nested-loop elem-filter (in·base) versus
   build-once index probe (base + in)."
  [pred base]
  (let [per-el (atom 0.0) one-time (atom 0.0)]
    (letfn [(go [e]
              (cond
                (e/app? e)
                (do (let [[h _] (e/get-app-fn-args e)]
                      (when (e/const? h)
                        (let [n (name/->string (e/const-name h))]
                          (cond (membership-scan-names n) (swap! per-el + base)
                                (index-build-names n)      (swap! one-time + base)))))
                    (go (e/app-fn e)) (go (e/app-arg e)))
                (e/lam? e) (go (e/lam-body e))
                (e/forall? e) (go (e/forall-body e))))]
      (go pred))
    [@per-el @one-time]))


(defn pipeline-resources
  "RESOURCE PROFILE of a SOAC pipeline `term`: {:size <output cardinality> :time <elements
   processed> :memory <peak working set>}. :time is the cardinality-propagation cost (datahike-style,
   made static — each op pays its input size, filters shrink, join/flatMap expand, folds collapse).
   :memory is the MAX over the plan of each node's footprint: streaming ops (map/filter/expand/dedup)
   add NOTHING; join carries its build-side index (O(|build|)); sort/group carry their buffer
   (O(|input or keys|)). This is the dimension the memory-aware physical-strategy choice gates on
   (hoist the index iff build-side ≤ budget, else spill/sort-merge — see docs/PHYSICAL_PLANNING.md).

   Opts:
     :base        source-list size (default 1000)
     :fanout      expand/join multiplicity (default 3)
     :selectivity (fn pred→rate) OR (map pred-string→rate) — measured-profile / refinement override.
     :sizes       per-source {fvar-id→cardinality} (an engine's :estimate)."
  ([term] (pipeline-resources term {}))
  ([term {:keys [base fanout selectivity sizes] :or {base 1000.0 fanout 3.0}}]
   (let [sel (cond (fn? selectivity) selectivity
                   (map? selectivity) (fn [p] (or (get selectivity (e/->string p)) (pred-selectivity p)))
                   :else pred-selectivity)
         size-of (fn [e] (or (when (and sizes (e/fvar? e)) (get sizes (e/fvar-id e))) base))]
     (letfn [(walk [e]                          ; → [size time mem]   (mem = peak working set)
               (let [[h args] (e/get-app-fn-args e)
                     info (when (e/const? h) (soac-info (name/->string (e/const-name h))))]
                 (if (and info (> (count args) (long (:list info))))
                   (let [[in cin min*] (walk (nth args (long (:list info))))]
                     (case (:kind info)
                       :map    [in (+ cin in) min*]                          ; streaming: no extra mem
                       :filter (let [pred (nth args (long (:pred info)))
                                     [per-el one-time] (predicate-extra-cost pred base)]
                                 [(* in (double (sel pred))) (+ cin in (* in per-el) one-time) min*])
                       :fold   [1.0 (+ cin in) min*]                          ; scalar acc: O(1)
                       :expand [(* in fanout) (+ cin in) min*]
                       :dedup  [(* in 0.7) (+ cin in) min*]
                       :sort   [in (+ cin (* in (Math/log (max 2.0 in)))) (max min* in)]  ; in-mem sort buffer
                       :group  [in (+ cin in) (max min* in)]                  ; holds the grouped structure
                       :join   (let [[r cr mr] (walk (nth args (long (:rhs info))))]
                                 ;; OUTPUT order-invariant (min). TIME = probe driver `in` + BUILD the
                                 ;; INDEXED side `r` at join-build-weight (the only order-dependent
                                 ;; term → index the smaller side, Map.join_comm). MEMORY = the
                                 ;; build-side index footprint `r` (the thing a hoist materializes;
                                 ;; O(|keys|) once pre-aggregated). The memory-aware planner hoists
                                 ;; iff r ≤ budget, else spills.
                                 [(* (min in r) fanout) (+ cin cr in (* join-build-weight r)) (max min* mr r)])
                       [in cin min*]))
                   [(size-of e) 0.0 0.0])))]
       (let [[s t m] (walk term)] {:size s :time t :memory m})))))


(defn pipeline-cost
  "Estimated total elements PROCESSED by SOAC pipeline `term` (the :time projection of
   `pipeline-resources`): datahike-style cardinality propagation, made static. Lower is cheaper;
   drives optimize-cost's adopt gate so a SOAC-count-neutral REORDER is preferred by its cardinality
   win. See `pipeline-resources` for the full {time, memory} profile + opts."
  ([term] (pipeline-cost term {}))
  ([term opts] (:time (pipeline-resources term opts))))


(defn mentions-const?
  "True if expr `e` mentions the constant named `cname` anywhere (used by the pre-check to keep a
   SOAC-trivial body that nonetheless has a rewritable costly predicate, e.g. List.elem)."
  [e cname]
  (cond
    (e/const? e)  (= cname (name/->string (e/const-name e)))
    (e/app? e)    (or (mentions-const? (e/app-fn e) cname) (mentions-const? (e/app-arg e) cname))
    (e/lam? e)    (or (mentions-const? (e/lam-type e) cname) (mentions-const? (e/lam-body e) cname))
    (e/forall? e) (or (mentions-const? (e/forall-type e) cname) (mentions-const? (e/forall-body e) cname))
    :else false))
