;; Phase 5.1 (clean tree) — THE COST MODEL: SOAC op counts + the cardinality-propagation resource
;; model (datahike-estimate made static). Heuristic — cost only STEERS the search; soundness is
;; certifys. Clean copy; the relational cost-rewrites retarget to the aggregate laws in 5.5.
(ns wandler.clean.optimize.cost
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [wandler.clean.optimize.certify :as cert])
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


(defn soac-depth-cost
  "Honest cost for the e-graph's NON-CONFLUENT reorder/hoist search: a SOAC op is charged
   `base^depth`, where `depth` is the number of enclosing SOAC step-λs. A fold/map nested inside
   a `map`/`filter`/`foldl` step-λ runs ONCE PER ELEMENT of the outer collection, so its true cost
   is exponential in the nesting — exactly the signal `soac-cost` (flat count) and `pipeline-cost`
   (which doesn't descend step-λs, to keep factorization gates intact) both miss. This is what lets
   extraction PREFER a loop-invariant HOIST: pulling an inner fold out of a map's step-λ drops it
   from depth 1 (base¹) to depth 0 (1).

     foldl + 0 (map (λx. x * foldl + 0 ys) xs)   →  1 (foldl) + 1 (map) + base¹ (inner fold)  ≈ 12
     (foldl + 0 (map id xs)) * (foldl + 0 ys)    →  1 + 1 + 1                                  =  3

   A λ ARGUMENT of a SOAC is a per-element step ⇒ its body is costed at depth+1; any other λ (a
   let-bound function value) does not multiply work, so its body stays at the same depth. Used ONLY
   as the e-graph extraction/adopt cost — `pipeline-cost` remains the cardinality gate for the
   confluent/factorization path, so that invariant is untouched. `base` > 1 is all that matters for
   ranking; 10 keeps the numbers legible."
  [term & {:keys [base] :or {base 10.0}}]
  (letfn [(walk [e depth]
            (cond
              (e/app? e)
              (let [[h args] (e/get-app-fn-args e)
                    soac? (and (e/const? h) (cert/soac-names (name/->string (e/const-name h))))]
                (+ (if soac? (Math/pow (double base) (double depth)) 0.0)
                   (reduce + 0.0
                           (map (fn [a]
                                  (if (and soac? (e/lam? a))
                                    (walk (e/lam-body a) (inc depth))  ; per-element step body
                                    (walk a depth)))
                                args))))
              (e/lam? e)    (walk (e/lam-body e) depth)   ; non-SOAC λ: does not multiply
              (e/forall? e) (walk (e/forall-body e) depth)
              (e/let? e)    (+ (walk (e/let-value e) depth) (walk (e/let-body e) depth))
              :else 0.0))]
    (walk term 0)))

(defn soac-invariant-cost
  "Effective-DEPENDENCE cost (the under-binder #C signal): a SOAC pays `base^k` where k = the number of
   distinct ENCLOSING binders its subtree actually DEPENDS ON — counting both opened-binder fvars
   (id ≥ 950000000, present during under-binder extraction) and enclosing step-λ bvars (present in the
   final re-abstracted term). A loop-INVARIANT SOAC (syntactically under a binder it doesn't use) pays
   base^0. This REWARDS making a subterm invariant — e.g. the nested-FAQ inner hoist `∑y x·y → x·(∑y y)`,
   which leaves `∑y y` under the outer `λx` (so `soac-depth-cost` is unchanged) but x-INDEPENDENT (so
   THIS cost drops). Used as the LEXICOGRAPHIC SECONDARY after `soac-depth-cost`: depth drives the
   hoists that move a SOAC out of a binder (Step 1, the FAQ outer hoist); invariance drives the inner
   hoist that makes the next outer hoist possible."
  [term & {:keys [base] :or {base 10.0}}]
  (letfn [(enc [ex d acc]   ; collect enclosing-binder identities used in `ex` (d = current λ-depth)
            (cond
              (e/fvar? ex) (when (>= (e/fvar-id ex) 950000000) (vswap! acc conj [:fv (e/fvar-id ex)]))
              (e/bvar? ex) (let [l (- d 1 (e/bvar-idx ex))] (when (>= l 0) (vswap! acc conj [:bv l])))
              (e/app? ex)  (let [[h ar] (e/get-app-fn-args ex)] (enc h d acc) (run! #(enc % d acc) ar))
              (e/lam? ex)  (do (enc (e/lam-type ex) d acc) (enc (e/lam-body ex) (inc d) acc))
              (e/forall? ex) (do (enc (e/forall-type ex) d acc) (enc (e/forall-body ex) (inc d) acc))
              :else nil))
          (eff [ex d]   ; # distinct enclosing binders the SOAC subtree depends on (own binders excluded)
            (let [acc (volatile! #{})]
              (enc ex d acc)
              (count (filter (fn [[t l]] (or (= t :fv) (< l d))) @acc))))
          (walk [ex d]
            (cond
              (e/app? ex) (let [[h ar] (e/get-app-fn-args ex)
                                s? (and (e/const? h) (cert/soac-names (name/->string (e/const-name h))))]
                            (+ (if s? (Math/pow (double base) (double (eff ex d))) 0.0)
                               (reduce + 0.0 (map (fn [a] (if (e/lam? a) (walk (e/lam-body a) (inc d)) (walk a d))) ar))))
              (e/lam? ex)    (walk (e/lam-body ex) (inc d))
              (e/forall? ex) (walk (e/forall-body ex) d)
              (e/let? ex)    (+ (walk (e/let-value ex) d) (walk (e/let-body ex) d))
              :else 0.0))]
    (walk term 0)))


;; ── cardinality-propagation cost (datahike's estimate.cljc, made static) ──────
;; soac-cost counts ops; it can't tell a filter that runs BEFORE a join (small
;; input) from one that runs AFTER it (large input) — both are 2 ops. The cost
;; that the cost-search GATE actually needs is the number of elements PROCESSED,
;; which propagates cardinality through the pipeline. Heuristic, so it only
;; affects search QUALITY — every adopted rewrite is still kernel-certified.



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


;; ── per-op COST DESCRIPTORS (the framework seam) ─────────────────────────────
;; Each head → {:list <driving-input arg idx>, :tf <transform>}. The walk descends the :list input,
;; then `:tf` computes this op's [size time mem] from that input profile + the op's args + a context.
;; `:tf` signature = (ctx in-profile args benv walk) → [size time mem]; ctx carries {:base :fanout
;; :sel :ndv}, and `walk` lets a binary op (join) recurse its rhs.
;;
;; This is the OP-COST side of the cost handshake (the per-source cardinality/selectivity side —
;; datahike live :estimate, JIT profile-selectivity — flows in via pipeline-resources opts). The
;; registry is OPEN: an engine (stratum fused-join, raster SIMD kernel, a datahike pushdown) declares
;; how ITS op transforms cardinality/time/memory by `register-op-cost!` — the single declarative place
;; engine costs live, mirroring the codegen / surface-elaborator registries. Adding an op = data.
;; (Roadmap COST_MODEL_REDESIGN §4: :list and output-list? to derive from the kernel SIGNATURE — a
;; cheap return-type read — rather than this hand-keyed name table; the transforms stay.)
(defonce ^{:doc "head (string) → cost descriptor {:list idx :tf (ctx in args benv walk)→[size time mem]}.
   Seeded with the Init SOAC/relational ops; engines register their own via register-op-cost!."}
  op-cost-registry
  (atom
  {"List.map"       {:list 3 :tf (fn [_   [in cin mn] _ _ _] [in (+ cin in) mn])}                ; streaming
   "List.filter"    {:list 2 :tf (fn [ctx [in cin mn] args _ _]
                                   (let [pred (nth args 1)
                                         [per-el one-time] (predicate-extra-cost pred (:base ctx))]
                                     [(* in (double ((:sel ctx) pred))) (+ cin in (* in per-el) one-time) mn]))}
   "List.foldl"     {:list 4 :tf (fn [_   [in cin mn] _ _ _] [1.0 (+ cin in) mn])}               ; scalar acc
   "List.foldr"     {:list 4 :tf (fn [_   [in cin mn] _ _ _] [1.0 (+ cin in) mn])}
   "List.length"    {:list 1 :tf (fn [_   [in cin mn] _ _ _] [1.0 (+ cin in) mn])}               ; count boundary
   "List.flatMap"   {:list 3 :tf (fn [ctx [in cin mn] _ _ _] [(* in (:fanout ctx)) (+ cin in) mn])}
   "List.eraseDups" {:list 2 :tf (fn [_   [in cin mn] _ _ _] [(* in 0.7) (+ cin in) mn])}
   "List.mergeSort" {:list 1 :tf (fn [_   [in cin mn] _ _ _] [in (+ cin (* in (Math/log (max 2.0 in)))) (max mn in)])}
   "Map.group_by"   {:list 4 :tf (fn [_   [in cin mn] _ _ _] [in (+ cin in) (max mn in)])}
   "Map.join"       {:list 6 :tf (fn [ctx [in cin mn] args benv walk]
                                   (let [[r cr mr] (walk (nth args 7) benv)        ; rhs (build) side
                                         out (if (:ndv ctx) (max 1.0 (/ (* in r) (double (:ndv ctx))))
                                                            (* (min in r) (:fanout ctx)))]
                                     [out (+ cin cr in (* join-build-weight r)) (max mn mr r)]))}}))

(defn register-op-cost!
  "Register/override the cost descriptor for op `head` (string). `descriptor` is
   {:list <driving-input arg idx> :tf (fn [ctx in-profile args benv walk] → [size time mem])}.
   The seam an engine uses to declare how its operation transforms cardinality/time/memory — so the
   planner can cost a plan that lowers to it. Idempotent; later registrations override. Returns head."
  [head descriptor]
  (swap! op-cost-registry assoc head descriptor)
  head)


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
     :sizes       per-source {fvar-id→cardinality} (an engine's :estimate).
     :ndv         distinct join-key values. When given, a join's OUTPUT cardinality uses datahike's
                  per-key fan-out estimate |L|·|R|/ndv (estimate.cljc: attr-total/distinct-v) instead
                  of the coarse min(|L|,|R|)·fanout default — the textbook equi-join selectivity."
  ([term] (pipeline-resources term {}))
  ([term {:keys [base fanout selectivity sizes ndv] :or {base 1000.0 fanout 3.0}}]
   (let [sel (cond (fn? selectivity) selectivity
                   (map? selectivity) (fn [p] (or (get selectivity (e/->string p)) (pred-selectivity p)))
                   :else pred-selectivity)
         size-of (fn [e] (or (when (and sizes (e/fvar? e)) (get sizes (e/fvar-id e))) base))
         ctx {:base base :fanout fanout :sel sel :ndv ndv}
         op-cost @op-cost-registry]
     ;; `benv` = sizes of let-bound vars (de-Bruijn, innermost first), so a shared subexpression's
     ;; size flows into its `let` body and is paid for ONCE — the only new state. A λ is a function
     ;; value, returned as a unit leaf and NOT descended (the consuming op accounts per-element):
     ;; this preserves the invariant that SOAC step-λs keep zero cost, so factorization gates hold.
     (letfn [(walk [e benv]                     ; → [size time mem]   (mem = peak working set)
               (cond
                 (e/bvar? e)  [(let [i (e/bvar-idx e)] (if (< i (count benv)) (nth benv i) base)) 0.0 0.0]
                 (e/lam? e)   [1.0 0.0 0.0]
                 (e/let? e)   (let [[sv tv mv] (walk (e/let-value e) benv)
                                    [sb tb mb] (walk (e/let-body e) (cons sv benv))]
                                [sb (+ tv tb) (max mv mb)])        ; value paid ONCE → CSE is cheaper
                 (e/app? e)
                 (let [[h args] (e/get-app-fn-args e)
                       desc (when (e/const? h) (op-cost (name/->string (e/const-name h))))]
                   (if (and desc (> (count args) (long (:list desc))))
                     ((:tf desc) ctx (walk (nth args (long (:list desc))) benv) args benv walk)
                     ;; non-SOAC app = a TREE node (Nat.add, Prod.mk, …): output size unchanged
                     ;; (`base`), but TIME sums the branches and MEM is their peak. Non-data args
                     ;; (types, scalars, λ) recurse to time 0, so only real pipeline branches add cost.
                     (let [ps (map #(walk % benv) args)]
                       [(size-of e) (reduce + 0.0 (map second ps)) (reduce max 0.0 (map #(nth % 2) ps))])))
                 :else [(size-of e) 0.0 0.0]))]   ; fvar / const / lit
       (let [[s t m] (walk term [])] {:size s :time t :memory m})))))


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
