;; Split from the wandler.optimize monolith (cohesion audit item 5): PHYSICAL STRATEGIES —
;; the dedicated cost-chosen plan drivers (join reorder, count/fold factorization,
;; grace-hash spill, pre-aggregated FAQ index, invariant-index hoisting). Every adoption
;; is gated by cert/verified-rewrite?.
(ns wandler.optimize.physical
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [wandler.optimize.certify :as cert]
            [wandler.optimize.cost :as cost])
  (:import [ansatz.kernel Env]))

(declare compose-trans)


;; ---- join reordering (#29): the Perm→Eq bridge, cost-driven --------------------

(defn count-join
  "Match `List.length (Map.join K X Y dec kf lf xs ys)` — a COUNT over a join, the
   ORDER-INVARIANT boundary where the bag-equivalence `Map.join_comm` becomes a real
   Eq. Returns the join's 8 args (the reorder telescope), or nil."
  [term]
  (let [[h args] (e/get-app-fn-args term)]
    (when (and (e/const? h) (= "List.length" (name/->string (e/const-name h))) (>= (count args) 2))
      (let [[jh jargs] (e/get-app-fn-args (nth args 1))]
        (when (and (e/const? jh) (= "Map.join" (name/->string (e/const-name jh))) (>= (count jargs) 8))
          (vec (take 8 jargs)))))))


(defn try-join-reorder
  "Cost-driven JOIN REORDER for count queries, certified by the `Map.join_length_comm`
   Perm→Eq bridge. If `term` = length (join … kf lf xs ys) and the bridge law is admitted,
   it rewrites to length (join … lf kf ys xs) — swapping which side is INDEXED. Adopt iff
   that strictly lowers `cost/pipeline-cost` (index the smaller side) AND the bridge proof
   strict-certifies the Eq (`cert/verified-rewrite?`). Returns {:term :proof :verified? true
   :changed? true} or nil.

   This is the dedicated path the simp cost-rewrite pool CANNOT take: `Map.join_length_comm`
   is PERMUTATIVE (LHS ~ RHS modulo arg-swap), so simp's perm-guard would canonicalize it to
   a fixed orientation rather than choose by cost. Here we apply the law directly and let the
   cardinality cost decide — soundness still rests entirely on `cert/verified-rewrite?`."
  [^Env env term & {:keys [lctx selectivity sizes]}]
  (when-let [jargs (count-join term)]
    (let [proof (apply e/app* (e/const' (name/from-string "Map.join_length_comm") []) jargs)
          st (cert/mk-st env lctx)
          ;; infer-type fails gracefully (→ nil) if the bridge law isn't registered
          ptype (try (tc/infer-type st proof) (catch Throwable _ nil))
          [_ eqargs] (when ptype (e/get-app-fn-args ptype))]   ; @Eq Nat LHS RHS
      (when (and eqargs (>= (count eqargs) 3))
        (let [rhs (nth eqargs 2)
              res {:term rhs :proof proof :changed? true :rw :join-reorder}]
          (when (and (< (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                        (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                     (cert/verified-rewrite? env term res :lctx lctx))
            (assoc res :verified? true)))))))


(defn try-count-factor
  "Cost-driven COUNT FACTORIZATION — aggregation-THROUGH-join (the FAQ asymptotic win,
   count instance). If `term` = length (Map.join … kf lf xs ys) and `Map.count_join_factor`
   is admitted, rewrite to  sum (map (λx. length (bucket (kf x) ys)) xs)  — count the join
   WITHOUT materializing the |xs|·|ys| product (no pairs built; cost/pipeline-cost charges that
   product on the LHS, ~0 on the factored sum). Adopt iff it strictly lowers cost/pipeline-cost
   AND the proof strict-certifies. Returns {:term :proof :verified? :changed? :rw} or nil.

   Same dedicated-path shape as `try-join-reorder`: applied directly (not via the simp pool)
   because the law's RHS is a different SOAC SHAPE the cost-search must choose by cardinality,
   not op-count (cost/soac-cost actually RISES 1→2; the materialization win is only visible to
   cost/pipeline-cost). Soundness rests entirely on `cert/verified-rewrite?`. The law itself is proven
   on Map.join's flatMap form via length_flatMap+length_map (see wandler.factor-test)."
  [^Env env term & {:keys [lctx selectivity sizes]}]
  (when-let [jargs (count-join term)]
    (let [proof (apply e/app* (e/const' (name/from-string "Map.count_join_factor") []) jargs)
          st (cert/mk-st env lctx)
          ptype (try (tc/infer-type st proof) (catch Throwable _ nil))   ; nil if law absent
          [_ eqargs] (when ptype (e/get-app-fn-args ptype))]             ; @Eq Nat LHS RHS
      (when (and eqargs (>= (count eqargs) 3))
        (let [rhs (nth eqargs 2)
              res {:term rhs :proof proof :changed? true :rw :count-factor}]
          (when (and (< (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                        (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                     (cert/verified-rewrite? env term res :lctx lctx))
            (assoc res :verified? true)))))))


(defn- fold-join
  "Match `List.foldl op e (Map.join K X Y dec kf lf xs ys)` — ANY aggregate (count/sum/max/…) folded
   over a join. Returns {:S :op :e :jargs} (jargs = the join's 8 args), or nil."
  [term]
  (let [[h args] (e/get-app-fn-args term)]
    (when (and (e/const? h) (= "List.foldl" (name/->string (e/const-name h))) (>= (count args) 5))
      (let [[S _PXY op ini lst] (take 5 args)
            [jh jargs] (e/get-app-fn-args lst)]
        (when (and (e/const? jh) (= "Map.join" (name/->string (e/const-name jh))) (>= (count jargs) 8))
          {:S S :op op :e ini :jargs (vec (take 8 jargs))})))))


(defn try-fold-factor
  "Cost-driven AGGREGATION-THROUGH-JOIN factorization, GENERAL over the aggregate (count/sum/max/any
   foldl — `Map.foldl_join_factor`, no monoid axioms). FUSES first (so `foldl op e (map proj (join))`
   collapses via foldl_map to `foldl op' e (join)`), then if it's a foldl over a Map.join, rewrites
   to the per-key nested foldl that NEVER materializes the |xs|·|ys| pairs:
     foldl op e (join kf lf xs ys) = foldl (λacc x. foldl (λacc' y. op acc' (x,y)) acc (bucket x)) e xs
   Adopt iff it strictly lowers cost/pipeline-cost (the LHS pays the join product, the RHS ~0) AND the
   composed (fuse ∘ factor) proof certifies. Soundness rests on `cert/verified-rewrite?`."
  [^Env env term & {:keys [lctx selectivity sizes]}]
  (when (cost/mentions-const? term "Map.join")          ; cheap guard — skip the internal fuse otherwise
   (let [fused  (cert/optimize env term :lctx lctx)
         fterm  (if (:verified? fused) (:term fused) term)
         fproof (when (:verified? fused) (:proof fused))]
    (when-let [{:keys [S op e jargs]} (fold-join fterm)]
      (let [[K X Y dec kf lf xs ys] jargs
            factor-pf (e/app* (e/const' (name/from-string "Map.foldl_join_factor") [])
                              K X Y S dec op e kf lf xs ys)
            st (cert/mk-st env lctx)
            ptype (try (tc/infer-type st factor-pf) (catch Throwable _ nil))   ; nil if law absent
            [_ eqargs] (when ptype (e/get-app-fn-args ptype))]                 ; @Eq S LHS RHS
        (when (and eqargs (>= (count eqargs) 3))
          (let [rhs (nth eqargs 2)
                proof (compose-trans env lctx term fterm rhs fproof factor-pf)
                res {:term rhs :proof proof :changed? true :rw :fold-factor}]
            (when (and (< (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                          (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                       (cert/verified-rewrite? env term res :lctx lctx))
              (assoc res :verified? true)))))))))


(defn compose-trans
  "Eq.trans of `p1` (a=b) and `p2` (b=c) → a proof of a=c. nil proofs are identities
   (a=a), so `(compose-trans … a a c nil p2) = p2` and `(… a b b p1 nil) = p1`. Builds
   `@Eq.trans.{u} T a b c p1 p2` with T = type of `a`, u its sort level."
  [^Env env lctx a b c p1 p2]
  (cond
    (nil? p1) p2
    (nil? p2) p1
    :else (let [st (cert/mk-st env lctx)
                t (tc/infer-type st a)
                t-sort (#'tc/cached-whnf st (tc/infer-type st t))
                u (if (e/sort? t-sort) (e/sort-level t-sort) lvl/zero)]
            (e/app* (e/const' (name/from-string "Eq.trans") [u]) t a b c p1 p2))))


(defn try-fold-factor*
  "RECURSIVE FAQ variable elimination: iterate `try-fold-factor` to a fixpoint, eliminating EVERY join in
   a multi-way join tree, not just the outermost. After the outer join factors, the result is again a
   `foldl op e (… Map.join inner …)` whose inner join factors by the SAME proven law — so iterating the
   single step performs full variable elimination (O(N^k) → O(N)). Composes the per-step Eq.trans proofs
   into ONE certified rewrite (orig ≡ fully-factored); each step is independently `verified?`, so the
   chain is certified by transitivity. Returns the composed rewrite (`:rw :fold-factor`), or nil if no
   step fired. The single-join case is exactly one iteration, so this is a drop-in for `try-fold-factor`."
  [^Env env term & {:keys [lctx selectivity sizes max-depth] :or {max-depth 8}}]
  (loop [t term proof nil d 0]
    (let [step (when (and (< d (long max-depth)) (cost/mentions-const? t "Map.join"))
                 (try-fold-factor env t :lctx lctx :selectivity selectivity :sizes sizes))]
      (if (and step (:verified? step))
        (recur (:term step) (compose-trans env lctx term t (:term step) proof (:proof step)) (inc d))
        (when (pos? d)
          {:term t :proof proof :changed? true :rw :fold-factor :verified? true})))))


(defn try-grace-hash
  "PHYSICAL grace-hash spill: when the join's build-side index would EXCEED the memory budget,
   evaluate `foldl op e (Map.join xs ys)` in budget-sized BLOCKS of the build side (O(block) peak
   memory). Rewrites to `foldl (λacc blk. foldl op acc (join xs blk)) e (List.chunk B ys)` and
   certifies it by composing  congrArg (List.flatten_chunk B ys).symm  with  Map.foldl_join_blockfold
   — exactly the chain proven in wandler.grace-hash-test. The left-commutativity hypothesis is built
   as `rfl` (sound for COUNT and any p-independent aggregate; the kernel rejects it for non-lcomm ops,
   so cert/verified-rewrite? gates correctness). Fires only when an explicit `memory-budget` is set AND the
   index estimate exceeds it. B (block size) is a heuristic from the budget; correctness is independent
   of B, only the peak-memory guarantee depends on it."
  [^Env env term & {:keys [lctx selectivity sizes memory-budget block-size]}]
  (when (and memory-budget (cost/mentions-const? term "Map.join"))
    (let [fused  (cert/optimize env term :lctx lctx)
          fterm  (if (:verified? fused) (:term fused) term)
          fproof (when (:verified? fused) (:proof fused))]
      (when-let [{:keys [S op e jargs]} (fold-join fterm)]
        (let [[K X Y dec kf lf xs ys] jargs
              idx-mem (:memory (cost/pipeline-resources term {:selectivity selectivity :sizes sizes}))]
          (when (> (double idx-mem) (double memory-budget))
            (let [nm   (fn [s] (name/from-string s))
                  z    lvl/zero  L1 (lvl/succ z)
                  PXY  (e/app* (e/const' (nm "Prod") [z z]) X Y)
                  listY (e/app (e/const' (nm "List") [z]) Y)
                  B    (e/lit-nat (long (max 1 (or block-size (long (/ (double memory-budget) 1000.0))))))
                  chunked (e/app* (e/const' (nm "List.chunk") []) Y B ys)
                  flatChunked (e/app* (e/const' (nm "List.flatten") [z]) Y chunked)
                  joinW (fn [w] (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs w))
                  foldlG (fn [l] (e/app* (e/const' (nm "List.foldl") [z z]) S PXY op e l))
                  midL (foldlG (joinW ys)) midR (foldlG (joinW flatChunked))
                  fc    (e/app* (e/const' (nm "List.flatten_chunk") []) Y B ys)
                  fcSym (e/app* (e/const' (nm "Eq.symm") [L1]) listY flatChunked ys fc)
                  motive (e/lam "w" listY (e/app* (e/const' (nm "List.foldl") [z z]) S PXY op e (joinW (e/bvar 0))) :default)
                  congr (e/app* (e/const' (nm "congrArg") [L1 L1]) listY S ys flatChunked motive fcSym)
                  lc   (e/lam "a" S (e/lam "u" PXY (e/lam "v" PXY
                         (e/app* (e/const' (nm "Eq.refl") [L1]) S
                                 (e/app* op (e/app* op (e/bvar 2) (e/bvar 1)) (e/bvar 0))) :default) :default) :default)
                  bf   (e/app* (e/const' (nm "Map.foldl_join_blockfold") []) K X Y dec kf lf S op lc e xs chunked)
                  st   (cert/mk-st env lctx)
                  bftype (try (tc/infer-type st bf) (catch Throwable _ nil))   ; @Eq S midR rhs (nil if law absent)
                  [_ bfargs] (when bftype (e/get-app-fn-args bftype))]
              (when (and bfargs (>= (count bfargs) 3))
                (let [rhs    (nth bfargs 2)
                      result-pf (e/app* (e/const' (nm "Eq.trans") [L1]) S midL midR rhs congr bf)
                      proof  (compose-trans env lctx term fterm rhs fproof result-pf)
                      res {:term rhs :proof proof :changed? true :rewrites [:grace-hash]
                           :physical {:strategy :grace-hash :index-est idx-mem :budget memory-budget}
                           :cost (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})}]
                  (when (cert/verified-rewrite? env term res :lctx lctx)
                    (assoc res :verified? true)))))))))))


(defn- separable-sum-g
  "Detect a SEPARABLE additive aggregate op: `λacc:Nat. λp:(X×Y). Nat.add acc (g (Prod.snd X Y p))`
   where `g : Y → Nat` reads only the right (build) side. Returns g (a CLOSED Y→Nat term, i.e. no
   dependence on acc/p) or nil. This is the exact op shape `Map.foldl_join_sum_factor` is stated for,
   so a match means the law's LHS is def-eq to the term and the pre-aggregated index applies."
  [op]
  (when (e/lam? op)
    (let [b1 (e/lam-body op)]
      (when (e/lam? b1)
        (let [body (e/lam-body b1)
              [h args] (e/get-app-fn-args body)]
          (when (and (e/const? h) (= "Nat.add" (name/->string (e/const-name h))) (= 2 (count args))
                     (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                     (e/app? (second args)))
            (let [a2 (second args) G (e/app-fn a2) sndt (e/app-arg a2)
                  [sh sargs] (e/get-app-fn-args sndt)]
              (when (and (e/const? sh) (= "Prod.snd" (name/->string (e/const-name sh)))
                         (= 3 (count sargs)) (e/bvar? (nth sargs 2)) (= 0 (e/bvar-idx (nth sargs 2)))
                         (not (e/has-loose-bvars? G)))
                G))))))))


(defn try-pre-agg-index
  "PHYSICAL pre-aggregated (FAQ) index for a SEPARABLE SUM aggregate over a join — the O(distinct-keys)
   in-memory strategy. When `foldl (λacc p. acc + g (snd p)) e (Map.join … xs ys)` (sum of a right-side
   field), rewrite via `Map.foldl_join_sum_factor` to `foldl (λacc x. acc + getD (lookup (kf x) PREIDX)
   0) e xs`, where PREIDX = the group-by index with each bucket PRE-SUMMED once — held memory O(distinct
   keys), not O(|ys|). Certified by composing fusion ∘ the sum-factor law (proven in proofs.clj §6 from
   foldl_join_factor + foldl_congr + foldl_add_init + lookup_map_kv + getD_map). The `:ndv` oracle
   (HyperLogLog / datahike schema / stratum estimate, à la DuckDB `cardinality_estimator.cpp`) gives the
   held-index estimate (≤ |ys|); soundness of the SMALL estimate rests on the index actually being
   pre-summed (which the law proves). Soundness of the rewrite rests on `cert/verified-rewrite?`."
  [^Env env term & {:keys [lctx selectivity sizes memory-budget ndv]}]
  (when (cost/mentions-const? term "Map.join")
    (let [fused  (cert/optimize env term :lctx lctx)
          fterm  (if (:verified? fused) (:term fused) term)
          fproof (when (:verified? fused) (:proof fused))]
      (when-let [{:keys [S op e jargs]} (fold-join fterm)]
        (when (and (e/const? S) (= "Nat" (name/->string (e/const-name S))))
          (when-let [g (separable-sum-g op)]
            (let [[K X Y dec kf lf xs ys] jargs
                  ;; PRE-AGG is an ndv-DRIVEN choice (DuckDB PerfectHashAggregate gating): adopt only
                  ;; when the oracle gives a build-side distinct-count STRICTLY below the raw build size,
                  ;; i.e. a real held-memory win (O(distinct keys) ≪ O(|ys|)). Without ndv, the default
                  ;; fold-factor (+ hoist) plan stands — pre-agg's win isn't visible to the static model.
                  build-mem (:memory (cost/pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                  ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
              (when (and ndv-est (< (double ndv-est) (double build-mem)))
                (let [law (e/app* (e/const' (name/from-string "Map.foldl_join_sum_factor") [])
                                  K X Y dec g kf lf e xs ys)
                      st (cert/mk-st env lctx)
                      ptype (try (tc/infer-type st law) (catch Throwable _ nil))   ; nil if law absent
                      [_ eqargs] (when ptype (e/get-app-fn-args ptype))]           ; @Eq Nat LHS RHS
                  (when (and eqargs (>= (count eqargs) 3))
                    (let [rhs (nth eqargs 2)
                          proof (compose-trans env lctx term fterm rhs fproof law)
                          res {:term rhs :proof proof :changed? true :rewrites [:pre-agg-index]
                               :physical {:strategy :in-memory-hash :index-est (double ndv-est) :budget (or memory-budget 1.0e8)}
                               :cost (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})}]
                      (when (and (< (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                                    (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                                 (cert/verified-rewrite? env term res :lctx lctx))
                        (assoc res :verified? true)))))))))))))


;; ---- physical: loop-invariant index hoisting (LICM), memory-gated ----------------
(defn- collect-closed-group-bys
  "Distinct CLOSED (no loose bvars ⇒ loop-invariant) `Map.group_by` subterms that occur UNDER a
   binder — the index builds a factorized join recomputes per row. (Under-binder only, so an already
   hoisted top-level index isn't re-collected.)"
  [term]
  (let [acc (atom [])]
    (letfn [(go [t under?]
              (let [[h _] (e/get-app-fn-args t)
                    hn (when (e/const? h) (name/->string (e/const-name h)))]
                (when (and under? (= hn "Map.group_by") (not (e/has-loose-bvars? t))
                           (not (some #(.equals ^Object % t) @acc)))
                  (swap! acc conj t))
                (cond (e/app? t)    (do (go (e/app-fn t) under?) (go (e/app-arg t) under?))
                      (e/lam? t)    (do (go (e/lam-type t) under?) (go (e/lam-body t) true))
                      (e/forall? t) (do (go (e/forall-type t) under?) (go (e/forall-body t) true)))))]
      (go term false))
    @acc))


(defn- replace-closed
  "Replace every occurrence of the CLOSED subterm `s` with `F` (also closed) in `t`."
  [t s F]
  (cond (.equals ^Object t s) F
        (e/app? t)    (e/app (replace-closed (e/app-fn t) s F) (replace-closed (e/app-arg t) s F))
        (e/lam? t)    (e/lam (e/lam-name t) (replace-closed (e/lam-type t) s F)
                             (replace-closed (e/lam-body t) s F) (e/lam-info t))
        (e/forall? t) (e/forall' (e/forall-name t) (replace-closed (e/forall-type t) s F)
                                 (replace-closed (e/forall-body t) s F) (e/forall-info t))
        :else t))


(defn hoist-invariant-indices
  "LICM (the in-memory-hash physical strategy): lift loop-invariant index builds — closed
   `Map.group_by` subterms inside a fold — into β-redexes ABOVE the fold, so each index is built
   ONCE instead of re-bucketed per row (O(N) instead of O(N²)). The result is BETA-EQUIVALENT to
   `term`, so an existing `orig ≡ term` certificate still holds (def-eq absorbs the β-step). The
   caller MEMORY-GATES this (hoist iff the held index fits the budget). See docs/PHYSICAL_PLANNING.md."
  [^Env env lctx term]
  (let [st (cert/mk-st env lctx)
        ;; only SATURATED group_bys (type = a Map value, not a function) — a partial `Map.group_by f`
        ;; used as a higher-order fn is not a built index and would codegen under-applied.
        gbs (->> (collect-closed-group-bys term)
                 (keep (fn [s] (let [T (try (tc/infer-type st s) (catch Throwable _ nil))]
                                 (when (and T (not (e/forall? (#'tc/cached-whnf st T)))) [s T])))))
        tagged (map-indexed (fn [i [s T]] [s (+ 990000 i) T]) gbs)]
    (if (empty? tagged)
      term
      (let [term' (reduce (fn [t [s F _]] (replace-closed t s (e/fvar F))) term tagged)]
        (reduce (fn [body [s F T]] (e/app (e/lam "idx" T (e/abstract1 body F) :default) s))
                term' tagged)))))


(def rewrite-descriptions
  {:fold-factor  "aggregation pushed THROUGH the join (the |L|·|R| product is never materialized)"
   :count-factor "count pushed through the join"
   :join-reorder "join REORDERED to index the smaller side"
   :hoist-index  "in-memory HASH join — index built once, hoisted out of the row loop"
   :nested-loop  "NESTED-LOOP join — per-row filter, no held index"
   :grace-hash   "GRACE-HASH spill — build side processed in budget-sized blocks (List.chunk)"
   :pre-agg-index "PRE-AGGREGATED index — each join bucket pre-summed once (held memory O(distinct keys))"
   :egraph       "e-graph equality saturation"})
