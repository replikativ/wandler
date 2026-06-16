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


(defn- separable-frame-fg
  "Detect a SEPARABLE two-sided product aggregate op (the FAQ frame shape):
     λacc:Nat. λp:(X×Y). Nat.add acc (Nat.mul (f (Prod.fst X Y p)) (g (Prod.snd X Y p)))
   where f:X→Nat reads only the LEFT (probe) side and g:Y→Nat only the RIGHT (build) side. Returns
   [f g] (both CLOSED Nat-valued terms, i.e. no dependence on acc/p) or nil. This is the exact op shape
   `Map.foldl_join_frame` is stated for — a match means the law's LHS is def-eq to the term and the
   pre-aggregated index applies to the separable y-side weight g, with the x-side weight f factored out."
  [op]
  (when (e/lam? op)
    (let [b1 (e/lam-body op)]
      (when (e/lam? b1)
        (let [body (e/lam-body b1)
              [h args] (e/get-app-fn-args body)]
          (when (and (e/const? h) (= "Nat.add" (name/->string (e/const-name h))) (= 2 (count args))
                     (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                     (e/app? (second args)))
            (let [mult (second args)
                  [mh margs] (e/get-app-fn-args mult)]
              (when (and (e/const? mh) (= "Nat.mul" (name/->string (e/const-name mh))) (= 2 (count margs))
                         (e/app? (nth margs 0)) (e/app? (nth margs 1)))
                (let [fa (nth margs 0) ga (nth margs 1)
                      f (e/app-fn fa) g (e/app-fn ga)
                      [fh fargs] (e/get-app-fn-args (e/app-arg fa))
                      [gh gargs] (e/get-app-fn-args (e/app-arg ga))]
                  (when (and (e/const? fh) (= "Prod.fst" (name/->string (e/const-name fh)))
                             (= 3 (count fargs)) (e/bvar? (nth fargs 2)) (= 0 (e/bvar-idx (nth fargs 2)))
                             (e/const? gh) (= "Prod.snd" (name/->string (e/const-name gh)))
                             (= 3 (count gargs)) (e/bvar? (nth gargs 2)) (= 0 (e/bvar-idx (nth gargs 2)))
                             (not (e/has-loose-bvars? f)) (not (e/has-loose-bvars? g)))
                    [f g]))))))))))


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


(defn try-frame-index
  "PHYSICAL FAQ FRAME RULE for a SEPARABLE two-sided weight over a join — the O(distinct-keys) in-memory
   strategy GENERALIZED to a left-side weight. When `foldl (λacc p. acc + f(fst p)·g(snd p)) e
   (Map.join … xs ys)` (a product of a probe-side field f and a build-side field g), rewrite via
   `Map.foldl_join_frame` to `foldl (λacc x. acc + f(x)·getD (lookup (kf x) PREIDX) 0) e xs`, where
   PREIDX is the SAME g-only group-by index with each bucket PRE-SUMMED once — held memory O(distinct
   keys), not O(|ys|), and the per-x weight f(x) applied AFTER the lookup. The f≡1 case is exactly
   `try-pre-agg-index` (the two matchers are disjoint: this one requires the explicit Nat.mul). Same
   ndv gating (DuckDB PerfectHashAggregate) and certification (`cert/verified-rewrite?`) as the
   sum-factor index. Without ndv, the op-generic `try-fold-factor*` still removes the product; the frame
   index adds the pre-summed held-memory win when ndv ≪ |ys|."
  [^Env env term & {:keys [lctx selectivity sizes memory-budget ndv]}]
  (when (cost/mentions-const? term "Map.join")
    (let [fused  (cert/optimize env term :lctx lctx)
          fterm  (if (:verified? fused) (:term fused) term)
          fproof (when (:verified? fused) (:proof fused))]
      (when-let [{:keys [S op e jargs]} (fold-join fterm)]
        (when (and (e/const? S) (= "Nat" (name/->string (e/const-name S))))
          (when-let [[f g] (separable-frame-fg op)]
            (let [[K X Y dec kf lf xs ys] jargs
                  build-mem (:memory (cost/pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                  ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
              (when (and ndv-est (< (double ndv-est) (double build-mem)))
                (let [law (e/app* (e/const' (name/from-string "Map.foldl_join_frame") [])
                                  K X Y dec f g kf lf e xs ys)
                      st (cert/mk-st env lctx)
                      ptype (try (tc/infer-type st law) (catch Throwable _ nil))   ; nil if law absent
                      [_ eqargs] (when ptype (e/get-app-fn-args ptype))]           ; @Eq Nat LHS RHS
                  (when (and eqargs (>= (count eqargs) 3))
                    (let [rhs (nth eqargs 2)
                          proof (compose-trans env lctx term fterm rhs fproof law)
                          res {:term rhs :proof proof :changed? true :rewrites [:frame-index]
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


;; ---- loop-invariant distributive hoist (1-variable elimination) ----------------
;; foldl(+) 0 (map (λx. f x * c) xs)  →  (foldl(+) 0 (map f xs)) * c   when c is x-free.
;; Certified by `List.sum_map_mul_const`. This is the base case of FAQ variable elimination:
;; a multiplicative factor independent of the fold variable distributes OUT of the sum, so an
;; expensive invariant `c` (e.g. a nested fold over another stream) is computed ONCE rather than
;; per element — the measured O(|xs|·cost c) → O(|xs| + cost c) hoist.

(defn- cn? [e s] (and (e/const? e) (= s (name/->string (e/const-name e)))))

(defn- nat-zero?
  "True for every spelling of the Nat additive identity 0: the raw `Nat.zero` constructor, a bare
   `lit-nat 0` (what `reduce + 0` elaborates to), and `@OfNat.ofNat Nat 0 _` — all def-eq but
   syntactically distinct (the #73 boundary-normalization issue). The matcher is syntactic, so it
   accepts any of them; a false positive cannot pass the `verified-rewrite?` kernel gate, so loose
   recognition here is sound. Checks the literal value directly (no `->string`)."
  [e]
  (or (cn? e "Nat.zero")
      (and (e/lit-nat? e) (zero? (long (e/lit-nat-val e))))
      (let [[h args] (e/get-app-fn-args e)]
        (and (e/const? h) (= "OfNat.ofNat" (name/->string (e/const-name h))) (>= (count args) 2)
             (nat-zero? (nth args 1))))))

;; ---- CONDITIONAL SEPARATION: a separable guard over the join (Phase 4b) ---------
(defn- guarded-proj
  "If `t` is `(h (Prod.PROJ X Y (bvar 0)))` with `h` CLOSED and PROJ matching `proj-name`, return h;
   else nil. The closed `h` reads ONLY one side of the pair through the projection."
  [t proj-name]
  (when (e/app? t)
    (let [h (e/app-fn t)
          [ph pargs] (e/get-app-fn-args (e/app-arg t))]
      (when (and (e/const? ph) (= proj-name (name/->string (e/const-name ph)))
                 (= 3 (count pargs)) (e/bvar? (nth pargs 2)) (= 0 (e/bvar-idx (nth pargs 2)))
                 (not (e/has-loose-bvars? h)))
        h))))

(defn- separable-guarded-fpg
  "Detect a CONDITIONALLY-separable two-sided aggregate op (FAQ frame with a separable guard):
     λacc:Nat. λp:(X×Y). Nat.add acc (cond (P (fst p) && Q (snd p)) (f (fst p) · g (snd p)) 0)
   with P:X→Bool, Q:Y→Bool, f:X→Nat, g:Y→Nat all CLOSED. Returns {:P :Q :f :g} or nil. By
   Nat.cond_and_mul_split this op is POINTWISE-equal to the product op with f'=[P]·f, g'=[Q]·g — so
   the frame rule applies once the guard is split."
  [op]
  (when (e/lam? op)
    (let [b1 (e/lam-body op)]
      (when (e/lam? b1)
        (let [body (e/lam-body b1)
              [h args] (e/get-app-fn-args body)]
          (when (and (e/const? h) (= "Nat.add" (name/->string (e/const-name h))) (= 2 (count args))
                     (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                     (e/app? (second args)))
            (let [[ch cargs] (e/get-app-fn-args (second args))]
              (when (and (e/const? ch) (= "cond" (name/->string (e/const-name ch))) (= 4 (count cargs))
                         (e/app? (nth cargs 1)) (e/app? (nth cargs 2)) (nat-zero? (nth cargs 3)))
                (let [[gh gargs] (e/get-app-fn-args (nth cargs 1))    ; guard = Bool.and (P fst) (Q snd)
                      [mh margs] (e/get-app-fn-args (nth cargs 2))]   ; weight = Nat.mul (f fst) (g snd)
                  (when (and (e/const? gh) (= "Bool.and" (name/->string (e/const-name gh))) (= 2 (count gargs))
                             (e/const? mh) (= "Nat.mul" (name/->string (e/const-name mh))) (= 2 (count margs)))
                    (let [P (guarded-proj (nth gargs 0) "Prod.fst")
                          Q (guarded-proj (nth gargs 1) "Prod.snd")
                          f (guarded-proj (nth margs 0) "Prod.fst")
                          g (guarded-proj (nth margs 1) "Prod.snd")]
                      (when (and P Q f g) {:P P :Q Q :f f :g g}))))))))))))

(defn try-frame-index-cond
  "PHYSICAL conditional FAQ frame: a SEPARABLE GUARD `P(x) ∧ Q(y)` over a weighted join factorizes
   through the pre-aggregated index. When `foldl (λacc p. acc + cond (P(fst p) && Q(snd p)) (f(fst p) ·
   g(snd p)) 0) e (Map.join … xs ys)`, first split the guard via `Nat.cond_and_mul_split` (proven) to the
   product op with f'=[P]·f, g'=[Q]·g (a `List.foldl_congr` step), then apply `Map.foldl_join_frame` —
   composing the two into one certified rewrite. The probe side keeps its guard f', the build side
   pre-sums g' once. Same ndv gate / certification as `try-frame-index`."
  [^Env env term & {:keys [lctx selectivity sizes memory-budget ndv]}]
  (when (cost/mentions-const? term "Map.join")
    (let [fused  (cert/optimize env term :lctx lctx)
          fterm  (if (:verified? fused) (:term fused) term)
          fproof (when (:verified? fused) (:proof fused))]
      (when-let [{:keys [S op e jargs]} (fold-join fterm)]
        (when (and (e/const? S) (= "Nat" (name/->string (e/const-name S))))
          (when-let [{:keys [P Q f g]} (separable-guarded-fpg op)]
            (let [[K X Y dec kf lf xs ys] jargs
                  build-mem (:memory (cost/pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                  ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
              (when (and ndv-est (< (double ndv-est) (double build-mem)))
                (let [nm   (fn [s] (name/from-string s))
                      z    lvl/zero  L1 (lvl/succ z)
                      natT (e/const' (nm "Nat") []) zeroN (e/const' (nm "Nat.zero") [])
                      PXY  (e/app* (e/const' (nm "Prod") [z z]) X Y)
                      condN (fn [c x y] (e/app* (e/const' (nm "cond") [L1]) natT c x y))
                      fstp (fn [p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
                      sndp (fn [p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
                      addN (fn [x y] (e/app* (e/const' (nm "Nat.add") []) x y))
                      mulN (fn [x y] (e/app* (e/const' (nm "Nat.mul") []) x y))
                      andB (fn [x y] (e/app* (e/const' (nm "Bool.and") []) x y))
                      f'  (e/lam "x" X (condN (e/app P (e/bvar 0)) (e/app f (e/bvar 0)) zeroN) :default)
                      g'  (e/lam "y" Y (condN (e/app Q (e/bvar 0)) (e/app g (e/bvar 0)) zeroN) :default)
                      op-s (e/lam "acc" natT (e/lam "p" PXY
                             (addN (e/bvar 1) (mulN (e/app f' (fstp (e/bvar 0))) (e/app g' (sndp (e/bvar 0))))) :default) :default)
                      X1 (fn [p] (condN (andB (e/app P (fstp p)) (e/app Q (sndp p))) (mulN (e/app f (fstp p)) (e/app g (sndp p))) zeroN))
                      X2 (fn [p] (mulN (condN (e/app P (fstp p)) (e/app f (fstp p)) zeroN) (condN (e/app Q (sndp p)) (e/app g (sndp p)) zeroN)))
                      splitPf (fn [p] (e/app* (e/const' (nm "Nat.cond_and_mul_split") [])
                                              (e/app P (fstp p)) (e/app Q (sndp p)) (e/app f (fstp p)) (e/app g (sndp p))))
                      hyp (e/lam "acc" natT (e/lam "p" PXY
                            (e/app* (e/const' (nm "congrArg") [L1 L1]) natT natT (X1 (e/bvar 0)) (X2 (e/bvar 0))
                                    (e/lam "w" natT (addN (e/bvar 2) (e/bvar 0)) :default)
                                    (splitPf (e/bvar 0))) :default) :default)
                      join (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys)
                      foldlJ (fn [o] (e/app* (e/const' (nm "List.foldl") [z z]) natT PXY o e join))
                      congrEq (e/app* (e/const' (nm "List.foldl_congr") []) natT PXY op op-s join e hyp)
                      frameEq (e/app* (e/const' (nm "Map.foldl_join_frame") []) K X Y dec f' g' kf lf e xs ys)
                      st (cert/mk-st env lctx)
                      ftype (try (tc/infer-type st frameEq) (catch Throwable _ nil))   ; nil if law absent
                      [_ eqargs] (when ftype (e/get-app-fn-args ftype))]
                  (when (and eqargs (>= (count eqargs) 3))
                    (let [rhs (nth eqargs 2)
                          rwPf (e/app* (e/const' (nm "Eq.trans") [L1]) natT (foldlJ op) (foldlJ op-s) rhs congrEq frameEq)
                          proof (compose-trans env lctx term fterm rhs fproof rwPf)
                          res {:term rhs :proof proof :changed? true :rewrites [:frame-index-cond]
                               :physical {:strategy :in-memory-hash :index-est (double ndv-est) :budget (or memory-budget 1.0e8)}
                               :cost (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})}]
                      (when (and (< (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                                    (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                                 (cert/verified-rewrite? env term res :lctx lctx))
                        (assoc res :verified? true)))))))))))))

(def ^:private soac-heads
  "Heads whose presence in an invariant `c` makes hoisting it out of a row-loop worthwhile (the cost
   that matters is a per-row recompute of a collection traversal). A heuristic worth-it gate, NOT a
   soundness gate — false accepts cost a wasted verify, false negatives a missed micro-opt."
  #{"List.foldl" "List.foldr" "List.map" "List.filter" "List.flatMap" "List.filterMap"
    "List.foldlIdx" "List.length" "List.range" "Map.join" "Map.group_by"})

(defn- expr-children [e]
  (case (e/tag e)
    :app    [(e/app-fn e) (e/app-arg e)]
    :lam    [(e/lam-type e) (e/lam-body e)]
    :forall [(e/forall-type e) (e/forall-body e)]
    :let    [(e/let-type e) (e/let-value e) (e/let-body e)]
    :mdata  [(e/mdata-expr e)]
    :proj   [(e/proj-struct e)]
    []))

(defn- any-node? [e pred]
  (or (pred e) (boolean (some #(any-node? % pred) (expr-children e)))))

(defn- contains-soac? [e] (any-node? e #(and (e/const? %) (soac-heads (name/->string (e/const-name %))))))
(defn- contains-fvar? [e id] (any-node? e #(and (e/fvar? %) (= (long id) (e/fvar-id %)))))

(defn- fresh-fvar-id
  "An fvar id guaranteed not to occur in `term` — `max(occurring) + 1`, floored well above every id
   family in use (lctx params, LICM 990000+i, e-graph 9e8+depth). Avoids the C1 magic-constant
   collision: a hardcoded id sharing the LICM family could silently break the open-binder trick."
  [term]
  (let [mx (atom 2000000000)]
    (any-node? term (fn [x] (when (e/fvar? x) (swap! mx max (e/fvar-id x))) false))
    (inc (long @mx))))

(defn- match-sum-map-mul
  "term = foldl Nat Nat Nat.add 0 (map Nat Nat (λx. Nat.mul A B) xs) where exactly ONE of A,B is free
   of the map binder (the loop-invariant factor c) and the other depends on it (the per-row factor,
   becomes f). Handles BOTH multiplication orders. Returns {:f (λx.·) :c · :xs xs :side :right|:left}
   (`:right` = f x * c, `:left` = c * f x) or nil. Opens the binder with a fresh fvar so instantiate1
   handles all de Bruijn shifting."
  [term]
  (let [[h args] (e/get-app-fn-args term)]
    (when (and (cn? h "List.foldl") (= 5 (count args))
               (cn? (nth args 0) "Nat") (cn? (nth args 1) "Nat")
               (cn? (nth args 2) "Nat.add") (nat-zero? (nth args 3)))
      (let [[mh margs] (e/get-app-fn-args (nth args 4))]
        (when (and (cn? mh "List.map") (= 4 (count margs))
                   (cn? (nth margs 0) "Nat") (cn? (nth margs 1) "Nat") (e/lam? (nth margs 2)))
          (let [step (nth margs 2) xs (nth margs 3)
                K (fresh-fvar-id term)
                body ((requiring-resolve 'ansatz.kernel.expr/instantiate1) (e/lam-body step) (e/fvar K))
                [bh bargs] (e/get-app-fn-args body)
                lam-of (fn [P] (e/lam "x" (e/const' (name/from-string "Nat") []) (e/abstract1 P K) :default))]
            (when (and (cn? bh "Nat.mul") (= 2 (count bargs)))
              (let [A (nth bargs 0) B (nth bargs 1)
                    A? (contains-fvar? A K) B? (contains-fvar? B K)]
                (cond
                  (and A? (not B?)) {:f (lam-of A) :c B :xs xs :side :right}   ; f x * c
                  (and B? (not A?)) {:f (lam-of B) :c A :xs xs :side :left}    ; c * f x
                  :else nil)))))))))      ; both dependent (no invariant) or both invariant (degenerate)

(defn try-hoist-invariant
  "Cost-driven LOOP-INVARIANT HOIST (1-variable FAQ elimination). If `term` =
   foldl(+) 0 (map (λx. f x * c) xs) (or the mirror `c * f x`) with `c` x-free AND loop-shaped
   (contains a SOAC, so the per-row recompute is the cost that matters), rewrite the invariant OUT
   of the row loop so it is evaluated ONCE. Certified by `List.sum_map_mul_const` (right) /
   `List.sum_map_const_mul` (left); adopt iff it strict-certifies. The worth-it gate is LOCAL
   (c contains a SOAC) rather than the global cost model, which keeps SOAC step-λs uncounted (the
   factorization gates depend on that). Returns {:term :proof :verified? :changed? :rw} or nil."
  [^Env env term & {:keys [lctx selectivity sizes] :as _opts}]
  (when-let [{:keys [f c xs side]} (match-sum-map-mul term)]
    (when (contains-soac? c)
      (let [natC (e/const' (name/from-string "Nat") [])
            mul  (fn [a b] (e/app* (e/const' (name/from-string "Nat.mul") []) a b))
            add0 (fn [l] (e/app* (e/const' (name/from-string "List.foldl") [lvl/zero lvl/zero]) natC natC
                                 (e/const' (name/from-string "Nat.add") []) (e/const' (name/from-string "Nat.zero") []) l))
            sumf (add0 (e/app* (e/const' (name/from-string "List.map") [lvl/zero lvl/zero]) natC natC f xs))
            [law rhs] (if (= side :left)
                        ["List.sum_map_const_mul" (mul c sumf)]    ; c * (∑ f)
                        ["List.sum_map_mul_const" (mul sumf c)])   ; (∑ f) * c
            cert (e/app* (e/const' (name/from-string law) []) f c xs)
            res  {:term rhs :proof cert :changed? true :rw :hoist-invariant}]
        (when (cert/verified-rewrite? env term res :lctx lctx)
          (assoc res :verified? true))))))


(def rewrite-descriptions
  {:fold-factor  "aggregation pushed THROUGH the join (the |L|·|R| product is never materialized)"
   :hoist-invariant "loop-INVARIANT factor hoisted OUT of the sum (computed once, not per row)"
   :count-factor "count pushed through the join"
   :join-reorder "join REORDERED to index the smaller side"
   :hoist-index  "in-memory HASH join — index built once, hoisted out of the row loop"
   :nested-loop  "NESTED-LOOP join — per-row filter, no held index"
   :grace-hash   "GRACE-HASH spill — build side processed in budget-sized blocks (List.chunk)"
   :pre-agg-index "PRE-AGGREGATED index — each join bucket pre-summed once (held memory O(distinct keys))"
   :egraph       "e-graph equality saturation"})
