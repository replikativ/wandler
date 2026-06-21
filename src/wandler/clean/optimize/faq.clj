;; Split from the wandler.optimize monolith (cohesion audit item 5): PHYSICAL STRATEGIES —
;; the dedicated cost-chosen plan drivers (join reorder, count/fold factorization,
;; grace-hash spill, pre-aggregated FAQ index, invariant-index hoisting). Every adoption
;; is gated by cert/verified-rewrite?.
(ns wandler.clean.optimize.faq
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.codegen :as cg]
            [wandler.clean.optimize.certify :as cert]
            [wandler.clean.optimize.cost :as cost]
            [wandler.clean.optimize.filter-elim :as fe]
            [wandler.laws.semiring :as sreg]
            [wandler.semiring-class :as sc])
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


;; ── semiring instance registry (the last mile: route the carrier-generic laws by carrier) ───────────
;; carrier const-name → its ops + the axiom-PROOF const-names the generic frame-family laws require. A
;; recognizer reads the carrier S off the fold op's binder type and looks the entry up here; the emitter
;; instantiates the `_generic` law with the entry's ops + proofs (instead of the Nat-specific alias). Add
;; a row — with that carrier's Init-proven distributive/annihilator/monoid lemmas — and its queries
;; factorize through the pre-aggregated index end-to-end. Nat = counting/SUM; Bool = boolean provenance /
;; reachability (∨ = ∃, ∧ = ∧). Soundness still rests entirely on `cert/verified-rewrite?` (check-constant);
;; a bad registry row cannot pass the kernel gate.
;; The semiring carrier registry lives in wandler.laws.semiring (each carrier registers its row next to
;; where its kernel laws are admitted). `sr-entry`/`sr-c` here are thin aliases used by the recognizers/
;; emitters below.
(defn- sr-entry [S] (sreg/entry S))
(defn- sr-c [entry kw] (sreg/const entry kw))

(defn- adopt-if-improved
  "Shared frame-emitter tail: adopt the rewrite `res` (whose :term is the rewritten RHS) iff it strictly
   lowers pipeline-cost AND passes the kernel gate cert/verified-rewrite?. The single place the cost
   improvement and the soundness check are made jointly — kept here so the frame emitters can't drift."
  [^Env env term res lctx selectivity sizes]
  (when (and (< (cost/pipeline-cost (:term res) {:selectivity selectivity :sizes sizes})
                (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
             (cert/verified-rewrite? env term res :lctx lctx))
    (assoc res :verified? true)))

(defn- separable-sum-g
  "Detect a SEPARABLE additive aggregate op: `λacc:S. λp:(X×Y). add acc (g (Prod.snd X Y p))` over any
   registered semiring carrier S (add = the carrier's additive op), where `g : Y → S` reads only the right
   (build) side. Returns g (a CLOSED Y→S term, no dependence on acc/p) or nil. This is the exact op shape
   `Map.foldl_join_sum_factor[_generic]` is stated for, so a match means the law's LHS is def-eq."
  [op]
  (when (e/lam? op)
    (when-let [entry (sr-entry (e/lam-type op))]
      (let [b1 (e/lam-body op)]
        (when (e/lam? b1)
          (let [body (e/lam-body b1)
                [h args] (e/get-app-fn-args body)]
            (when (and (e/const? h) (= (:add entry) (name/->string (e/const-name h))) (= 2 (count args))
                       (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                       (e/app? (second args)))
              (let [a2 (second args) G (e/app-fn a2) sndt (e/app-arg a2)
                    [sh sargs] (e/get-app-fn-args sndt)]
                (when (and (e/const? sh) (= "Prod.snd" (name/->string (e/const-name sh)))
                           (= 3 (count sargs)) (e/bvar? (nth sargs 2)) (= 0 (e/bvar-idx (nth sargs 2)))
                           (not (e/has-loose-bvars? G)))
                  G)))))))))


(defn- separable-frame-fg
  "Detect a SEPARABLE two-sided product aggregate op (the FAQ frame shape):
     λacc:Nat. λp:(X×Y). Nat.add acc (Nat.mul (f (Prod.fst X Y p)) (g (Prod.snd X Y p)))
   where f:X→Nat reads only the LEFT (probe) side and g:Y→Nat only the RIGHT (build) side. Returns
   [f g] (both CLOSED Nat-valued terms, i.e. no dependence on acc/p) or nil. This is the exact op shape
   `Map.foldl_join_frame` is stated for — a match means the law's LHS is def-eq to the term and the
   pre-aggregated index applies to the separable y-side weight g, with the x-side weight f factored out."
  [op]
  (when (e/lam? op)
    (when-let [entry (sr-entry (e/lam-type op))]
      (let [b1 (e/lam-body op)]
       (when (e/lam? b1)
        (let [body (e/lam-body b1)
              [h args] (e/get-app-fn-args body)]
          (when (and (e/const? h) (= (:add entry) (name/->string (e/const-name h))) (= 2 (count args))
                     (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                     (e/app? (second args)))
            (let [mult (second args)
                  [mh margs] (e/get-app-fn-args mult)]
              (when (and (e/const? mh) (= (:mul entry) (name/->string (e/const-name mh))) (= 2 (count margs))
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
                    [f g])))))))))))


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
        (when-let [entry (sr-entry S)]
          (when-let [g (separable-sum-g op)]
            (let [[K X Y dec kf lf xs ys] jargs
                  ;; PRE-AGG is an ndv-DRIVEN choice (DuckDB PerfectHashAggregate gating): adopt only
                  ;; when the oracle gives a build-side distinct-count STRICTLY below the raw build size,
                  ;; i.e. a real held-memory win (O(distinct keys) ≪ O(|ys|)). Without ndv, the default
                  ;; fold-factor (+ hoist) plan stands — pre-agg's win isn't visible to the static model.
                  build-mem (:memory (cost/pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                  ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
              (when (and ndv-est (< (double ndv-est) (double build-mem)))
                (let [law (e/app* (e/const' (name/from-string "Map.foldl_join_sum_factor_generic") [])
                                  S (sc/mk-addmonoid-instance S entry)
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
                      (adopt-if-improved env term res lctx selectivity sizes))))))))))))


(defn- reads-fst?
  "Does `t` reference the X side of the pair `p` (= `bvar 0`) through a `Prod.fst … p` projection? A
   recursive scan that is robust to how the key is read — a const application `kf (fst p)`, a structure
   projection node `Customer.0 (fst p)`, or any closed function of it. Used to confirm the LEFT factor
   genuinely reads the probe side (not the build side)."
  [t]
  (let [hit (atom false)]
    (letfn [(go [x]
              (when-not @hit
                (let [[h a] (e/get-app-fn-args x)]
                  (when (and (e/const? h) (= "Prod.fst" (name/->string (e/const-name h)))
                             (= 3 (count a)) (e/bvar? (nth a 2)) (= 0 (e/bvar-idx (nth a 2))))
                    (reset! hit true))
                  (when (e/proj? x) (go (e/proj-struct x)))
                  (doseq [c a] (go c))
                  (when (e/app? x) (go (e/app-fn x))))))]
      (go t))
    @hit))

(defn- abstract-read
  "Abstract the build side out of an expression `R` that reads the pair `p` (= bvar 0) ONLY through
   `Prod.<proj> X Y p`: return `λy:Y. R[that projection ↦ y]` (handles a record `proj` node, a const app,
   or any nesting uniformly), or nil if R touches `p` any other way. The surface elaborates a build-side
   field read `(:amount o)` to `Order.1 (Prod.snd p)` — a proj node — so this is what lets a real record
   query reach the frame."
  [R proj-name Y]
  (let [F 889000
        repl (fn repl [t]
               (let [[h a] (e/get-app-fn-args t)]
                 (if (and (e/const? h) (= proj-name (name/->string (e/const-name h)))
                          (= 3 (count a)) (e/bvar? (nth a 2)) (= 0 (e/bvar-idx (nth a 2))))
                   (e/fvar F)
                   (cond
                     (e/proj? t) (e/proj (e/proj-type-name t) (e/proj-idx t) (repl (e/proj-struct t)))
                     (e/app? t)  (e/app (repl (e/app-fn t)) (repl (e/app-arg t)))
                     :else t))))
        R' (repl R)]
    (when-not (e/has-loose-bvars? R')                ; no remaining `p` reference ⇒ cleanly build-side
      (e/lam "y" Y (e/abstract1 R' F) :default))))

(defn- separable-keyfactor-wg
  "Detect a KEY-FACTOR two-sided aggregate op (the FD scope quotient):
     λacc:Nat. λp:(X×Y). Nat.add acc (Nat.mul (w (read-of (Prod.fst p))) (read-of (Prod.snd p)))
   The LEFT factor is `w` applied to a read of the probe side; the RIGHT is any read of the build side
   (record projection or otherwise). Returns [w g] where w = the outer left factor (closed) and
   g = λy. (right factor)[snd p ↦ y] (the build-side fn), or nil. We do NOT match the inner key read
   against the join's kf here (it may be a const app, a `proj` node, or an η-expanded lambda — the #73
   spellings): try-frame-index-keyfactor builds f'=w∘kf and lets `verified-rewrite?` gate soundness — the
   composed frame∘float proof only typechecks when the left read IS def-eq to `kf (fst p)`."
  [op X Y]
  (when (e/lam? op)
    (when-let [entry (sr-entry (e/lam-type op))]
      (let [b1 (e/lam-body op)]
       (when (e/lam? b1)
        (let [body (e/lam-body b1)
              [h args] (e/get-app-fn-args body)]
          (when (and (e/const? h) (= (:add entry) (name/->string (e/const-name h))) (= 2 (count args))
                     (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                     (e/app? (second args)))
            (let [[mh margs] (e/get-app-fn-args (second args))]
              (when (and (e/const? mh) (= (:mul entry) (name/->string (e/const-name mh))) (= 2 (count margs))
                         (e/app? (nth margs 0)))                                  ; left = w applied to a read
                (let [w (e/app-fn (nth margs 0)) kfx (e/app-arg (nth margs 0))   ; w (read-of (fst p))
                      g (abstract-read (nth margs 1) "Prod.snd" Y)]              ; g = λy. (snd-read)[snd p↦y]
                  (when (and (not (e/has-loose-bvars? w)) (some? g)
                             (reads-fst? kfx))                                    ; left factor reads the probe side
                    [w g])))))))))))

(defn- extract-frame-preidx
  "Navigate a frame output `foldl Nat X step e xs` to the index the per-x lookup probes (the pre-aggregated
   PREIDX) — step body = acc + (f' x)·getD (lookup (kf x) PREIDX) 0. Returns PREIDX (closed) or nil."
  [R1]
  (try
    (let [[_ a1] (e/get-app-fn-args R1)
          body (e/lam-body (e/lam-body (nth a1 2)))
          [_ addA] (e/get-app-fn-args body)
          [_ mulA] (e/get-app-fn-args (nth addA 1))
          [_ getdA] (e/get-app-fn-args (nth mulA 1))
          [_ lkA] (e/get-app-fn-args (nth getdA 1))]
      (when (>= (count lkA) 5) (nth lkA 4)))
    (catch Throwable _ nil)))

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
        (when-let [entry (sr-entry S)]
          (when-let [[f g] (separable-frame-fg op)]
            (let [[K X Y dec kf lf xs ys] jargs
                  build-mem (:memory (cost/pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                  ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
              (when (and ndv-est (< (double ndv-est) (double build-mem)))
                (let [law (e/app* (e/const' (name/from-string "Map.foldl_join_frame_generic") [])
                                  S (sc/mk-semiring-instance S entry)
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
                      (adopt-if-improved env term res lctx selectivity sizes))))))))))))


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
    (when-let [entry (sr-entry (e/lam-type op))]
      (let [b1 (e/lam-body op)]
       (when (e/lam? b1)
        (let [body (e/lam-body b1)
              [h args] (e/get-app-fn-args body)]
          (when (and (e/const? h) (= (:add entry) (name/->string (e/const-name h))) (= 2 (count args))
                     (e/bvar? (first args)) (= 1 (e/bvar-idx (first args)))
                     (e/app? (second args)))
            (let [[ch cargs] (e/get-app-fn-args (second args))]
              (when (and (e/const? ch) (= "cond" (name/->string (e/const-name ch))) (= 4 (count cargs))
                         (e/app? (nth cargs 1)) (e/app? (nth cargs 2))
                         (or (nat-zero? (nth cargs 3)) (cn? (nth cargs 3) (:zero entry))))
                (let [[gh gargs] (e/get-app-fn-args (nth cargs 1))    ; guard = Bool.and (P fst) (Q snd)
                      [mh margs] (e/get-app-fn-args (nth cargs 2))]   ; weight = (carrier mul) (f fst) (g snd)
                  (when (and (e/const? gh) (= "Bool.and" (name/->string (e/const-name gh))) (= 2 (count gargs))
                             (e/const? mh) (= (:mul entry) (name/->string (e/const-name mh))) (= 2 (count margs)))
                    (let [P (guarded-proj (nth gargs 0) "Prod.fst")
                          Q (guarded-proj (nth gargs 1) "Prod.snd")
                          f (guarded-proj (nth margs 0) "Prod.fst")
                          g (guarded-proj (nth margs 1) "Prod.snd")]
                      (when (and P Q f g) {:P P :Q Q :f f :g g})))))))))))))

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
        (when-let [entry (sr-entry S)]
          (when-let [{:keys [P Q f g]} (separable-guarded-fpg op)]
            (let [[K X Y dec kf lf xs ys] jargs
                  build-mem (:memory (cost/pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                  ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
              (when (and ndv-est (< (double ndv-est) (double build-mem)))
                (let [nm   (fn [s] (name/from-string s))
                      z    lvl/zero  L1 (lvl/succ z)
                      natT S zeroN (sr-c entry :zero)            ; carrier-generic (natT name kept for diff)
                      PXY  (e/app* (e/const' (nm "Prod") [z z]) X Y)
                      condN (fn [c x y] (e/app* (e/const' (nm "cond") [L1]) natT c x y))
                      fstp (fn [p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
                      sndp (fn [p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
                      addN (fn [x y] (e/app* (sr-c entry :add) x y))
                      mulN (fn [x y] (e/app* (sr-c entry :mul) x y))
                      andB (fn [x y] (e/app* (e/const' (nm "Bool.and") []) x y))
                      f'  (e/lam "x" X (condN (e/app P (e/bvar 0)) (e/app f (e/bvar 0)) zeroN) :default)
                      g'  (e/lam "y" Y (condN (e/app Q (e/bvar 0)) (e/app g (e/bvar 0)) zeroN) :default)
                      op-s (e/lam "acc" natT (e/lam "p" PXY
                             (addN (e/bvar 1) (mulN (e/app f' (fstp (e/bvar 0))) (e/app g' (sndp (e/bvar 0))))) :default) :default)
                      X1 (fn [p] (condN (andB (e/app P (fstp p)) (e/app Q (sndp p))) (mulN (e/app f (fstp p)) (e/app g (sndp p))) zeroN))
                      X2 (fn [p] (mulN (condN (e/app P (fstp p)) (e/app f (fstp p)) zeroN) (condN (e/app Q (sndp p)) (e/app g (sndp p)) zeroN)))
                      splitPf (fn [p] (e/app* (e/const' (nm "Nat.cond_and_mul_split_generic") [])
                                              natT (sc/mk-semiring-instance natT entry)
                                              (e/app P (fstp p)) (e/app Q (sndp p)) (e/app f (fstp p)) (e/app g (sndp p))))
                      hyp (e/lam "acc" natT (e/lam "p" PXY
                            (e/app* (e/const' (nm "congrArg") [L1 L1]) natT natT (X1 (e/bvar 0)) (X2 (e/bvar 0))
                                    (e/lam "w" natT (addN (e/bvar 2) (e/bvar 0)) :default)
                                    (splitPf (e/bvar 0))) :default) :default)
                      join (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys)
                      foldlJ (fn [o] (e/app* (e/const' (nm "List.foldl") [z z]) natT PXY o e join))
                      congrEq (e/app* (e/const' (nm "List.foldl_congr") []) natT PXY op op-s join e hyp)
                      frameEq (e/app* (e/const' (nm "Map.foldl_join_frame_generic") [])
                                      natT (sc/mk-semiring-instance natT entry)
                                      K X Y dec f' g' kf lf e xs ys)
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
                      (adopt-if-improved env term res lctx selectivity sizes))))))))))))

(defn try-frame-index-keyfactor
  "PHYSICAL FD SCOPE QUOTIENT: a KEY-FACTOR weight `w(kf x)·g(y)` over a join FLOATS the key-factor into
   the per-key index. When `foldl (λacc p. acc + w(kf(fst p))·g(snd p)) e (Map.join … xs ys)` (the left
   factor reads the matched key via the join's own kf), run the frame with f'=w∘kf, then compose
   `Map.foldl_keyfactor_float` to reweight each index entry by w of its key — so w is computed once per
   distinct key instead of per matching row. Both moves certified (frame ∘ float), ndv-gated like the
   other frame indices. The dependent-types win: a key-determined factor moves to the cheaper scope."
  [^Env env term & {:keys [lctx selectivity sizes memory-budget ndv]}]
  (when (cost/mentions-const? term "Map.join")
    (let [fused  (cert/optimize env term :lctx lctx)
          fterm  (if (:verified? fused) (:term fused) term)
          fproof (when (:verified? fused) (:proof fused))]
      (when-let [{:keys [S op e jargs]} (fold-join fterm)]
        (when-let [entry (sr-entry S)]
          (let [[K X Y dec kf lf xs ys] jargs]
            (when-let [[w g] (separable-keyfactor-wg op X Y)]
              (let [build-mem (:memory (cost/pipeline-resources fterm {:selectivity selectivity :sizes sizes}))
                    ndv-est (when (and ndv (e/fvar? ys)) (get ndv (e/fvar-id ys)))]
                (when (and ndv-est (< (double ndv-est) (double build-mem)))
                  (let [nm   (fn [s] (name/from-string s))
                        z    lvl/zero  L1 (lvl/succ z)  natT S
                        f'   (e/lam "x" X (e/app w (e/app kf (e/bvar 0))) :default)
                        frameEq (e/app* (e/const' (nm "Map.foldl_join_frame_generic") [])
                                        natT (sc/mk-semiring-instance natT entry)
                                        K X Y dec f' g kf lf e xs ys)
                        st (cert/mk-st env lctx)
                        feT (try (tc/infer-type st frameEq) (catch Throwable _ nil))
                        [_ feA] (when feT (e/get-app-fn-args feT))
                        R1 (when (and feA (>= (count feA) 3)) (nth feA 2))
                        ;; the [inst]-parameterized frame rhs carries instance projections that shift
                        ;; arg positions — monomorphize them away before structural navigation.
                        preidx (when R1 (extract-frame-preidx (cg/collapse-instance-projections env R1)))]
                    (when preidx
                      (let [floatEq (e/app* (e/const' (nm "Map.foldl_keyfactor_float_generic") [])
                                            natT (sc/mk-semiring-instance natT entry)
                                            K X dec w kf e xs preidx)
                            flT (try (tc/infer-type st floatEq) (catch Throwable _ nil))
                            [_ flA] (when flT (e/get-app-fn-args flT))
                            R2 (when (and flA (>= (count flA) 3)) (nth flA 2))]
                        (when R2
                          (let [rwPf (e/app* (e/const' (nm "Eq.trans") [L1]) natT fterm R1 R2 frameEq floatEq)
                                proof (compose-trans env lctx term fterm R2 fproof rwPf)
                                res {:term R2 :proof proof :changed? true :rewrites [:frame-index-keyfactor]
                                     :physical {:strategy :in-memory-hash :index-est (double ndv-est) :budget (or memory-budget 1.0e8)}
                                     :cost (cost/pipeline-cost R2 {:selectivity selectivity :sizes sizes})}]
                            (adopt-if-improved env term res lctx selectivity sizes)))))))))))))))

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

;; ── the cost-search DRIVER (Phase 8 Level 1 — verbatim port of old optimize-cost) ──────────────
(defn optimize-cost-driver
  "Cost-directed optimization (the SEARCH layer). Always applies the confluent
   fusion set; then GREEDILY tries cost/cost-rewrites (filter_map, relational
   pushdowns) — adopting one only when the re-optimized term both VERIFIES and has
   strictly lower `cost/soac-cost`. The search is untrusted; soundness rests entirely
   on each adopted step being kernel-certified (`verified?`). Returns the
   `cert/optimize` result plus `:rewrites` (the cost/cost-rewrites adopted) and `:cost`.

   FIRST tries a certified, cost-lowering JOIN REORDER (`try-join-reorder`, the
   `Map.join_comm` Perm→Eq bridge for count queries). If it fires, the REORDERED term
   is then fused, and the reorder proof is composed with the fusion proof via
   `Eq.trans` — so a count-join is reordered AND deforested in one kernel-certified
   step. Falls back to the no-reorder search if the composed proof doesn't verify.

   `:selectivity` (a map pred-string→rate, or fn pred→rate) is threaded to
   `cost/pipeline-cost` — pass a MEASURED profile here to drive the search with real
   per-predicate pass-rates (see `ansatz.core/measure-selectivity`). Defaults to
   the static heuristic.

   `:use-egraph?` swaps the greedy one-at-a-time search for EQUALITY SATURATION
   (`wandler.clean.optimize.egraph/saturate-and-extract`): saturate the e-graph with all
   laws and extract the cost-minimal equivalent plan, interleaved with simp fusion.
   Explores rewrite COMBINATIONS greedy ordering can miss; each step still
   kernel-certified. Falls back to the greedy result if saturation doesn't verify."
  [^Env env term & {:keys [lctx pool selectivity sizes use-egraph? skip-reorder? extra-lemmas memory-budget ndv] :or {pool cost/cost-rewrites}}]
  (let [pc (fn [t] (cost/pipeline-cost t {:selectivity selectivity :sizes sizes}))
        ;; PHYSICAL pre-aggregated index (FAQ): a SEPARABLE SUM over a join holds an O(distinct-keys)
        ;; pre-summed index — the best in-memory plan when ndv ≪ |ys|. Try FIRST; adopt when its held
        ;; estimate fits the budget (DuckDB PerfectHashAggregate gating). Certified rewrite.
        pre-agg (when (not skip-reorder?)
                  (try-pre-agg-index env term :lctx lctx :selectivity selectivity :sizes sizes
                                     :memory-budget memory-budget :ndv ndv))
        ;; FAQ FRAME RULE: a SEPARABLE two-sided weight f(x)·g(y) over a join holds the SAME
        ;; O(distinct-keys) pre-summed index (g pre-aggregated), with the probe-side weight f(x) applied
        ;; after the lookup. The f≡1 generalization of pre-agg; disjoint matcher (requires the Nat.mul).
        frame (when (not skip-reorder?)
                (try-frame-index env term :lctx lctx :selectivity selectivity :sizes sizes
                                      :memory-budget memory-budget :ndv ndv))
        ;; CONDITIONAL frame: a separable guard P(x)∧Q(y) over a weighted join — split the guard
        ;; (Nat.cond_and_mul_split) to f'=[P]·f, g'=[Q]·g, then the frame index. Disjoint matcher (cond).
        frame-cond (when (not skip-reorder?)
                     (try-frame-index-cond env term :lctx lctx :selectivity selectivity :sizes sizes
                                                :memory-budget memory-budget :ndv ndv))
        ;; FD SCOPE QUOTIENT: a key-factor w(kf x)·g(y) floats the key-factor into the per-key index
        ;; (frame ∘ Map.foldl_keyfactor_float) — w computed per-key not per-row. Disjoint matcher (w∘kf).
        frame-kf (when (not skip-reorder?)
                   (try-frame-index-keyfactor env term :lctx lctx :selectivity selectivity :sizes sizes
                                                   :memory-budget memory-budget :ndv ndv))
        ;; PHYSICAL grace-hash: if a memory budget is set and the join index would exceed it, spill
        ;; the build side into budget-sized blocks BEFORE factorization (grace-hash is an ALTERNATIVE
        ;; to the in-memory hash/factor, operating on the raw foldl-over-join). Certified rewrite.
        gh (when (and memory-budget (not skip-reorder?))
             (try-grace-hash env term :lctx lctx :selectivity selectivity :sizes sizes :memory-budget memory-budget))
        ;; dedicated count-over-join paths, cost-chosen + certified directly (not via the simp
        ;; pool): FIRST factorize the join away (aggregation-through-join, biggest win), else
        ;; reorder which side is indexed. Both reduce to length/sum over xs, then fuse normally.
        reorder (when-not skip-reorder?
                  (or ;; Step 3c: certified refinement filter-elimination — drop a filter the element
                      ;; type proves redundant (always-true), composed with downstream fusion. Folds
                      ;; Subsystem B's capability into the one cascade. Sound (verified-rewrite?).
                      (fe/try-filter-elim env term :lctx lctx)
                      ;; Step 4: certified DISTINCT-removal — drop an eraseDups over a Nodup-refined
                      ;; (declared `:set`/key) list. Sound ONLY given the declared uniqueness.
                      (fe/try-distinct-elim env term :lctx lctx)
                      (try-count-factor env term :lctx lctx :selectivity selectivity :sizes sizes)
                      ;; RECURSIVE FAQ variable elimination: factor EVERY join in a multi-way tree, not
                      ;; just the outermost (iterate the proven single step to a fixpoint, composing proofs).
                      (try-fold-factor* env term :lctx lctx :selectivity selectivity :sizes sizes)
                      (try-join-reorder env term :lctx lctx :selectivity selectivity :sizes sizes)
                      ;; 1-variable FAQ elimination: hoist a loop-invariant multiplicative factor out of
                      ;; a sum (the measured nested-fold quadratic → linear). Certified by sum_map_mul_const.
                      (try-hoist-invariant env term :lctx lctx :selectivity selectivity :sizes sizes)))]
    (cond
      ;; pre-agg wins when its held index (O(distinct keys)) fits the budget — strictly better than the
      ;; raw factor (O(|ys|) buckets) for separable sums. Else fall through to grace-hash / factor.
      (and pre-agg (:verified? pre-agg)
           (<= (double (:index-est (:physical pre-agg))) (double (or memory-budget 1.0e8))))
      pre-agg
      ;; frame index (two-sided separable weight) — same held-index gate as pre-agg.
      (and frame (:verified? frame)
           (<= (double (:index-est (:physical frame))) (double (or memory-budget 1.0e8))))
      frame
      ;; conditional frame index (separable guard) — same held-index gate.
      (and frame-cond (:verified? frame-cond)
           (<= (double (:index-est (:physical frame-cond))) (double (or memory-budget 1.0e8))))
      frame-cond
      ;; key-factor float (FD scope quotient) — same held-index gate.
      (and frame-kf (:verified? frame-kf)
           (<= (double (:index-est (:physical frame-kf))) (double (or memory-budget 1.0e8))))
      frame-kf
      (:verified? gh) gh
      (and reorder (:verified? reorder))
      ;; a pre-rewrite fired → fuse its result, then compose proofs (pre ∘ fuse).
      (let [sub (optimize-cost-driver env (:term reorder) :lctx lctx :pool pool :extra-lemmas extra-lemmas
                               :selectivity selectivity :sizes sizes :use-egraph? use-egraph? :skip-reorder? true)
            composed (compose-trans env lctx term (:term reorder) (:term sub)
                                    (:proof reorder) (:proof sub))
            res {:term (:term sub) :proof composed :changed? true
                 :rewrites (into [(:rw reorder)] (:rewrites sub)) :cost (:cost sub)}
            ;; PHYSICAL strategy: hoist loop-invariant index builds out of the fold (the in-memory
            ;; hash join), making a factorized join O(N) not O(N²). β-equivalent → the composed proof
            ;; still certifies. MEMORY-GATED: only when the held index fits the budget (default
            ;; generous; aggregation-through-join indices are O(distinct keys)).
            res (let [h (hoist-invariant-indices env lctx (:term res))
                      ;; the held-index footprint ≈ the build side: estimate from the ORIGINAL term
                      ;; (which still has the Map.join node; the factorized/hoisted term doesn't).
                      idx-mem (:memory (cost/pipeline-resources term {:selectivity selectivity :sizes sizes}))]
                  (cond
                    ;; FITS the budget → in-memory HASH: hoist the index (β-equiv, proof unchanged).
                    (and (not (.equals ^Object h (:term res))) (<= idx-mem (or memory-budget 1.0e8)))
                    (assoc res :term h :rewrites (conj (:rewrites res) :hoist-index)
                           :physical {:strategy :in-memory-hash :index-est idx-mem :budget (or memory-budget 1.0e8)})
                    ;; EXCEEDS an explicit budget → NESTED-LOOP: bucket_content removes the O(|ys|)
                    ;; index → a per-row filter (O(bucket) memory, no held index). Certified by an
                    ;; Eq law, so compose: orig ≡ factorized (res.proof) ∘ factorized ≡ nested-loop.
                    (and memory-budget (> idx-mem memory-budget))
                    (let [nl (cert/optimize env (:term res) :lctx lctx :extra-lemmas ['Map.bucket_content])]
                      (if (and (:changed? nl) (:verified? nl) (:proof nl))
                        (assoc res :term (:term nl) :rewrites (conj (:rewrites res) :nested-loop)
                               :proof (compose-trans env lctx term (:term res) (:term nl) (:proof res) (:proof nl))
                               :physical {:strategy :nested-loop :index-est idx-mem :budget memory-budget})
                        res))
                    :else res))
            res (assoc res :verified? (cert/verified-rewrite? env term res :lctx lctx))]
        (if (:verified? res)
          res
          ;; composition didn't certify — fall back to the plain (no-reorder) search
          (optimize-cost-driver env term :lctx lctx :pool pool :selectivity selectivity :sizes sizes :extra-lemmas extra-lemmas
                         :use-egraph? use-egraph? :skip-reorder? true)))
      :else
      ;; no reorder → the cost-directed search
      (let [base (cert/optimize env term :lctx lctx :extra-lemmas extra-lemmas)
            base (if (:verified? base) base {:term term :verified? true :changed? false})]
        (if use-egraph?
          ;; e-graph saturation search (resolved lazily to avoid a namespace cycle)
          (let [sat ((requiring-resolve 'wandler.clean.optimize.egraph/saturate-and-extract)
                     env term :lctx lctx :selectivity selectivity :sizes sizes)]
            (if (and sat (:verified? sat) (:changed? sat)
                     (< (pc (:term sat)) (pc (:term base))))
              (assoc sat :rewrites [:egraph] :cost (cost/soac-cost (:term sat)))
              (assoc base :rewrites [] :cost (cost/soac-cost (:term base)))))
          ;; greedy cost-directed search (default)
          (loop [best base, remaining pool, applied []]
            (let [cands (keep (fn [r]
                                (let [v (cert/optimize env term :lctx lctx
                                                  :extra-lemmas (concat extra-lemmas (conj applied r)))]
                                  ;; GATE on cost/pipeline-cost (cardinality), not op-count, so a
                                  ;; SOAC-neutral reorder (filter→join) is kept for its
                                  ;; cardinality win. `:cost` still reports cost/soac-cost.
                                  (when (and (:verified? v) (< (pc (:term v)) (pc (:term best))))
                                    [r v])))
                              remaining)]
              (if (empty? cands)
                (assoc best :rewrites applied :cost (cost/soac-cost (:term best)))
                (let [[r v] (apply min-key (comp pc :term second) cands)]
                  (recur v (remove #{r} remaining) (conj applied r)))))))))))


