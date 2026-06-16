(ns wandler.optimize
  "The verified optimizer (facade). THE IR IS THE KERNEL TERM; THE REWRITER IS simp —
   the elaborated a/defn body IS the plan, and every adopted rewrite carries a kernel
   proof `orig = result` (translation validation, Lean's @[csimp] discipline).

   Split per the cohesion audit:
     wandler.optimize.certify  — simp rewriting + the strict kernel gate (soundness)
     wandler.optimize.cost     — SOAC counts + cardinality/resource model (policy)
     wandler.optimize.physical — dedicated plan drivers (reorder/factor/spill/FAQ/hoist)
   This ns keeps the entry points (optimize-cost, optimize-body, explain) and re-exports
   the split names so existing callers keep working."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [wandler.optimize.certify :as cert]
            [wandler.optimize.cost :as cost]
            [wandler.optimize.physical :as phys]
            [wandler.optimize.cse :as cse])
  (:import [ansatz.kernel Env]))

;; ── re-exports (the pre-split public API) ────────────────────────────────────
(def fusion-lemmas cert/fusion-lemmas)
(def string-lemmas cert/string-lemmas)
(def optimize-term cert/optimize-term)
(def verified-rewrite? cert/verified-rewrite?)
(def optimize cert/optimize)
(def install-filtermap-fusion-law! cert/install-filtermap-fusion-law!)
(def unfold-eqn-ci cert/unfold-eqn-ci)
(def cost-rewrites cost/cost-rewrites)
(def soac-cost cost/soac-cost)
(def soac-stages cost/soac-stages)
(def pipeline-resources cost/pipeline-resources)
(def pipeline-cost cost/pipeline-cost)
(def try-join-reorder phys/try-join-reorder)
(def try-count-factor phys/try-count-factor)
(def try-fold-factor phys/try-fold-factor)
(def try-fold-factor* phys/try-fold-factor*)
(def try-grace-hash phys/try-grace-hash)
(def try-pre-agg-index phys/try-pre-agg-index)
(def try-frame-index phys/try-frame-index)
(def try-frame-index-cond phys/try-frame-index-cond)
(def try-frame-index-keyfactor phys/try-frame-index-keyfactor)
(def hoist-invariant-indices phys/hoist-invariant-indices)



;; When true, a/defn's optimize-body uses EQUALITY SATURATION (the e-graph) instead of the greedy
;; one-at-a-time cost search — it considers all law combinations and extracts the globally cheapest
;; equivalent plan (catching reorders greedy misses), each round kernel-certified. Opt-in per the
;; cost (saturation is heavier): `(binding [opt/*use-egraph* true] (a/defn …))`. Default greedy.
(def ^:dynamic *use-egraph* false)


(defn explain
  "Human-readable account of what `optimize-cost` did — the relational/PHYSICAL strategy
   (in-memory hash vs nested-loop) with the MEMORY reasoning behind the choice, the algebraic
   rewrites, and the certificate. For the REPL: `(println (opt/explain res))`. The resource-aware
   physical decision is legible: which strategy, and why (index estimate vs budget)."
  [result]
  (let [rw (:rewrites result)
        phys (:physical result)
        rewrites (keep phys/rewrite-descriptions rw)
        strlaws  (filter string? rw)]
    (str "verified plan" (when-not (:changed? result) " (unchanged)") "\n"
         (when (seq rewrites) (str "  rewrites: " (clojure.string/join "; " rewrites) "\n"))
         (when phys
           (str "  physical: "
                (case (:strategy phys)
                  :in-memory-hash "IN-MEMORY HASH (build the index once)"
                  :nested-loop    "NESTED-LOOP (stream, no held index)"
                  :grace-hash     "GRACE-HASH (spill: build side in budget-sized blocks)"
                  :pre-agg-index  "PRE-AGGREGATED HASH (buckets pre-summed; O(distinct keys))"
                  (str (:strategy phys)))
                (format " — index est ~%.0f %s budget %s\n"
                        (double (:index-est phys))
                        (if (<= (double (:index-est phys)) (double (:budget phys))) "≤" ">")
                        (if (>= (double (:budget phys)) 1.0e8) "(default)" (format "%.0f" (double (:budget phys)))))))
         (when (seq strlaws) (str "  laws:     " (clojure.string/join ", " strlaws) "\n"))
         "  proof:    " (if (:verified? result) "optimized ≡ original (kernel-certified)" "UNVERIFIED"))))


(defn optimize-cost
  "Cost-directed optimization (the SEARCH layer). Always applies the confluent
   fusion set; then GREEDILY tries cost/cost-rewrites (filter_map, relational
   pushdowns) — adopting one only when the re-optimized term both VERIFIES and has
   strictly lower `cost/soac-cost`. The search is untrusted; soundness rests entirely
   on each adopted step being kernel-certified (`verified?`). Returns the
   `cert/optimize` result plus `:rewrites` (the cost/cost-rewrites adopted) and `:cost`.

   FIRST tries a certified, cost-lowering JOIN REORDER (`phys/try-join-reorder`, the
   `Map.join_comm` Perm→Eq bridge for count queries). If it fires, the REORDERED term
   is then fused, and the reorder proof is composed with the fusion proof via
   `Eq.trans` — so a phys/count-join is reordered AND deforested in one kernel-certified
   step. Falls back to the no-reorder search if the composed proof doesn't verify.

   `:selectivity` (a map pred-string→rate, or fn pred→rate) is threaded to
   `cost/pipeline-cost` — pass a MEASURED profile here to drive the search with real
   per-predicate pass-rates (see `ansatz.core/measure-selectivity`). Defaults to
   the static heuristic.

   `:use-egraph?` swaps the greedy one-at-a-time search for EQUALITY SATURATION
   (`wandler.optimize.egraph/saturate-and-extract`): saturate the e-graph with all
   laws and extract the cost-minimal equivalent plan, interleaved with simp fusion.
   Explores rewrite COMBINATIONS greedy ordering can miss; each step still
   kernel-certified. Falls back to the greedy result if saturation doesn't verify."
  [^Env env term & {:keys [lctx pool selectivity sizes use-egraph? skip-reorder? extra-lemmas memory-budget ndv] :or {pool cost/cost-rewrites}}]
  (let [pc (fn [t] (cost/pipeline-cost t {:selectivity selectivity :sizes sizes}))
        ;; PHYSICAL pre-aggregated index (FAQ): a SEPARABLE SUM over a join holds an O(distinct-keys)
        ;; pre-summed index — the best in-memory plan when ndv ≪ |ys|. Try FIRST; adopt when its held
        ;; estimate fits the budget (DuckDB PerfectHashAggregate gating). Certified rewrite.
        pre-agg (when (not skip-reorder?)
                  (phys/try-pre-agg-index env term :lctx lctx :selectivity selectivity :sizes sizes
                                     :memory-budget memory-budget :ndv ndv))
        ;; FAQ FRAME RULE: a SEPARABLE two-sided weight f(x)·g(y) over a join holds the SAME
        ;; O(distinct-keys) pre-summed index (g pre-aggregated), with the probe-side weight f(x) applied
        ;; after the lookup. The f≡1 generalization of pre-agg; disjoint matcher (requires the Nat.mul).
        frame (when (not skip-reorder?)
                (phys/try-frame-index env term :lctx lctx :selectivity selectivity :sizes sizes
                                      :memory-budget memory-budget :ndv ndv))
        ;; CONDITIONAL frame: a separable guard P(x)∧Q(y) over a weighted join — split the guard
        ;; (Nat.cond_and_mul_split) to f'=[P]·f, g'=[Q]·g, then the frame index. Disjoint matcher (cond).
        frame-cond (when (not skip-reorder?)
                     (phys/try-frame-index-cond env term :lctx lctx :selectivity selectivity :sizes sizes
                                                :memory-budget memory-budget :ndv ndv))
        ;; FD SCOPE QUOTIENT: a key-factor w(kf x)·g(y) floats the key-factor into the per-key index
        ;; (frame ∘ Map.foldl_keyfactor_float) — w computed per-key not per-row. Disjoint matcher (w∘kf).
        frame-kf (when (not skip-reorder?)
                   (phys/try-frame-index-keyfactor env term :lctx lctx :selectivity selectivity :sizes sizes
                                                   :memory-budget memory-budget :ndv ndv))
        ;; PHYSICAL grace-hash: if a memory budget is set and the join index would exceed it, spill
        ;; the build side into budget-sized blocks BEFORE factorization (grace-hash is an ALTERNATIVE
        ;; to the in-memory hash/factor, operating on the raw foldl-over-join). Certified rewrite.
        gh (when (and memory-budget (not skip-reorder?))
             (phys/try-grace-hash env term :lctx lctx :selectivity selectivity :sizes sizes :memory-budget memory-budget))
        ;; dedicated count-over-join paths, cost-chosen + certified directly (not via the simp
        ;; pool): FIRST factorize the join away (aggregation-through-join, biggest win), else
        ;; reorder which side is indexed. Both reduce to length/sum over xs, then fuse normally.
        reorder (when-not skip-reorder?
                  (or (phys/try-count-factor env term :lctx lctx :selectivity selectivity :sizes sizes)
                      ;; RECURSIVE FAQ variable elimination: factor EVERY join in a multi-way tree, not
                      ;; just the outermost (iterate the proven single step to a fixpoint, composing proofs).
                      (phys/try-fold-factor* env term :lctx lctx :selectivity selectivity :sizes sizes)
                      (phys/try-join-reorder env term :lctx lctx :selectivity selectivity :sizes sizes)
                      ;; 1-variable FAQ elimination: hoist a loop-invariant multiplicative factor out of
                      ;; a sum (the measured nested-fold quadratic → linear). Certified by sum_map_mul_const.
                      (phys/try-hoist-invariant env term :lctx lctx :selectivity selectivity :sizes sizes)))]
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
      (let [sub (optimize-cost env (:term reorder) :lctx lctx :pool pool :extra-lemmas extra-lemmas
                               :selectivity selectivity :sizes sizes :use-egraph? use-egraph? :skip-reorder? true)
            composed (phys/compose-trans env lctx term (:term reorder) (:term sub)
                                    (:proof reorder) (:proof sub))
            res {:term (:term sub) :proof composed :changed? true
                 :rewrites (into [(:rw reorder)] (:rewrites sub)) :cost (:cost sub)}
            ;; PHYSICAL strategy: hoist loop-invariant index builds out of the fold (the in-memory
            ;; hash join), making a factorized join O(N) not O(N²). β-equivalent → the composed proof
            ;; still certifies. MEMORY-GATED: only when the held index fits the budget (default
            ;; generous; aggregation-through-join indices are O(distinct keys)).
            res (let [h (phys/hoist-invariant-indices env lctx (:term res))
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
                               :proof (phys/compose-trans env lctx term (:term res) (:term nl) (:proof res) (:proof nl))
                               :physical {:strategy :nested-loop :index-est idx-mem :budget memory-budget})
                        res))
                    :else res))
            res (assoc res :verified? (cert/verified-rewrite? env term res :lctx lctx))]
        (if (:verified? res)
          res
          ;; composition didn't certify — fall back to the plain (no-reorder) search
          (optimize-cost env term :lctx lctx :pool pool :selectivity selectivity :sizes sizes :extra-lemmas extra-lemmas
                         :use-egraph? use-egraph? :skip-reorder? true)))
      :else
      ;; no reorder → the cost-directed search
      (let [base (cert/optimize env term :lctx lctx :extra-lemmas extra-lemmas)
            base (if (:verified? base) base {:term term :verified? true :changed? false})]
        (if use-egraph?
          ;; e-graph saturation search (resolved lazily to avoid a namespace cycle)
          (let [sat ((requiring-resolve 'wandler.optimize.egraph/saturate-and-extract)
                     env term :lctx lctx :selectivity selectivity)]
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


(defn optimize-body
  "Optimize the pipeline INSIDE a function body `λp0…λp_{n-1}. pipeline`. Opens
   the `n` parameter binders with fresh fvars (so the pipeline is optimized in
   its proper context, not as a whole-function term that η-collapses), certifies
   the inner rewrite, then re-abstracts. Returns {:term body', :verified?,
   :changed?}; `:term` is the original body unless the rewrite verified. This is
   what `a/defn` calls to get a faster — but proven-equivalent — runtime term."
  [^Env env body n & {:keys [extra-lemmas]}]
  (loop [e body, i 0, fvids [], types [], names []]
    (if (and (< i n) (e/lam? e))
      (let [fid (+ 8800000 i)]
        (recur (e/instantiate1 (e/lam-body e) (e/fvar fid)) (inc i)
               (conj fvids fid) (conj types (e/lam-type e)) (conj names (e/lam-name e))))
      (let [lctx (into {} (map (fn [fid nm ty] [fid {:name (str nm) :type ty}]) fvids names types))
            ;; INLINE named helpers: a pipeline split across `v/defn` steps fuses as if
            ;; written inline (the `.eq_unfold` rules are definitional, generated on the
            ;; fly into env+). Deep cost counts the passes a helper boundary hides, so the
            ;; pre-check + keep-gate are honest.
            [env0 unfold-names] (cert/with-unfold-lemmas env e)
            ;; ensure the map∘filter→filterMap law is available to the cost driver (idempotent;
            ;; verified once, used only for this optimization — does not touch the global env)
            env+ (cert/install-filtermap-fusion-law! env0)
            cost-before (cost/soac-cost-deep env e)
            ;; cheap pre-check: nothing to fuse with < 2 (deep) SOAC ops — skip simp entirely
            ;; (keeps the default-on path free for non-pipeline bodies). EXCEPTION: a single
            ;; `filter` over a membership scan (List.elem) is SOAC-trivial but the scan is O(in·ys)
            ;; — the verified SEMIJOIN rewrites it to a build-once index probe, so don't skip it.
            res (if (and (< cost-before 2)
                         (not (cost/mentions-const? e "List.elem"))
                         ;; a bare aggregate over a join is SOAC-trivial but carries the
                         ;; |xs|*|ys| product — the factorization laws are exactly for it
                         (not (cost/mentions-const? e "Map.join")))
                  {:term e :verified? true :changed? false :rewrites []}
                  ;; cost-directed search (confluent fusion + cost-gated reorderings),
                  ;; each adopted step kernel-certified; helper unfolds inline named steps
                  (optimize-cost env+ e :lctx lctx :use-egraph? *use-egraph*
                                 :extra-lemmas (concat extra-lemmas unfold-names)))
            ;; SHARED-SUBTREE PLANNING (CSE) — POST-fusion: fusion inlines cheap shared subterms
            ;; (filter/map fuse away), so what remains shared is a BARRIER the planner should compute
            ;; once (a join / sort / group-by / engine read used by ≥2 consumers). Hoist it into a
            ;; `let`; the certificate is Eq.refl (zeta defeq). Runs after fusion so simp's zeta can't
            ;; re-inline it. Composes (fuse ∘ cse) proofs by Eq.trans.
            res (if-not (:verified? res) res
                  (loop [r res, guard 0]
                    (let [c (when (< guard 8) (cse/try-cse env+ (:term r) :lctx lctx))]
                      (if (and c (:verified? c))
                        (recur {:term (:term c)
                                :proof (phys/compose-trans env+ lctx e (:term r) (:term c) (:proof r) (:proof c))
                                :verified? true :changed? true
                                :rewrites (conj (vec (:rewrites r)) :cse)}
                               (inc guard))
                        r))))
            ;; keep iff verified + changed; AND when helpers were inlined, only if the
            ;; honest SOAC cost strictly DROPPED — so inlining that doesn't fuse (would
            ;; just duplicate code) is reverted to the compact original.
            ok (and (:verified? res) (:changed? res)
                    (or (empty? unfold-names)
                        (< (cost/soac-cost (:term res)) cost-before)))
            reabstract (fn [t]
                         (loop [t t, j (dec (count fvids))]
                           (if (neg? j) t
                               (recur (e/lam (str (nth names j)) (nth types j)
                                             (e/abstract1 t (nth fvids j)) :default)
                                      (dec j)))))]
        {:term (if ok (reabstract (:term res)) body)
         :verified? (:verified? res)
         :changed? (boolean ok)
         :rewrites (:rewrites res)
         ;; plan/explain info: the pipeline stages + pass counts, before/after fusion
         :stages-before (cost/soac-stages e)
         :stages-after (cost/soac-stages (if ok (:term res) e))
         :passes-before cost-before
         :passes-after (cost/soac-cost (if ok (:term res) e))}))))

