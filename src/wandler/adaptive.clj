(ns wandler.adaptive
  "Adaptive dependently-typed planning — the loop is fundamentally ABDUCTION made honest by a kernel
   theorem:

     1. ABDUCE   — from a data SAMPLE, defeasibly posit the most exploitable refinement consistent with
                   it (here: `kf` is a UNIQUE KEY over the relation — `(distinct? (map kf sample))`).
     2. DEDUCE   — let the kernel PROVE that, *under that refinement*, the plan rewrites to a cheaper
                   one (`Map.groupby_self_elim` : Nodup (map kf xs) ⊢ denormalize-each-row ≡ map-each-row).
                   The refinement is a hypothesis of the theorem, so the rewrite is sound EXACTLY when it
                   holds — never a silent wrong answer.
     3. GUARD    — at the runtime boundary, CHECK the abduced refinement on the real data. The check is
                   the discharge of the theorem's hypothesis; if it fails we fall back to the original
                   plan (which is always correct), so soundness never depends on the abduction being right.
     4. BENCHMARK— purity lets us run BOTH plans on the sample as isolated micro-benchmarks and ADOPT the
                   rewrite only when it is actually faster *including* the guard cost. Statistics govern
                   SELECTION; the kernel proof governs SOUNDNESS. (Cf. refinement-planner — types
                   enlarge the sound-rewrite relation; stats pick among equivalent plans.)

   This is speculative JIT (abduce a fast path, guard it, deopt on failure) with the speculation made
   honest: the fast path is a kernel-certified equivalence, not a hope.

   The prototype is specialized to the GROUP-BY-ELIMINATION capability (Path 2b), the cleanest unique-key
   rewrite; the same skeleton generalizes to any refinement→law pair (distinct-removal, FD scope, …)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [wandler.optimize.filter-elim :as fe]
            [wandler.laws.groupby :as groupby]))

(defn- C [s ls] (e/const' (nm/from-string s) ls))

;; ── 1. ABDUCE ────────────────────────────────────────────────────────────────────────────────────
(defn unique-key?
  "ABDUCE / GUARD: over `coll`, does `kf` produce no duplicate values? This is BOTH the abduction probe
   (run on a sample to posit the refinement) AND the runtime guard (run on the real data to discharge
   the theorem's `Nodup (map kf ·)` hypothesis). Empty/singleton trivially unique."
  [kf coll]
  (let [ks (map kf coll)]
    (or (empty? ks) (apply distinct? ks))))

;; ── carrier construction ───────────────────────────────────────────────────────────────────────--
(defn keyed-carrier
  "Build the dependent carrier `{xs : List X // Nodup (map kf xs)}` for the abduced unique key `kf`
   (a kernel term `X → K`), and an lctx binding fresh fvar `id` to it. `u` = the level of X and K
   (Nat/Prod live at level 0). Returns {:lctx :xs :carrier} where `:xs` is `Subtype.val s` — the
   underlying list, ready to substitute for a plain-`List X` relation binder in a plan."
  [X K kf u id]
  (let [u1     (lvl/succ u)
        listX  (e/app (C "List" [u]) X)
        P       (e/lam "l" listX
                       (e/app* (C "List.Nodup" [u]) K
                               (e/app* (C "List.map" [u u]) X K kf (e/bvar 0)))
                       :default)
        carrier (e/app* (C "Subtype" [u1]) listX P)
        s       (e/fvar id)]
    {:lctx    {id {:name "s" :type carrier}}
     :xs      (e/app* (C "Subtype.val" [u1]) listX P s)
     :carrier carrier}))

;; ── compilation ────────────────────────────────────────────────────────────────────────────────--
(defn compile-plan
  "Compile a kernel plan `term` over the source fvars in `lctx` to a CURRIED Clojure fn (outermost arg
   = lowest fvar id). `Subtype.val` lowers to identity, so a carrier source is passed its underlying
   list at runtime."
  [env term lctx]
  (let [lam (reduce (fn [body id]
                      (e/lam (or (:name (lctx id)) (str "s" id)) (:type (lctx id))
                             (e/abstract1 body id) :default))
                    term (sort > (keys lctx)))]
    (eval (a/ansatz->clj env lam []))))

;; ── benchmarking ───────────────────────────────────────────────────────────────────────────────--
(defn- time-ns
  "Median wall-clock ns of `(thunk)` over `iters` timed runs after `warmup` warmup runs. Purity ⇒ an
   isolated micro-benchmark is meaningful."
  [thunk & {:keys [warmup iters] :or {warmup 20 iters 50}}]
  (dotimes [_ warmup] (thunk))
  (let [ts (sort (for [_ (range iters)]
                   (let [t0 (System/nanoTime)] (thunk) (- (System/nanoTime) t0))))]
    (nth (vec ts) (quot iters 2))))

;; ── 2-4. the loop ──────────────────────────────────────────────────────────────────────────────--
(defn adaptive-groupby
  "THE adaptive loop for group-by elimination. Inputs:
     env        — the post-install env (must have `Map.groupby_self_elim`; call (groupby/install!)).
     X, K       — element / key kernel TYPES (level `u`, default 0).
     kf         — the key projection kernel term `X → K`.
     kf-runtime — the same projection as a Clojure fn (for abduction + guard + benchmark).
     make-plan  — `(xs-term) → plan-term`: builds the kernel plan over a relation term. The plan must
                  contain the denormalize-each-row-with-its-group shape that `try-groupby-elim` matches.
     sample     — sample rows (Clojure data) used to abduce the key and to benchmark.
   Options: :u (level, default lvl/zero), :id (fresh fvar id, default 9001), :data (the real data to
   run the chosen plan over + guard against; defaults to `sample`), :amortize (number of queries the
   refined relation is expected to serve, default 1). The unique-key guard is a ONE-TIME boundary check
   performed when the refined relation is constructed — it is NOT paid per query — so adoption compares
   `rewritten + guard/amortize` against `original`. A one-shot query (amortize 1) keeps the guard cost
   in full (often declines the rewrite); a relation queried many times amortizes the guard toward zero
   (adopts the cheaper plan). This is the plan-once-run-many / PGO model (see wandler.jit.pgo).

   Returns a decision artifact:
     {:abduced-unique? :verified? :rewrites :strategy :certificate
      :bench {:original-ns :rewritten-ns :guard-ns}
      :run  — a 1-arg fn (rows → result) using the ADOPTED plan, with the guard wired in so a runtime
              relation that violates the abduced key transparently falls back to the original plan.}"
  [env X K kf kf-runtime make-plan sample
   & {:keys [u id data amortize] :or {u lvl/zero id 9001 amortize 1}}]
  (let [data         (or data sample)
        abduced?     (unique-key? kf-runtime sample)
        ;; original plan over a PLAIN list source (always correct, always runnable)
        plain        (e/fvar id)
        plain-lctx   {id {:name "xs" :type (e/app (C "List" [u]) X)}}
        orig-plain   (make-plan plain)
        orig-fn      (compile-plan env orig-plain plain-lctx)]
    (if-not abduced?
      ;; abduction failed on the sample — no speculation, just run the original.
      {:abduced-unique? false :verified? false :rewrites [] :strategy :original
       :certificate nil :bench {:original-ns (time-ns #(orig-fn data))}
       :run orig-fn}
      ;; abduced a unique key — DEDUCE the certified rewrite under the carrier.
      (let [{:keys [lctx xs]} (keyed-carrier X K kf u id)
            plan-c   (make-plan xs)                           ; plan over the carrier source
            res      (fe/try-groupby-elim env plan-c :lctx lctx)]
        (if-not (and res (:verified? res))
          ;; the rewrite did not certify — keep the original (sound by default).
          {:abduced-unique? true :verified? false :rewrites [] :strategy :original
           :certificate nil :bench {:original-ns (time-ns #(orig-fn data))}
           :run orig-fn}
          ;; certified candidate: compile it, benchmark both (rewritten incl. guard), pick the winner.
          (let [rw-fn       (compile-plan env (:term res) lctx)
                orig-ns     (time-ns #(orig-fn data))
                guard-ns    (time-ns #(unique-key? kf-runtime data))
                rw-ns       (time-ns #(rw-fn data))
                ;; the guard is a ONE-TIME boundary check, amortized over the query stream; the
                ;; rewrite is worth it once per-query rewritten + amortized guard beats the original.
                adopt?      (< (+ (/ guard-ns (double (max 1 amortize))) rw-ns) orig-ns)
                ;; the SOUND runtime fn: guard the abduced key on the actual rows; fall back if violated.
                guarded-run (fn [rows]
                              (if (unique-key? kf-runtime rows) (rw-fn rows) (orig-fn rows)))]
            {:abduced-unique? true
             :verified?       true
             :rewrites        (:rewrites res)
             :certificate     (:proof res)
             :strategy        (if adopt? :rewritten :original)
             :bench           {:original-ns orig-ns :rewritten-ns rw-ns :guard-ns guard-ns
                               :amortize amortize}
             :run             (if adopt? guarded-run orig-fn)}))))))
