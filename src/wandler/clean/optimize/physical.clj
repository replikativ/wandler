(ns wandler.clean.optimize.physical
  "Physical strategies of the CLEAN optimizer — the cost-driven, kernel-CERTIFIED rewrites that turn a
   logical aggregate over a relational `Map.join` into an asymptotically cheaper physical plan. Unlike
   the streaming fusion pool (simp-applied), each strategy is a DEDICATED recognizer: it pattern-matches
   a join-aggregate shape, builds the proof = the thin relational LAW applied to the recognized args,
   reads the rewritten term off the law's RHS, and adopts it ONLY when it both lowers `cost/pipeline-cost`
   AND strict-certifies via `cert/verified-rewrite?` (check-constant). Soundness rests entirely on that
   gate — the cost model only chooses *which* certified plan.

   This is the clean re-expression of old `wandler.optimize.physical` (foldl-based, ~776 LOC citing
   term-built `Map.foldl_join_*`), now over the AGGREGATE (`wsum`) laws of `wandler.clean.laws.*`:

     try-agg-join-factor — THE FAQ FACTORIZATION (separable-weight instance). Recognizes
       `wsum m (map (λpr. mul m (w pr.fst) (v pr.snd)) (Map.join … kf lf xs ys))` — a sum of a
       SEPARABLE weight `w·v` over a join — and rewrites it via `Map_aggJoin_factor` so the right factor
       `v` is summed ONCE per matching bucket: `wsum m (map (λx. mul m (w x) (∑ v over x's bucket)) xs)`.
       O(|xs|·|ys|) → O(|xs|+|ys|) with a pre-aggregated index; no pairs materialized.

   The commutativity witness `hc : Std.Commutative S (WAddMonoid.add m)` the law needs is supplied by the
   caller (the planner knows its monoid) via `:comm`, with instance synthesis as a fallback."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [wandler.clean.optimize.certify :as cert]
            [wandler.clean.optimize.cost :as cost])
  (:import [ansatz.kernel Env]))

(defn- cn [x] (when (e/const? x) (name/->string (e/const-name x))))

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

(defn- match-app
  "If `t` = `(const head a0 a1 …)` with ≥ n args, return the arg vector; else nil."
  [t head n]
  (let [[h args] (e/get-app-fn-args t)]
    (when (and (e/const? h) (= head (cn h)) (>= (count args) n)) (vec args))))

(defn agg-join-factor-match
  "Recognize `wsum S m (List.map PXY S (λpr. WSemiring.mul S m (w pr.fst) (v pr.snd))
                                       (Map.join K X Y dec kf lf xs ys))`.
   Returns {:K :X :Y :S :dec :m :kf :lf :w :v :xs :ys} or nil. `w`/`v` are the (binder-free) separable
   factor functions, read off the weight lambda's `w (Prod.fst …)` / `v (Prod.snd …)` applications."
  [term]
  (when-let [[_S _addm mapt] (match-app term "wsum" 3)]
    (when-let [[pxy _S2 weight joint] (match-app mapt "List.map" 4)]
      (when-let [[jK jX jY dec kf lf xs ys] (match-app joint "Map.join" 8)]
        (when (e/lam? weight)
          (let [body (e/lam-body weight)]              ; under bvar 0 = pr
            (when-let [[_S3 _m a b] (match-app body "WSemiring.mul" 4)]
              (let [[wf wa] (e/get-app-fn-args a)
                    [vf va] (e/get-app-fn-args b)
                    fst? (and (= 1 (count wa)) (= "Prod.fst" (cn (first (e/get-app-fn-args (first wa))))))
                    snd? (and (= 1 (count va)) (= "Prod.snd" (cn (first (e/get-app-fn-args (first va))))))]
                ;; w = wf, v = vf must be closed (no reference to bvar 0 = pr); the only pr use is the proj.
                (when (and fst? snd?
                           (not (e/has-loose-bvars? wf)) (not (e/has-loose-bvars? vf)))
                  {:K jK :X jX :Y jY :S _S :dec dec :m _m :kf kf :lf lf
                   :w wf :v vf :xs xs :ys ys :pxy pxy})))))))))

(defn agg-join-reorder-match
  "Recognize `wsum S m (List.map PXY S (λpr. f pr.fst pr.snd) (Map.join K X Y dec kf lf xs ys))` — the
   sum of a per-pair weight `f : X→Y→S` over an equi-join. Returns {:K :X :Y :S :m :dec :kf :lf :f
   :xs :ys} or nil. `m` is the wsum's WAddMonoid (no separability needed — reorder is monoid-only)."
  [term]
  (when-let [[_S m mapt] (match-app term "wsum" 3)]
    (when-let [[_pxy _S2 weight joint] (match-app mapt "List.map" 4)]
      (when-let [[jK jX jY dec kf lf xs ys] (match-app joint "Map.join" 8)]
        (when (e/lam? weight)
          (let [body (e/lam-body weight)              ; under bvar 0 = pr
                [ff fargs] (e/get-app-fn-args body)]   ; f (Prod.fst pr) (Prod.snd pr)
            (when (and (= 2 (count fargs))
                       (= "Prod.fst" (cn (first (e/get-app-fn-args (nth fargs 0)))))
                       (= "Prod.snd" (cn (first (e/get-app-fn-args (nth fargs 1)))))
                       (not (e/has-loose-bvars? ff)))
              {:K jK :X jX :Y jY :S _S :m m :dec dec :kf kf :lf lf :f ff :xs xs :ys ys})))))))

(defn- synth-comm
  "The commutativity witness `Std.Commutative S (WAddMonoid.add m)` for the factor law. Prefer the
   caller-supplied `comm`; else try instance synthesis."
  [^Env env st S m comm]
  (or comm
      (let [add  (e/app* (e/const' (name/from-string "WAddMonoid.add") []) S m)
            ssort (try (#'tc/cached-whnf st (tc/infer-type st S)) (catch Throwable _ nil))
            u    (if (and ssort (e/sort? ssort)) (e/sort-level ssort) lvl/zero)
            goal (e/app* (e/const' (name/from-string "Std.Commutative") [u]) S add)]
        (try ((requiring-resolve 'ansatz.tactic.instance/synthesize)
              env ((requiring-resolve 'ansatz.core/instance-index)) goal)
             (catch Throwable _ nil)))))

(defn try-agg-join-factor
  "Cost-driven FAQ factorization of a separable-weight sum over a `Map.join`, certified by
   `Map_aggJoin_factor`. Returns {:term :proof :changed? :verified? :rw} or nil. `:comm` supplies the
   commutativity witness; `:selectivity`/`:sizes` parameterize the cost gate."
  [^Env env term & {:keys [lctx selectivity sizes comm]}]
  (when-let [{:keys [K X Y S dec m kf lf w v xs ys]} (agg-join-factor-match term)]
    (let [st (cert/mk-st env lctx)]
      (when-let [hc (synth-comm env st S m comm)]
        (let [proof (e/app* (e/const' (name/from-string "Map_aggJoin_factor") [])
                            K X Y S dec m hc kf lf w v xs ys)
              ptype (try (tc/infer-type st proof) (catch Throwable _ nil))
              [_ eqargs] (when ptype (e/get-app-fn-args ptype))]
          (when (and eqargs (>= (count eqargs) 3))
            (let [rhs (nth eqargs 2)
                  res {:term rhs :proof proof :changed? true :rw :agg-join-factor}]
              (when (and (< (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                            (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                         (cert/verified-rewrite? env term res :lctx lctx))
                (assoc res :verified? true)))))))))

(defn try-agg-join-reorder
  "Cost-driven JOIN REORDER (drive-direction swap) of a per-pair sum over a `Map.join`, certified by
   `Map_aggJoin_reorder`: build the group_by index on whichever side the cost model prefers (typically
   the smaller). Returns {:term :proof :changed? :verified? :rw} or nil. `:comm` supplies the
   commutativity witness; adopt iff the swapped plan strictly lowers cost AND certifies."
  [^Env env term & {:keys [lctx selectivity sizes comm]}]
  (when-let [{:keys [K X Y S m dec kf lf f xs ys]} (agg-join-reorder-match term)]
    (let [st (cert/mk-st env lctx)]
      (when-let [hc (synth-comm env st S m comm)]
        (let [proof (e/app* (e/const' (name/from-string "Map_aggJoin_reorder") [])
                            K X Y S dec m hc kf lf f xs ys)
              ptype (try (tc/infer-type st proof) (catch Throwable _ nil))
              [_ eqargs] (when ptype (e/get-app-fn-args ptype))]
          (when (and eqargs (>= (count eqargs) 3))
            (let [rhs (nth eqargs 2)
                  res {:term rhs :proof proof :changed? true :rw :agg-join-reorder}]
              (when (and (< (cost/pipeline-cost rhs {:selectivity selectivity :sizes sizes})
                            (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                         (cert/verified-rewrite? env term res :lctx lctx))
                (assoc res :verified? true)))))))))

;; ── loop-invariant HOIST (1-variable FAQ elimination) — Phase 8.4b ────────────────────────────
(defn- cn? [e s] (= s (cn e)))

(defn- nat-zero?
  "Every spelling of Nat 0: the Nat.zero ctor, a bare lit-nat 0 (what `reduce + 0` elaborates to),
   and @OfNat.ofNat Nat 0 _ — all def-eq but syntactically distinct. Syntactic; a false positive
   cannot pass verified-rewrite?, so loose recognition is sound."
  [e]
  (or (cn? e "Nat.zero")
      (and (e/lit-nat? e) (zero? (long (e/lit-nat-val e))))
      (let [[h args] (e/get-app-fn-args e)]
        (and (e/const? h) (= "OfNat.ofNat" (cn h)) (>= (count args) 2) (nat-zero? (nth args 1))))))

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

(def ^:private soac-heads
  "Heads whose presence in an invariant `c` makes hoisting it out of a row-loop worthwhile (the cost
   that matters is a per-row recompute of a traversal). A heuristic worth-it gate, NOT a soundness gate."
  #{"List.foldl" "List.foldr" "List.map" "List.filter" "List.flatMap" "List.filterMap"
    "List.foldlIdx" "List.length" "List.range" "Map.join" "Map.group_by"})

(defn- contains-soac? [e] (any-node? e #(and (e/const? %) (soac-heads (cn %)))))
(defn- contains-fvar? [e id] (any-node? e #(and (e/fvar? %) (= (long id) (e/fvar-id %)))))

(defn- fresh-fvar-id
  "An fvar id guaranteed not to occur in `term` — max(occurring)+1, floored well above every id family
   in use (lctx params, e-graph 9e8+). Avoids the open-binder magic-constant collision."
  [term]
  (let [mx (atom 2000000000)]
    (any-node? term (fn [x] (when (e/fvar? x) (swap! mx max (e/fvar-id x))) false))
    (inc (long @mx))))

(defn- match-sum-map-mul
  "term = foldl Nat Nat Nat.add 0 (map Nat Nat (λx. Nat.mul A B) xs) where exactly ONE of A,B is free
   of the map binder (the loop-invariant factor c) and the other depends on it (the per-row factor f).
   Returns {:f (λx.·) :c · :xs xs :side :right|:left} (:right = f x * c, :left = c * f x) or nil."
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
                body (e/instantiate1 (e/lam-body step) (e/fvar K))
                [bh bargs] (e/get-app-fn-args body)
                lam-of (fn [P] (e/lam "x" (e/const' (name/from-string "Nat") []) (e/abstract1 P K) :default))]
            (when (and (cn? bh "Nat.mul") (= 2 (count bargs)))
              (let [A (nth bargs 0) B (nth bargs 1)
                    A? (contains-fvar? A K) B? (contains-fvar? B K)]
                (cond
                  (and A? (not B?)) {:f (lam-of A) :c B :xs xs :side :right}   ; f x * c
                  (and B? (not A?)) {:f (lam-of B) :c A :xs xs :side :left})))))))))   ; c * f x

(defn try-hoist-invariant
  "Cost-driven LOOP-INVARIANT HOIST (1-variable FAQ elimination). If `term` = foldl(+) 0 (map (λx. f x *
   c) xs) (or the mirror c * f x) with `c` x-free AND loop-shaped (contains a SOAC, so the per-row
   recompute is the cost that matters), rewrite the invariant OUT of the row loop so it is evaluated
   ONCE. Certified by List.sum_map_mul_const (right) / List.sum_map_const_mul (left); adopt iff it
   strict-certifies. Returns {:term :proof :verified? :changed? :rw} or nil. Clean-tree port."
  [^Env env term & {:keys [lctx] :as _opts}]
  (when-let [{:keys [f c xs side]} (match-sum-map-mul term)]
    (when (contains-soac? c)
      (let [natC (e/const' (name/from-string "Nat") [])
            mul  (fn [a b] (e/app* (e/const' (name/from-string "Nat.mul") []) a b))
            add0 (fn [l] (e/app* (e/const' (name/from-string "List.foldl") [lvl/zero lvl/zero]) natC natC
                                 (e/const' (name/from-string "Nat.add") []) (e/const' (name/from-string "Nat.zero") []) l))
            sumf (add0 (e/app* (e/const' (name/from-string "List.map") [lvl/zero lvl/zero]) natC natC f xs))
            [law rhs] (if (= side :left)
                        ["List.sum_map_const_mul" (mul c sumf)]
                        ["List.sum_map_mul_const" (mul sumf c)])
            cert (e/app* (e/const' (name/from-string law) []) f c xs)
            res  {:term rhs :proof cert :changed? true :rw :hoist-invariant}]
        (when (cert/verified-rewrite? env term res :lctx lctx)
          (assoc res :verified? true))))))
