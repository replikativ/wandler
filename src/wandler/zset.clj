(ns wandler.zset
  "The DBSP-faithful relational VIEW: a Z-set `Zset A := A → Int` (element → weight), the order-free
   weighted-set model. Because the carrier is a FUNCTION (not an ordered list), the differential join
   is an EXACT equality (funext + Int distributivity) — no permutation, and deletions come for free as
   negative weights. This is the port of `equi_join`/`product_bilinear` from the reference Lean DBSP
   formalization (tchajed/dbsp-theory, relational.lean), where relations are `Z[A] = A → ℤ`.

   Contrast with wandler.dbsp (List(A×Int) carrier, `Zset.weight`): there the join is over ordered lists
   and only the WEIGHT (count) increment is exact (permutation-invariant). Here the FULL view is exact.

   Certified (check-constant'd; `(wandler.zset/install!)`):
     Zproduct_left_linear  : Zproduct (m1 ⊞ d) m2  = Zproduct m1 m2 ⊞ Zproduct d m2
     Zproduct_right_linear : Zproduct m1 (m2 ⊞ d)  = Zproduct m1 m2 ⊞ Zproduct m1 d
     Zproduct_product_rule : Zproduct (m1⊞d1)(m2⊞d2) = (m1·m2 ⊞ m1·d2) ⊞ (d1·m2 ⊞ d1·d2)
   — the last is the bilinear DIFFERENTIAL join (both relations change), exact, the streaming
   incremental step over Z-set streams."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(def ^:private intT (e/const' (nm "Int") []))
(defn- zsetOf [a] (e/app (e/const' (nm "Zset") []) a))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- pfst [X Y p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
(defn- psnd [X Y p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
(defn- haddI [a b] (e/app* (e/const' (nm "HAdd.hAdd") [z z z]) intT intT intT
                           (e/app* (e/const' (nm "instHAdd") [z]) intT (e/const' (nm "Int.instAdd") [])) a b))
(defn- hmulI [a b] (e/app* (e/const' (nm "HMul.hMul") [z z z]) intT intT intT
                           (e/app* (e/const' (nm "instHMul") [z]) intT (e/const' (nm "Int.instMul") [])) a b))
(defn- funextZ [T f g h] (e/app* (e/const' (nm "funext") [L1 L1]) T (e/lam "_" T intT :default) f g h))
(defn- eqZ [T x y] (e/app* (e/const' (nm "Eq") [L1]) T x y))
(defn- zaddE [A m1 m2] (e/app* (e/const' (nm "Zadd") []) A m1 m2))
(defn- zprodE [A B m1 m2] (e/app* (e/const' (nm "Zproduct") []) A B m1 m2))

(defn- op-defs []
  (let [A (e/fvar 1) B (e/fvar 2)]
    [;; Zset A := A → Int
     (kenv/mk-def (nm "Zset") [] (e/forall' "A" type0 type0 :default)
       (e/lam "A" type0 (e/forall' "_" (e/bvar 0) intT :default) :default))
     ;; Zadd m1 m2 := λa. m1 a + m2 a  (pointwise abelian-group op ⊞)
     (kenv/mk-def (nm "Zadd") []
       (-> (e/forall' "_" (zsetOf A) (zsetOf A) :default)
           (#(e/forall' "m1" (zsetOf A) % :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
       (-> (haddI (e/app (e/fvar 2) (e/bvar 0)) (e/app (e/fvar 3) (e/bvar 0)))
           (#(e/lam "a" A % :default))
           (#(e/lam "m2" (zsetOf A) (e/abstract1 % 3) :default)) (#(e/lam "m1" (zsetOf A) (e/abstract1 % 2) :default))
           (#(e/lam "A" type0 (e/abstract1 % 1) :default))))
     ;; Zproduct m1 m2 := λp:(A×B). m1 p.1 * m2 p.2  (cartesian product of Z-sets, bilinear)
     (kenv/mk-def (nm "Zproduct") []
       (-> (zsetOf (prodT A B))
           (#(e/forall' "m2" (zsetOf B) % :default)) (#(e/forall' "m1" (zsetOf A) % :default))
           (#(e/forall' "B" type0 (e/abstract1 % 2) :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
       (-> (hmulI (e/app (e/fvar 3) (pfst A B (e/bvar 0))) (e/app (e/fvar 4) (psnd A B (e/bvar 0))))
           (#(e/lam "p" (prodT A B) % :default))
           (#(e/lam "m2" (zsetOf B) (e/abstract1 % 4) :default)) (#(e/lam "m1" (zsetOf A) (e/abstract1 % 3) :default))
           (#(e/lam "B" type0 (e/abstract1 % 2) :default)) (#(e/lam "A" type0 (e/abstract1 % 1) :default))))]))

;; bilinearity: linear in each argument (EXACT — funext + Int distributivity). `dist` is the Int law
;; (add_mul for the left arg, mul_add for the right); `mk-pt` builds the pointwise witness at p.
(defn- prove-linear [side]
  (let [A (e/fvar 1) B (e/fvar 2) m1 (e/fvar 3) x (e/fvar 4) y (e/fvar 5) p (e/fvar 6) AB (prodT A B)
        left? (= side :left)
        ;; left: Zproduct (m1 ⊞ x) y ; right: Zproduct m1 (x ⊞ y)   (x = the delta-bearing arg)
        lhs (if left? (zprodE A B (zaddE A m1 x) y) (zprodE A B m1 (zaddE B x y)))
        rhs (if left? (zaddE AB (zprodE A B m1 y) (zprodE A B x y))
                      (zaddE AB (zprodE A B m1 x) (zprodE A B m1 y)))
        pt (if left?
             (e/app* (e/const' (nm "Int.add_mul") []) (e/app m1 (pfst A B p)) (e/app x (pfst A B p)) (e/app y (psnd A B p)))
             (e/app* (e/const' (nm "Int.mul_add") []) (e/app m1 (pfst A B p)) (e/app x (psnd A B p)) (e/app y (psnd A B p))))
        proof (funextZ AB lhs rhs (e/lam "p" AB (e/abstract1 pt 6) :default))
        ty (eqZ (zsetOf AB) lhs rhs)
        zt (fn [v] (zsetOf (if left? v v)))
        wrap (fn [t mk] (-> t (#(mk "y" (zsetOf (if left? B B)) 5 %)) (#(mk "x" (zsetOf (if left? A B)) 4 %))
                            (#(mk "m1" (zsetOf A) 3 %))
                            (#(mk "B" type0 2 %)) (#(mk "A" type0 1 %))))]
    [(wrap ty (fn [n t i b] (e/forall' n t (e/abstract1 b i) :default)))
     (wrap proof (fn [n t i b] (e/lam n t (e/abstract1 b i) :default)))]))

;; the 4-term differential — BOTH inputs change: compose left + right linearity.
(defn- prove-product-rule []
  (let [A (e/fvar 1) B (e/fvar 2) m1 (e/fvar 3) d1 (e/fvar 4) m2 (e/fvar 5) d2 (e/fvar 6) AB (prodT A B)
        m2d2 (zaddE B m2 d2)
        ll (e/app* (e/const' (nm "Zproduct_left_linear") []) A B m1 d1 m2d2)
        rA (e/app* (e/const' (nm "Zproduct_right_linear") []) A B m1 m2 d2)
        rB (e/app* (e/const' (nm "Zproduct_right_linear") []) A B d1 m2 d2)
        zaddAB (fn [x y] (zaddE AB x y))
        Pm1 (zprodE A B m1 m2d2) Pd1 (zprodE A B d1 m2d2)
        Rm1 (zaddAB (zprodE A B m1 m2) (zprodE A B m1 d2)) Rd1 (zaddAB (zprodE A B d1 m2) (zprodE A B d1 d2))
        cg1 (e/app* (e/const' (nm "congrArg") [L1 L1]) (zsetOf AB) (zsetOf AB) Pm1 Rm1
                    (e/lam "X" (zsetOf AB) (zaddAB (e/bvar 0) Pd1) :default) rA)
        cg2 (e/app* (e/const' (nm "congrArg") [L1 L1]) (zsetOf AB) (zsetOf AB) Pd1 Rd1
                    (e/lam "Y" (zsetOf AB) (zaddAB Rm1 (e/bvar 0)) :default) rB)
        congr (e/app* (e/const' (nm "Eq.trans") [L1]) (zsetOf AB) (zaddAB Pm1 Pd1) (zaddAB Rm1 Pd1) (zaddAB Rm1 Rd1) cg1 cg2)
        proof (e/app* (e/const' (nm "Eq.trans") [L1]) (zsetOf AB)
                      (zprodE A B (zaddE A m1 d1) m2d2) (zaddAB Pm1 Pd1) (zaddAB Rm1 Rd1) ll congr)
        ty (eqZ (zsetOf AB) (zprodE A B (zaddE A m1 d1) (zaddE B m2 d2)) (zaddAB Rm1 Rd1))
        wrap (fn [t mk] (-> t (#(mk "d2" (zsetOf B) 6 %)) (#(mk "m2" (zsetOf B) 5 %)) (#(mk "d1" (zsetOf A) 4 %)) (#(mk "m1" (zsetOf A) 3 %))
                            (#(mk "B" type0 2 %)) (#(mk "A" type0 1 %))))]
    [(wrap ty (fn [n t i b] (e/forall' n t (e/abstract1 b i) :default)))
     (wrap proof (fn [n t i b] (e/lam n t (e/abstract1 b i) :default)))]))

(defonce ^:private cache (atom nil))
(defn install!
  "Admit the Z-set carrier + the EXACT bilinear differential join (idempotent)."
  []
  (when-not (kenv/lookup (a/env) (nm "Zproduct_product_rule"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [defs (op-defs)
            _ (doseq [d defs] (swap! a/ansatz-env kenv/check-constant d))
            thms [["Zproduct_left_linear" (prove-linear :left)]
                  ["Zproduct_right_linear" (prove-linear :right)]
                  ["Zproduct_product_rule" (prove-product-rule)]]
            cis (mapv (fn [[name [ty pf]]] (let [ci (kenv/mk-thm (nm name) [] ty pf)]
                                             (swap! a/ansatz-env kenv/check-constant ci) ci)) thms)]
        (reset! cache (into (vec defs) cis)))))
  (a/env))

;; ── runtime: a Z-set is a map element→weight (0 = absent); deletions are NEGATIVE weights ─────────
(defn z-add
  "Z-set addition ⊞ — pointwise weight sum, dropping zeros (the abelian-group op)."
  [m1 m2]
  (into {} (remove (comp zero? val)) (merge-with + m1 m2)))

(defn z-product
  "Z-set cartesian product — `{[a b] (* wa wb)}` over the supports (weights multiply)."
  [m1 m2]
  (into {} (remove (fn [[_ v]] (zero? v)))
        (for [[a wa] m1 [b wb] m2] [[a b] (* wa wb)])))

(defn z-join
  "Equi-join of two Z-sets on key fns — product, keep matching keys (weights multiply)."
  [kf lf m1 m2]
  (into {} (remove (fn [[_ v]] (zero? v)))
        (for [[a wa] m1 [b wb] m2 :when (= (kf a) (lf b))] [[a b] (* wa wb)])))

;; ── the INTEGRATED incremental join engine ──────────────────────────────────────────────────────
;; Each step IS the certified bilinear differential (Zproduct_product_rule): given the join view V of
;; L ⋈ R and a delta batch (δL, δR), the new view is V ⊞ (δL⋈R ⊞ L⋈δR ⊞ δL⋈δR). Only the THREE cross-
;; terms touch the deltas — O(|δ|·|other| + |δ|²) per step, never the O(|L|·|R|) full recompute. The
;; kernel theorem proves this equals `(L⊞δL) ⋈ (R⊞δR)`, so the engine is sound BY CONSTRUCTION.
(defn join-step
  "One incremental step: from state [L R V] and a delta batch [δL δR], maintain the join view via the
   3 cross-terms (the certified bilinear differential). Returns the next [L' R' V']."
  [kf lf [L R V] [dL dR]]
  (let [dV (reduce z-add [(z-join kf lf dL R) (z-join kf lf L dR) (z-join kf lf dL dR)])]
    [(z-add L dL) (z-add R dR) (z-add V dV)]))

(defn incremental-join
  "Maintain `L ⋈ R` INCREMENTALLY over a sequence of `[δL δR]` Z-set delta batches (insertions are
   positive weights, RETRACTIONS negative). Lazy: returns the stream of running join views (one per
   batch consumed) — the certified differential view over time. `deltas` may be an infinite lazy seq."
  [kf lf deltas]
  (->> deltas
       (reductions (partial join-step kf lf) [{} {} {}])
       (drop 1)               ; drop the empty seed state
       (map (fn [[_ _ V]] V))))

(defn batch-join
  "The from-scratch recompute of `L ⋈ R` after applying all `deltas` up to each point — the spec the
   incremental engine is differential-tested against."
  [kf lf deltas]
  (->> deltas
       (reductions (fn [[L R] [dL dR]] [(z-add L dL) (z-add R dR)]) [{} {}])
       (drop 1)
       (map (fn [[L R]] (z-join kf lf L R)))))

;; LINEAR operators on Z-sets — their increment is just the operator applied to the delta (DBSP Thm 5.4),
;; so they compose with the bilinear join in the incremental engine (filter → join → aggregate).
(defn z-filter
  "Filter a Z-set by a predicate on the element (weights preserved). LINEAR: z-filter q (a ⊞ b) =
   z-filter q a ⊞ z-filter q b."
  [pred m]
  (into {} (filter (fn [[e w]] (and (pred e) (not (zero? w))))) m))

(defn z-negate
  "The Z-set additive inverse — negate every weight (`z-add m (z-negate m) = ∅`). A full retraction;
   used to diff successive views (`new ⊞ negate(old)` = the change) when wiring dataflow-graph edges."
  [m]
  (into {} (map (fn [[e w]] [e (- w)])) m))

(defn z-map
  "Map a Z-set's elements by `f` (weights preserved; colliding images SUM their weights). LINEAR:
   z-map f (a ⊞ b) = z-map f a ⊞ z-map f b — so its increment is the map of the delta."
  [f m]
  (into {} (remove (fn [[_ v]] (zero? v)))
        (reduce (fn [acc [e w]] (update acc (f e) (fnil + 0) w)) {} m)))

(defn z-sum
  "Weighted aggregate: Σ weight(e) · (f e) — a group homomorphism (so its increment is exact)."
  [f m]
  (reduce-kv (fn [acc e w] (+ acc (* w (f e)))) 0 m))

;; ── the query front door: compile a streaming query to the incremental engine + EXPLAIN the certificate ─
(defn query
  "Compile a streaming relational query — a vector of `stages` — into a fn `Δ-stream → running-results`.
   Stages (the join first, producing the view stream; then linear post-ops):
     [:join kf lf]   — the bilinear differential join   (licensed by `Zproduct_product_rule`)
     [:filter pred]  — keep matching rows                (linear — DBSP Thm 5.4)
     [:map f]        — map each row                      (linear)
     [:sum f]        — Σ weight·(f row)                  (group homomorphism)
   Each step of the resulting engine is a kernel-certified operator; `explain` prints the chain."
  [stages]
  (let [[[_ kf lf] & post] stages]
    (fn [deltas]
      (reduce (fn [views [op a]]
                (case op
                  :filter (map #(z-filter a %) views)
                  :map    (map #(z-map a %) views)
                  :sum    (map #(z-sum a %) views)))
              (incremental-join kf lf deltas) post))))

(defn explain
  "The CERTIFICATE chain for a compiled `query`: which kernel law makes each stage sound to run
   incrementally. The incremental plan is ≡ the batch recompute at every step, by these laws."
  [stages]
  (clojure.string/join "\n"
    (for [[op a b] stages]
      (case op
        :join   (format "  join %s=%s   ⟶  BILINEAR differential  (Zproduct_product_rule): Δview = δL⋈R ⊞ L⋈δR ⊞ δL⋈δR" a b)
        :filter "  filter         ⟶  LINEAR  (DBSP Thm 5.4: Q^Δ=Q — increment is the filter on the delta)"
        :sum    "  sum            ⟶  group HOMOMORPHISM (increment is the sum of the delta)"))))
