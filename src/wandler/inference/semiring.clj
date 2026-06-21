(ns wandler.inference.semiring
  "The SEMIRING core — `Rel A S := A → S` over a semiring `S` (PROGRAMMING_MODEL.md §2). One algebra,
   many domains: swap `S` and the *same* relational operators compute query results (counting), set
   semantics (Bool), shortest paths (tropical), provenance, fuzzy logic, …  Z-sets are the case `S = ℤ`.

   This brick lands the piece that is uniquely ours vs. the datahike/Scallop semiring-datalog design
   (../datahike/.internal): that design *documents* which semirings may safely recurse in a POPS
   compatibility matrix; here the gate is a **kernel theorem**. The key one is **absorption**
   `a ⊕ (a ⊗ b) = a` (Khamis et al. datalog° POPS): a semiring with it converges under recursion.

     `Bool.absorptive` — PROVEN (`∨ a (∧ a b) = a`, by cases): classical datalog recurses safely. ★
     counting (`ℕ`/`ℤ`): absorption FAILS (`1 + 1·1 = 2 ≠ 1`) — may NOT recurse (use a windowed/top-k
       strategy or it diverges). ✗

   A `Semiring` here is a Clojure spec bundling the runtime ops + a reference to the kernel proof of its
   recursion-safety (same pattern as `wandler.reducers/MonoidSpec`). The relational operators
   (`rel-add`/`rel-mul`/`rel-join`/`rel-sum`) are generic over it. See [[semiring-sum-product-planner]]."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.set :as set]))

;; ── the recursion-safety certificate: Bool absorption (PROVEN) ───────────────────────────────────
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(defn- nm [s] (name/from-string s))
(def ^:private BoolT (e/const' (nm "Bool") []))

(defn- prove-bool-absorptive []
  ;; Bool.absorptive : ∀ a b : Bool, Bool.or a (Bool.and a b) = a   (by cases on a; each case is rfl)
  (let [a (e/fvar 1) b (e/fvar 2)
        orE  (fn [x y] (e/app* (e/const' (nm "Bool.or") []) x y))
        andE (fn [x y] (e/app* (e/const' (nm "Bool.and") []) x y))
        eqB  (fn [x y] (e/app* (e/const' (nm "Eq") [L1]) BoolT x y))
        reflB (fn [c] (e/app* (e/const' (nm "Eq.refl") [L1]) BoolT c))
        motive (e/lam "x" BoolT (eqB (orE (e/bvar 0) (andE (e/bvar 0) b)) (e/bvar 0)) :default)
        body (e/app* (e/const' (nm "Bool.casesOn") [z]) motive a
                     (reflB (e/const' (nm "Bool.false") [])) (reflB (e/const' (nm "Bool.true") [])))
        ty (-> (eqB (orE a (andE a b)) a)
               (#(e/forall' "b" BoolT (e/abstract1 % 2) :default))
               (#(e/forall' "a" BoolT (e/abstract1 % 1) :default)))
        pf (-> body
               (#(e/lam "b" BoolT (e/abstract1 % 2) :default))
               (#(e/lam "a" BoolT (e/abstract1 % 1) :default)))]
    [ty pf]))

;; ── the kernel `Semiring` STRUCTURE — the semiring as a kernel-typed value (B1) ───────────────────
;; `Semiring S := { zero one : S, add mul : S → S → S }` via a/structure (projections + recursor); a
;; semiring is then a first-class kernel term, so `Rel A S` is a kernel type and the planner (B2) can be
;; generic over it. Built programmatically in `install!` (the macro qualifies everything, so `eval` is
;; safe from here) so it survives the test env-reset. Instances are `Semiring.mk S 0 1 ⊕ ⊗`.
(defn- mkInst [T zero one add mul] (e/app* (e/const' (nm "Semiring.mk") []) T zero one add mul))
(defn- srOf [T] (e/app (e/const' (nm "Semiring") []) T))

(defn- install-structure! []
  (when-not (kenv/lookup (a/env) (nm "Semiring"))
    (eval '(ansatz.core/structure Semiring [S Type] (zero S) (one S)
                                  (add (-> S (-> S S))) (mul (-> S (-> S S))))))
  ;; kernel instances: Bool (existence) and Nat (counting)
  (let [BoolT (e/const' (nm "Bool") []) NatT (e/const' (nm "Nat") [])
        defs [["Semiring.Bool" BoolT (mkInst BoolT (e/const' (nm "Bool.false") []) (e/const' (nm "Bool.true") [])
                                             (e/const' (nm "Bool.or") []) (e/const' (nm "Bool.and") []))]
              ["Semiring.Nat" NatT (mkInst NatT (e/const' (nm "Nat.zero") []) (e/app (e/const' (nm "Nat.succ") []) (e/const' (nm "Nat.zero") []))
                                           (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.mul") []))]]]
    (doseq [[name T inst] defs]
      (when-not (kenv/lookup (a/env) (nm name))
        (swap! a/ansatz-env kenv/check-constant (kenv/mk-def (nm name) [] (srOf T) inst))))))

;; ── the FAQ-soundness certificate for Bool: distributivity (factorization) + ⊕/⊗ commutativity ────
(defn- opE [o x y] (e/app* (e/const' (nm o) []) x y))
(defn- eqBl [x y] (e/app* (e/const' (nm "Eq") [L1]) BoolT x y))
(defn- reflBl [x] (e/app* (e/const' (nm "Eq.refl") [L1]) BoolT x))
(defn- casesBl [motive maj cF cT] (e/app* (e/const' (nm "Bool.casesOn") [z]) motive maj cF cT))
(def ^:private bF (e/const' (nm "Bool.false") [])) (def ^:private bT (e/const' (nm "Bool.true") []))

(defn- prove-bool-comm [o]
  ;; ∀ a b, op a b = op b a  (commutativity — the FAQ elimination-order-independence; nested cases, rfl)
  (let [a (e/fvar 1) b (e/fvar 2)
        inner (fn [av] (casesBl (e/lam "y" BoolT (eqBl (opE o av (e/bvar 0)) (opE o (e/bvar 0) av)) :default) b
                                (reflBl (opE o av bF)) (reflBl (opE o av bT))))
        body  (casesBl (e/lam "x" BoolT (eqBl (opE o (e/bvar 0) b) (opE o b (e/bvar 0))) :default) a (inner bF) (inner bT))]
    [(-> (eqBl (opE o a b) (opE o b a)) (#(e/forall' "b" BoolT (e/abstract1 % 2) :default)) (#(e/forall' "a" BoolT (e/abstract1 % 1) :default)))
     (-> body (#(e/lam "b" BoolT (e/abstract1 % 2) :default)) (#(e/lam "a" BoolT (e/abstract1 % 1) :default)))]))

(defn- prove-bool-distrib []
  ;; ∀ a b c, a ∧ (b ∨ c) = (a∧b) ∨ (a∧c)  — ⊗ distributes over ⊕ = the FAQ factorization core (cases on a)
  (let [a (e/fvar 1) b (e/fvar 2) c (e/fvar 3)
        body (casesBl (e/lam "x" BoolT (eqBl (opE "Bool.and" (e/bvar 0) (opE "Bool.or" b c))
                                             (opE "Bool.or" (opE "Bool.and" (e/bvar 0) b) (opE "Bool.and" (e/bvar 0) c))) :default)
                      a (reflBl bF) (reflBl (opE "Bool.or" b c)))]
    [(-> (eqBl (opE "Bool.and" a (opE "Bool.or" b c)) (opE "Bool.or" (opE "Bool.and" a b) (opE "Bool.and" a c)))
         (#(e/forall' "c" BoolT (e/abstract1 % 3) :default)) (#(e/forall' "b" BoolT (e/abstract1 % 2) :default)) (#(e/forall' "a" BoolT (e/abstract1 % 1) :default)))
     (-> body (#(e/lam "c" BoolT (e/abstract1 % 3) :default)) (#(e/lam "b" BoolT (e/abstract1 % 2) :default)) (#(e/lam "a" BoolT (e/abstract1 % 1) :default)))]))

(defn- bool-laws []
  ;; namespaced under `Semiring.` so they don't clobber Init's own `Bool.or_comm`/`Bool.and_comm`.
  [["Bool.absorptive"        (prove-bool-absorptive)]   ; recursion-safety (POPS); novel name, kept
   ["Semiring.bool_or_comm"  (prove-bool-comm "Bool.or")]
   ["Semiring.bool_and_comm" (prove-bool-comm "Bool.and")]
   ["Semiring.bool_distrib"  (prove-bool-distrib)]])     ; FAQ factorization

(defonce ^:private cache (atom nil))

(defn install!
  "Install the semiring core (idempotent): the kernel `Semiring` STRUCTURE + `Bool`/`Nat` instances (B1);
   and the PROVEN Bool semiring laws — `Bool.absorptive` (POPS recursion-safety), `Bool.or_comm`/
   `Bool.and_comm` (FAQ elimination-order independence), `Bool.and_or_distrib` (the FAQ factorization)."
  []
  (install-structure!)
  (when-not (kenv/lookup (a/env) (nm "Semiring.bool_distrib"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [cis (mapv (fn [[nme [ty pf]]]
                        (let [ci (kenv/mk-thm (nm nme) [] ty pf)]
                          (swap! a/ansatz-env kenv/check-constant ci) ci))
                      (bool-laws))]
        (reset! cache cis))))
  (a/env))

(defn faq-certificate
  "The kernel theorems that certify FAQ for `sr`, at one of two LEVELS:
   - `:algebra`   — the runtime FAQ is sound + order-independent: ⊗-distributes-over-⊕ + ⊕/⊗ commutativity
                    (so `join-order = elimination-order` affects cost, not result). Proven for `existence` (Bool).
   - `:execution` — the kernel OPTIMIZER's aggregating-join factorization plan is certified (proven over Nat):
                    `Map.foldl_join_sum_factor` (pre-aggregated FAQ index) + `Map.foldl_join_factor`. This is
                    what `wandler.clean.optimize.faq` rides on to lower a counting query to a verified physical plan.
   Other semirings: the analogous laws (ported/pending)."
  [sr]
  (case (:name sr)
    :existence {:level :algebra
                :distributivity "Semiring.bool_distrib" :add-comm "Semiring.bool_or_comm"
                :mul-comm "Semiring.bool_and_comm" :recursion "Bool.absorptive"}
    :counting  {:level :execution
                :factorization "Map.foldl_join_sum_factor" :fold-factor "Map.foldl_join_factor"}
    nil))

;; ── the Semiring abstraction (runtime ops + a reference to the kernel recursion-safety proof) ─────
(defrecord Semiring [name add mul zero one absorptive-proof])

(def counting
  "The counting semiring (ℕ/ℤ): ⊕=+, ⊗=×. Query cardinalities / Z-set weights. NOT absorptive — may not
   recurse (a recursive count diverges; use a windowed / top-k strategy)."
  (->Semiring :counting + * 0 1 nil))

(def existence
  "The Boolean semiring: ⊕=∨, ⊗=∧. Classical datalog / set membership. Absorptive — recursion-safe,
   certified by the kernel theorem `Bool.absorptive`."
  (->Semiring :existence #(or %1 %2) #(and %1 %2) false true "Bool.absorptive"))

(def min-max-prob
  "The MinMaxProb / fuzzy semiring on [0,1]: ⊕=max, ⊗=min. Recursion-safe (absorptive lattice); the
   proof is over Float and is future work, so its certificate is marked pending (`:pending`)."
  (->Semiring :min-max-prob max min 0.0 1.0 :pending))

(def probability
  "The PROBABILITY semiring (ℝ≥0): ⊕=+, ⊗=×, 0̄=0.0, 1̄=1.0 — the carrier of finite DISTRIBUTIONS
   (`FinDist`, wandler.inference.dist). ⊗ scales a path (independent events), ⊕ sums the probabilities of paths to the
   same outcome (law of total probability). NOT recursion-safe (a probabilistic fixpoint needs a measure /
   discounting). The continuous analogue is the Giry monad — an L2 trusted-oracle boundary, not this."
  (->Semiring :probability + * 0.0 1.0 nil))

(def tropical
  "The tropical / min-plus semiring (ℝ∪∞): ⊕=min, ⊗=+, 0̄=∞, 1̄=0. Shortest paths. Absorptive
   (`min a (a+b) = a` for b≥0) ⇒ recursion-safe; the proof is over Float (pending)."
  (->Semiring :tropical min + ##Inf 0 :pending))

(def provenance
  "The PROVENANCE semiring (Green–Tannen `ℕ[X]`/`BoolFormula`, DNF form): a tag is a set-of-sets of
   fact-ids `#{conj …}` (outer = disjunction, inner = conjunction). ⊕ = ∪ (a result holds via EITHER
   derivation), ⊗ = pairwise-∪ of conjuncts (a join needs BOTH). 0̄ = `#{}` (false), 1̄ = `#{#{}}` (true).
   NOT absorptive (DNF blows up under recursion) ⇒ not recursion-safe — matches the datahike matrix. This
   is the EXACT-marginal path for inference (B4): run it, then WMC the formula (`wmc`)."
  (->Semiring :provenance
    (fn [d1 d2] (set/union d1 d2))
    (fn [d1 d2] (set (for [c1 d1 c2 d2] (set/union c1 c2))))
    #{} #{#{}} nil))

;; ── the recursion gate — the certified version of the datahike POPS compatibility matrix ──────────
(defn recursion-safe?
  "May this semiring appear in a recursive stratum? `:certified` = absorption is a kernel theorem (`:proof`
   names it — vs the datahike/Scallop documentation-only matrix); `:provable-pending` = absorptive but the
   proof isn't in the kernel yet (TRUSTED, sound); `:unsafe` = not absorptive (would diverge). `:safe?` =
   certified OR provable-pending."
  [{:keys [absorptive-proof]}]
  (let [status (cond (string? absorptive-proof)     :certified
                     (= :pending absorptive-proof)  :provable-pending
                     :else                          :unsafe)]
    {:safe?      (not= status :unsafe)
     :certified? (= status :certified)
     :proof      (when (string? absorptive-proof) absorptive-proof)
     :status     status}))

;; ── `Rel A S` = a relation as a map element→S-value (0/absent dropped); operators GENERIC over S ──
(defn rel-add
  "Union ⊕ of two relations — pointwise `(:add sr)` (the additive identity `(:zero sr)` is dropped)."
  [{:keys [add zero]} m1 m2]
  (into {} (remove (fn [[_ v]] (= v zero))) (merge-with add m1 m2)))

(defn rel-mul
  "Cartesian product ⊗ — `(:mul sr)` of the S-values over the product of supports."
  [{:keys [mul zero]} m1 m2]
  (into {} (remove (fn [[_ v]] (= v zero)))
        (for [[a wa] m1 [b wb] m2] [[a b] (mul wa wb)])))

(defn rel-join
  "Equi-join on key fns — ⊗ of the S-values over matching keys. The SAME code computes a counting join
   (cardinalities), an existence join (Bool), a fuzzy join (min), … by swapping `sr`."
  [{:keys [mul zero]} kf lf m1 m2]
  (into {} (remove (fn [[_ v]] (= v zero)))
        (for [[a wa] m1 [b wb] m2 :when (= (kf a) (lf b))] [[a b] (mul wa wb)])))

(defn rel-sum
  "Aggregate / marginalize — ⊕-fold the S-values, re-keyed by `f` (the group key). The FAQ `⊕` /
   variable elimination over the semiring."
  [{:keys [add zero]} f m]
  (reduce-kv (fn [acc e w] (update acc (f e) (fn [cur] (add (or cur zero) w)))) {} m))

;; ── B2: the FAQ sum-product / VARIABLE-ELIMINATION engine, generic over the semiring ─────────────
;; A factor `{:vars #{…} :rel {assignment → S}}` (assignment = `{var → value}`) is a semiring-annotated
;; relation over named variables. A query is `⊕_eliminated ⊗_factors fᵢ`. Variable elimination ⊗-joins
;; the factors mentioning a variable and ⊕-marginalizes it out, one variable at a time. The elimination
;; ORDER is the PLAN — it determines cost, NOT the result (for a COMMUTATIVE semiring, by ⊕/⊗ comm + ⊗
;; distributing over ⊕; the kernel `Semiring` laws are the certificate). join-order = elimination-order:
;; THIS is where database query optimization and probabilistic inference are the same problem.
(defn factor "A semiring-annotated relation over named variables." [vars rel] {:vars (set vars) :rel rel})

(defn factor-join
  "⊗ of two factors — merge assignments agreeing on shared variables, `(:mul sr)` their S-values."
  [{:keys [mul zero]} f1 f2]
  (let [shared (set/intersection (:vars f1) (:vars f2))]
    {:vars (set/union (:vars f1) (:vars f2))
     :rel  (into {} (remove (fn [[_ w]] (= w zero)))
                 (for [[a1 w1] (:rel f1) [a2 w2] (:rel f2)
                       :when (every? #(= (a1 %) (a2 %)) shared)]
                   [(merge a1 a2) (mul w1 w2)]))}))

(defn factor-marginalize
  "⊕ a variable out of a factor (the FAQ marginalization / aggregation)."
  [{:keys [add zero]} v f]
  {:vars (disj (:vars f) v)
   :rel  (into {} (remove (fn [[_ w]] (= w zero)))
               (reduce (fn [acc [a w]] (update acc (dissoc a v) (fn [cur] (add (or cur zero) w)))) {} (:rel f)))})

(defn elimination-order
  "A simple min-degree PLAN: eliminate the non-`keep` variables least-mentioned-first (a cost heuristic;
   any order is correct for a commutative semiring)."
  [keep factors]
  (let [allv (reduce set/union #{} (map :vars factors))]
    (vec (sort-by (fn [v] (count (filter #(contains? (:vars %) v) factors)))
                  (set/difference allv (set keep))))))

(defn faq
  "Run the FAQ query `⊕_{vars∉keep} ⊗_factors fᵢ` over semiring `sr`, eliminating in `order` (default the
   min-degree plan). Plan once, run over ANY semiring — counting (path counts), tropical (shortest path),
   existence (reachability), probability, … — by swapping `sr`. Returns the result factor over `keep`."
  ([sr keep factors] (faq sr keep (elimination-order keep factors) factors))
  ([sr keep order factors]
   (loop [order order, factors (vec factors)]
     (if-let [v (first order)]
       (let [mention (filter #(contains? (:vars %) v) factors)
             rest*   (remove #(contains? (:vars %) v) factors)
             joined  (reduce (partial factor-join sr) mention)]   ; ⊗ factors mentioning v
         (recur (next order) (conj (vec rest*) (factor-marginalize sr v joined))))  ; ⊕ eliminate v
       (reduce (partial factor-join sr) factors)))))

;; ── B3: recursion / datalog as a least-fixpoint, GATED by the certified POPS recursion-safety ────
(defn factor-union
  "⊕ of two factors over the SAME variables — datalog rule-head accumulation / the lattice join."
  [{:keys [add zero]} f1 f2]
  {:vars (:vars f1)
   :rel  (into {} (remove (fn [[_ w]] (= w zero))) (merge-with add (:rel f1) (:rel f2)))})

(defn rename-factor
  "Rename a factor's variables by `kmap` {old→new} (to compose recursive relations on a shared variable)."
  [kmap f]
  {:vars (set (map #(kmap % %) (:vars f)))
   :rel  (into {} (map (fn [[a w]] [(into {} (map (fn [[k v]] [(kmap k k) v])) a) w])) (:rel f))})

(defn fixpoint
  "Least fixpoint over the semiring (datalog recursion): `R ← R ⊕ step(R)` until stable. **GATED by the
   certified POPS recursion-safety** (`recursion-safe?`): refuses a non-absorptive semiring (it would
   diverge) — the datahike/Scallop compatibility matrix, here enforced by the kernel theorem
   `Bool.absorptive`. `step : factor → factor` is the recursive rule body."
  [sr seed step & {:keys [max-iter] :or {max-iter 10000}}]
  (let [{:keys [safe? status]} (recursion-safe? sr)]
    (when-not safe?
      (throw (ex-info (str "recursion over the " (:name sr) " semiring is unsafe (not absorptive — it would "
                           "diverge; status " status "). Use a POPS-safe semiring (existence/tropical/fuzzy) "
                           "or a windowed / top-k strategy.")
                      {:semiring (:name sr) :status status})))
    (loop [r seed i 0]
      (let [r' (factor-union sr r (step r))]
        (cond (= (:rel r) (:rel r')) r
              (>= i max-iter)        (throw (ex-info "fixpoint did not converge" {:iters i}))
              :else                  (recur r' (inc i)))))))

(defn compose-step
  "The transitive-closure rule body for `fixpoint`: `R(from,to) :- E(from,mid), R(mid,to)` — join the
   edge relation `E` with the recursive `R` on a shared middle variable and eliminate it. Returns a
   `step` fn over the chosen semiring."
  [sr E]
  (fn [R]
    (factor-marginalize sr :mid
      (factor-join sr (rename-factor {:to :mid} E) (rename-factor {:from :mid} R)))))

;; ── the surface query front door: ONE datalog-ish query, run over ANY semiring ───────────────────
(defn relation
  "A named relation over ordered columns `cols`, with `tuples` = {[col-values…] → S-annotation}."
  [cols tuples] {:cols (vec cols) :tuples tuples})

(defn- atom->factor
  "A query atom `[rel-name qvar…]` over `relations` → a factor binding the relation's tuple positions to
   the query variables (positionally) — the relational scan, lifted into the FAQ algebra."
  [relations [rel-name & qvars]]
  (let [{:keys [tuples]} (relations rel-name)]
    {:vars (set qvars)
     :rel  (into {} (map (fn [[tup w]] [(zipmap qvars tup) w])) tuples)}))

(defn q
  "Run a datalog-ish query over a chosen semiring `sr`: `{:find [vars] :where [[rel-name qvar…] …]}` with
   `relations` = {name → (relation cols tuples)}. Builds factors from the `:where` atoms, plans the
   variable-elimination order (= the join order), and runs `faq` — so the SAME query is a count, a
   shortest path, a reachability check, or (via `provenance`+`wmc`) an inference, by swapping `sr`."
  [query sr relations]
  (faq sr (:find query) (mapv (partial atom->factor relations) (:where query))))

;; ── B4: inference = the provenance algebra (ours, certified) + WMC (a TRUSTED oracle) ────────────
;; The exact-marginal split (datahike PROBLOG_DESIGN): naive `(prob,+,×)` double-counts shared
;; variables (gives MPE, not the marginal). So: run the PROVENANCE semiring → a Boolean formula (the
;; certified algebraic part, via `faq`), then WEIGHTED MODEL COUNT the formula → the marginal. The WMC
;; is #P-hard and is the TRUSTED ORACLE (here exact via model enumeration; LogicNG/Ganak in production).
(defn wmc
  "Weighted model count of a DNF `formula` (set-of-sets of fact-ids) under INDEPENDENT fact probabilities
   `probs` {fact-id → p}: `P(⋁_conj ⋀_{f∈conj} f)`. A TRUSTED ORACLE — exact here by enumerating the
   2^|facts| assignments; production uses a knowledge-compilation backend (LogicNG/Ganak)."
  [probs formula]
  (let [facts (vec (distinct (mapcat seq formula)))
        sat?  (fn [assign] (boolean (some (fn [conj] (every? assign conj)) formula)))]
    (reduce + 0.0
      (for [bits (range (bit-shift-left 1 (count facts)))
            :let  [assign (into {} (map-indexed (fn [i f] [f (bit-test bits i)]) facts))]
            :when (sat? assign)]
        (reduce * 1.0 (map (fn [f] (if (assign f) (probs f) (- 1.0 (double (probs f))))) facts))))))
