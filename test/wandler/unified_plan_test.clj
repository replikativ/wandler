(ns wandler.unified-plan-test
  "Integration 1, first slice: the CONSUMER-AWARE unified planner (wandler.plan/unified-plan). The SAME
   list-producing source pipeline — a customers⋈orders join (the relational/inductive source) — is planned
   for THREE different sinks, and the SINK alone determines the plan:
     :count  → order-invariant → aggregation-through-join / reorder fires (a physical strategy)
     :sum    → order-invariant → aggregation-through-join fires
     :vector → order-PRESERVING → NO order-destroying rewrite (it wouldn't certify as Eq)
   Every plan is kernel-certified ≡ the naive query and executes to the same answer. This is the
   end-to-end source→sink consumer-awareness, with the certificate doing the gating."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.plan :as plan]
            [wandler.clean.optimize :as opt]
            [wandler.clean.optimize.cost :as cost]
            [wandler.core :as wc]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (wc/install!)        ; SEAM 3: runtime codegen-registry (so optimized plans execute)
    (km/install!)
    (rl/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; the relational source: custs ⋈ orders on field 0 (a stand-in for a materialized DB table source)
(defn- build []
  (let [N  (e/const' (nm "Nat") [])
        NN (e/app* (e/const' (nm "Prod") [z z]) N N)
        PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN)
        listNN (e/app (e/const' (nm "List") [z]) NN)
        dec (e/const' (nm "instDecidableEqNat") [])
        cid (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)
        custs (e/fvar 5001) ords (e/fvar 5002)
        lctx {5001 {:name "custs" :type listNN} 5002 {:name "ords" :type listNN}}
        join (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid custs ords)
        amount (e/lam "p" PJ (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                                     (e/app* (e/const' (nm "Prod.snd") [z z]) NN NN (e/bvar 0))) :default)]
    {:join join :PJ PJ :N N :amount amount :lctx lctx :listNN listNN :custs-id 5001 :ords-id 5002}))

(defn- compile-fn [{:keys [listNN custs-id ords-id]} t]
  (let [t1 (e/abstract1 t ords-id) ly (e/lam "ords" listNN t1 :default)
        t2 (e/abstract1 ly custs-id) lx (e/lam "custs" listNN t2 :default)]
    (eval (a/ansatz->clj (a/env) lx []))))

(def ^:private CUSTS [[1 10] [2 20] [3 30]])
(def ^:private ORDS  [[1 100] [1 200] [2 50] [3 5] [3 5]])  ; Σ amount = 360, #pairs = 5

(deftest consumer-aware-unified-plan
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [{:keys [join PJ N amount] :as D} (build)
          lctx (:lctx D)
          sz {5001 1000 5002 1000}
          run (fn [t] (((compile-fn D t) CUSTS) ORDS))
          p-count (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ :sink {:kind :count} :sizes sz)
          p-sum   (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ
                                     :sink {:kind :sum :value-fn amount :value-type N} :sizes sz)
          p-vec   (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ :sink {:kind :vector} :sizes sz)]

      (testing "the SINK alone drives the plan (consumer-awareness, gated by the certificate)"
        (is (:verified? p-count) "count plan certified ≡ naive")
        (is (some? (:route p-count)) "order-invariant count sink → a join strategy fired")
        (is (:verified? p-sum) "sum plan certified ≡ naive")
        (is (some? (:route p-sum)) "order-invariant sum sink → aggregation-through-join fired")
        (is (:verified? p-vec) "vector plan certified ≡ naive")
        (is (nil? (:route p-vec)) "order-PRESERVING vector sink → NO order-destroying rewrite")
        (is (:order-invariant? p-count))
        (is (not (:order-invariant? p-vec))))

      (testing "every certified plan executes to the naive answer"
        (is (= 5   (long (run (:term p-count)))) "count = #join pairs")
        (is (= 360 (long (run (:term p-sum))))   "sum = Σ amount")
        (is (= 5   (count (run (:term p-vec))))  "vector = the 5 join pairs (order preserved)"))

      (testing "#1 order-invariance derived from a COMMUTATIVITY certificate, not a hardcoded set"
        ;; a sum whose monoid is NOT commutative (order matters) must be treated as order-preserving —
        ;; even though it's a fold. The hardcoded {count sum group set} would wrongly reorder it.
        (let [p-noncomm (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ
                                           :sink {:kind :sum :value-fn amount :value-type N
                                                  :commutative? false} :sizes sz)]
          (is (plan/order-invariant? {:kind :sum}) "default sum monoid (Nat.add) is commutative")
          (is (plan/order-invariant? {:kind :sum :monoid {:laws {:comm 'Nat.add_comm}}}) "explicit comm proof")
          (is (not (plan/order-invariant? {:kind :sum :commutative? false})) "non-comm sum → order-matters")
          (is (not (plan/order-invariant? {:kind :concat})) "concat/append → order-sensitive")
          (is (not (:order-invariant? p-noncomm)))
          (is (empty? (:rewrites p-noncomm)) "non-commutative sink → no order-destroying rewrite attempted"))))))

;; #6 — the inductive⇄coinductive unification: ONE unified-plan entry plans both a materialized source
;; (exact size, datahike/stratum-style) and a live STREAM (a forked window sample → measured selectivity,
;; re-measured under drift). Both feed the same certified optimize-cost.
(deftest coinductive-oracle-stream-sampling
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [N (e/const' (nm "Nat") [])
          listN (e/app (e/const' (nm "List") [z]) N)
          source (e/fvar 5003)
          lctx {5003 {:name "src" :type listN}}
          p (e/lam "x" N (e/app* (e/const' (nm "Nat.blt") []) (e/lit-nat 50) (e/bvar 0)) :default)  ; x > 50
          filt (e/app* (e/const' (nm "List.filter") [z]) N p source)                                 ; filter (>50) src
          plan-with (fn [src] (plan/unified-plan (a/env) filt :lctx lctx :elem-type N
                                                 :sink {:kind :count} :sources {5003 src}))
          p-mat (plan-with {:nature :materialized :size 1000})            ; inductive: exact size
          p-w1  (plan-with {:nature :stream :sample [10 20 30 40 45]})    ; coinductive window 1: none > 50
          p-w2  (plan-with {:nature :stream :sample [60 70 80 90 99]})]   ; window 2 (drift): all > 50
      (testing "one entry plans both source natures; every plan certified ≡ naive"
        (is (:verified? p-mat)) (is (:verified? p-w1)) (is (:verified? p-w2)))
      (testing "the coinductive oracle MEASURES the stream window's selectivity; drift re-measures"
        (let [k (first (keys (:selectivity p-w1)))]
          (is (some? k) "the filter predicate was measured against the window sample")
          (is (< (double (get (:selectivity p-w1) k)) 0.5) "window 1 (none>50) → low selectivity")
          (is (> (double (get (:selectivity p-w2) k)) 0.5) "window 2 (all>50) → high (the distribution drifted)")
          (is (not= (:selectivity p-w1) (:selectivity p-w2)) "the plan re-adapts to the drifted window")))
      (testing "the materialized source plans from exact sizes, not a sample"
        (is (nil? (:selectivity p-mat)) "no stream sample → no measured profile (inductive/exact path)")))))

;; #4 — raster's Map→Reduce lesson, certified: a SCALAR sink (count/sum) over (map f …) must never
;; materialize the intermediate list. This falls out of the existing foldl_map fusion once the sink is
;; folded in — the terminal op drives the whole loop to fuse (whole-stage-codegen toward the sink).
(deftest sink-driven-fusion
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [N (e/const' (nm "Nat") [])
          listN (e/app (e/const' (nm "List") [z]) N)
          source (e/fvar 5004)
          lctx {5004 {:name "src" :type listN}}
          g (e/lam "x" N (e/app (e/const' (nm "Nat.succ") []) (e/bvar 0)) :default)   ; λx. x+1
          mapped (e/app* (e/const' (nm "List.map") [z z]) N N g source)               ; map (+1) src
          mentions-map? (fn [t] (boolean (re-find #"List\.map" (ansatz.kernel.expr/->string t))))
          p-count (plan/unified-plan (a/env) mapped :lctx lctx :elem-type N :sink {:kind :count} :sizes {5004 100})
          p-sum   (plan/unified-plan (a/env) mapped :lctx lctx :elem-type N
                                     :sink {:kind :sum :value-type N} :sizes {5004 100})]
      (testing "a scalar sink over (map f) fuses the map away — no intermediate list materialized"
        (is (mentions-map? mapped) "the naive pipeline builds the mapped list")
        (is (:verified? p-count))
        (is (not (mentions-map? (:term p-count))) "count over (map f) → fused, intermediate dropped")
        (is (:verified? p-sum))
        (is (not (mentions-map? (:term p-sum)))  "sum over (map f) → fused, intermediate dropped")))))

;; #5 — :limit / top-n sink (stratum's early-termination lesson). A :limit n sink folds to List.take n.
;; It is ORDER-SENSITIVE (keeps the first n), so the certificate correctly forbids any reorder; and the
;; take can fuse through a map (List.take_map) so only n elements are produced — early termination.
(deftest limit-sink-early-termination
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [N (e/const' (nm "Nat") [])
          listN (e/app (e/const' (nm "List") [z]) N)
          source (e/fvar 5005)
          lctx {5005 {:name "src" :type listN}}
          g (e/lam "x" N (e/app (e/const' (nm "Nat.succ") []) (e/bvar 0)) :default)
          mapped (e/app* (e/const' (nm "List.map") [z z]) N N g source)
          run (fn [t] ((eval (a/ansatz->clj (a/env) (e/lam "src" listN (e/abstract1 t 5005) :default) [])) [10 20 30 40 50]))
          p-lim (plan/unified-plan (a/env) mapped :lctx lctx :elem-type N :sink {:kind :limit :n 2} :sizes {5005 1000})]
      (testing ":limit is order-SENSITIVE (no reorder) and executes to the first n"
        (is (:verified? p-lim) "limit plan certified ≡ naive")
        (is (not (:order-invariant? p-lim)) "limit keeps the first n → order-sensitive, reorder forbidden")
        (is (= [11 21] (vec (run (:term p-lim)))) "first 2 of (map +1 [10 20 30 40 50])")))))

;; #7 — evaluation: the consumer-aware win, ATTRIBUTED via ablation on the SAME query. Plan count(join)
;; twice — reorder ALLOWED (sink known order-invariant) vs FORBIDDEN (order-blind) — and measure the cost
;; delta. Same answer either way (certified ≡ naive); the delta is exactly what knowing the consumer buys.
(deftest evaluation-ablation
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [{:keys [join PJ] :as D} (build) lctx (:lctx D) sz {5001 1000 5002 1000}
          aware (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ :sink {:kind :count} :sizes sz)
          ;; ablation: the SAME count query, but order-blind (pretend we don't know count ignores order)
          blind (opt/optimize-cost (a/env) (:wrapped aware) :lctx lctx :sizes sz :skip-reorder? true)]
      (testing "knowing the sink is order-invariant unlocks a strictly cheaper certified plan"
        (is (:verified? aware)) (is (:verified? blind))
        (is (some? (:route aware)) "consumer-aware → aggregation-through-join fired")
        ;; the optimizer gates on CARDINALITY (pipeline-cost), not op-count: the factored plan processes
        ;; O(|xs|+|ys|) not O(|xs|·|ys|), so its cardinality cost is far lower.
        (let [ca (double (cost/pipeline-cost (:term aware) {:sizes sz}))
              cb (double (cost/pipeline-cost (:term blind) {:sizes sz}))]
          (is (< ca cb) "consumer-aware (factored) plan has strictly lower cardinality cost")
          (println (format "  #7 ABLATION — count(join), 1k×1k cardinality cost: consumer-aware %.0f vs order-blind %.0f (%.1f×)"
                           ca cb (/ cb (max 1.0 ca)))))))))

;; #2 (coherent inspectable IR) + #3 (a/defn connection). describe gives the structured source→sink view;
;; and the consumer-aware path is the SAME optimize-cost that a/defn's optimize-body runs — so a relational
;; a/defn whose body ends in a count/sum (consumer IN the body) is already consumer-aware; unified-plan
;; generalizes that to EXTERNAL sinks declared on the query.
(deftest describe-and-adefn-connection
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [{:keys [join PJ] :as D} (build) lctx (:lctx D) sz {5001 1000 5002 1000}
          sources {5001 {:nature :materialized :size 1000} 5002 {:nature :materialized :size 1000}}
          p (plan/unified-plan (a/env) join :lctx lctx :elem-type PJ :sink {:kind :count} :sources sources :sizes sz)
          d (plan/describe p sources)]
      (testing "#2 describe: one inspectable source→sink view over the live lens (no field bolted on)"
        (is (= {5001 :materialized 5002 :materialized} (:sources d)))
        (is (= :count (:sink d)))
        (is (:order-invariant? d))
        (is (some? (:plan d)) "the optimized term reads back through the plan lens")
        (is (true? (:verified? d))))
      (testing "#3 a/defn connection: the count consumer in-body factors via the SAME optimize-cost"
        ;; (:wrapped p) = count(join) is exactly the shape an a/defn body `(count (join …))` produces;
        ;; optimize-body calls optimize-cost, so a/defn inherits this consumer-aware factoring in-body.
        (let [via-body (opt/optimize-cost (a/env) (:wrapped p) :lctx lctx :sizes sz)]
          (is (:verified? via-body))
          (is (some? (get-in via-body [:physical :strategy])) "in-body count consumer → factored, like unified-plan"))))))
