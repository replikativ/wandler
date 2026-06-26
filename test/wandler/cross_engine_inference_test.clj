(ns wandler.cross-engine-inference-test
  "JOINT INFERENCE over a cross-engine compute graph. A discrete factor graph / Bayesian chain
   Region — Channel — HighValue whose two factors live in DIFFERENT engines:

     φ₁(Channel, Region)   — a customer potential, sourced from a datahike :memory database
     φ₂(Channel, HighValue) — an order/outcome potential, sourced from a stratum columnar dataset

   The marginal query P(HighValue) sums out the nuisance variables Region and Channel:

       g(h)  =  Σ_R Σ_C  φ₁(C,R) · φ₂(C,h)              P(H=h) = g(h) / Σ_h' g(h')

   VARIABLE ELIMINATION = the aggregation-through-join factorization (Map.foldl_join_factor) we
   already proved, read at the sum-product semiring: the factors share Channel, so Σ over their
   product is a Σ over a JOIN on Channel — which FACTORIZES, aggregating each channel's contribution
   per-bucket and NEVER materializing the |φ₁|·|φ₂| (Region×Channel×HighValue) joint. The kernel proof
   that `factored ≡ naive` IS the variable-elimination certificate, and it is engine-agnostic at the
   source boundary, so the SAME certificate covers factors drawn from two different databases.

   Count-weighted factors keep the proof at Nat (the structure is what's certified; the normalization
   to a probability is the trusted numeric step — the FinDist architecture). The marginal is
   cross-validated against a brute-force enumeration of the full joint.

   Optional: needs the :datahike + :stratum engines on the classpath AND the full Init env. Skips
   cleanly otherwise. Run live:
     clj -M:local-ansatz:datahike:stratum:test -n wandler.cross-engine-inference-test"
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc] [wandler.kmap :as km] [wandler.laws.faq :as rl]
            [wandler.optimize :as opt] [wandler.optimize.cost :as cost]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as name] [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(defn- c' [s & ls] (e/const' (nm s) (vec ls)))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)

;; ── optional engine handles (nil if the engine isn't on the classpath) ───────────────────────────────
(defn- rr [sym] (try (requiring-resolve sym) (catch Throwable _ nil)))
(def ^:private dh-create  (rr 'datahike.api/create-database))
(def ^:private dh-delete  (rr 'datahike.api/delete-database))
(def ^:private dh-exists? (rr 'datahike.api/database-exists?))
(def ^:private dh-connect (rr 'datahike.api/connect))
(def ^:private dh-transact (rr 'datahike.api/transact))
(def ^:private dh-q       (rr 'datahike.api/q))
(def ^:private st-q       (rr 'stratum.query/q))
(defn- engines? [] (and dh-q st-q @test-env/init-full-env))

;; ── projections over nested Prods ────────────────────────────────────────────────────────────────────
(defn- prod [a b] (e/app* (c' "Prod" z z) a b))
(defn- listOf [t] (e/app (c' "List" z) t))
(defn- pfst [a b x] (e/app* (c' "Prod.fst" z z) a b x))
(defn- psnd [a b x] (e/app* (c' "Prod.snd" z z) a b x))

;; ── the (engine-agnostic) factored marginal plan ─────────────────────────────────────────────────────
;; φ₁ row : Prod C (Prod R W)   (channel, (region, weight))   — keyed on channel = fst
;; φ₂ row : Prod C (Prod H W)   (channel, (highvalue, weight)) — keyed on channel = fst
;; g = Σ over (φ₁ ⋈_C φ₂) of  w₁·w₂  =  Σ_R Σ_C φ₁(C,R)·φ₂(C,·)  — Region & Channel summed out (VE).
(defn- build []
  (let [N (c' "Nat") RW (prod N N) HW (prod N N)
        F1 (prod N RW) F2 (prod N HW)
        PJ (prod F1 F2)
        dec (c' "instDecidableEqNat")
        kf (e/lam "a" F1 (pfst N RW (e/bvar 0)) :default)   ; φ₁.channel
        lf (e/lam "b" F2 (pfst N HW (e/bvar 0)) :default)   ; φ₂.channel
        join (e/app* (c' "Map.join") N F1 F2 dec kf lf (e/fvar 7001) (e/fvar 7002))
        ;; ⊗ : the factor product — w₁ (from φ₁ payload) · w₂ (from φ₂ payload)
        wprod (e/lam "p" PJ
                (e/app* (c' "Nat.mul")
                        (psnd N N (psnd N RW (pfst F1 F2 (e/bvar 0))))    ; w₁
                        (psnd N N (psnd N HW (psnd F1 F2 (e/bvar 0))))) :default) ; w₂
        weighted (e/app* (c' "List.map" z z) PJ N wprod join)
        ;; ⊕ : marginalize — Σ over the weighted join
        g (e/app* (c' "List.foldl" z z) N N (c' "Nat.add") (c' "Nat.zero") weighted)]
    {:g g :F1 F1 :F2 F2
     :lctx {7001 {:name "phi1" :type (listOf F1)} 7002 {:name "phi2" :type (listOf F2)}}}))

(defn- compile2 [{:keys [F1 F2]} t]
  (let [t1 (e/abstract1 t 7002) l2 (e/lam "phi2" (listOf F2) t1 :default)
        t2 (e/abstract1 l2 7001) l1 (e/lam "phi1" (listOf F1) t2 :default)]
    (eval (a/ansatz->clj (a/env) l1 []))))

;; ── the factor potentials (small, explicit — the "learned" tables) ───────────────────────────────────
;; channels {0,1}, regions {0,1}, highvalue {0,1}.  φ₁ in datahike, φ₂ in stratum.
(def ^:private phi1-rows ;; (channel, region, weight)
  [[0 0 3] [0 1 1] [1 0 1] [1 1 2]])
(def ^:private phi2-rows ;; (channel, highvalue, weight)
  [[0 0 1] [0 1 4] [1 0 3] [1 1 1]])

;; runtime record rep matching F1/F2 = [c [x w]]
(defn- ->f1 [[c r w]] [(long c) [(long r) (long w)]])
(defn- ->f2 [[c h w]] [(long c) [(long h) (long w)]])

(defn- fresh-datahike-phi1! [scale]
  (let [cfg {:store {:backend :memory :id #uuid "00000000-0000-0000-0000-0000facc0001"}
             :schema-flexibility :read :keep-history? false}]
    (when (dh-exists? cfg) (dh-delete cfg))
    (dh-create cfg)
    (dh-transact (dh-connect cfg)
                 (vec (for [k (range scale) [c r w] phi1-rows]
                        {:phi1id (+ (* 100 k) (* 4 c) r) :channel c :region r :w w})))
    {:engine :datahike :cfg cfg}))

(defn- read-phi1 [{:keys [cfg]}]
  (->> (dh-q '[:find ?c ?r ?w :where [?e :channel ?c] [?e :region ?r] [?e :w ?w]] (deref (dh-connect cfg)))
       (map (fn [[c r w]] [(long c) (long r) (long w)]))))

(defn- stratum-phi2-reader [scale h-filter]
  (let [rows (vec (for [_ (range scale) row phi2-rows
                        :when (or (nil? h-filter) (= h-filter (nth row 1)))]
                    row))]
    {:engine :stratum
     :reader #(st-q {:from {:channel   (long-array (map first rows))
                            :highvalue (long-array (map second rows))
                            :w         (long-array (map last rows))}
                     :select [:channel :highvalue :w]})}))

(defn- read-phi2 [leaf]
  (->> ((:reader leaf)) (map (fn [{:keys [channel highvalue w]}] [(long channel) (long highvalue) (long w)]))))

;; brute-force ground truth: Σ over the full joint, optionally restricted to H=h*
(defn- brute [p1 p2 h*]
  (reduce + 0 (for [[c1 _r w1] p1 [c2 h w2] p2 :when (and (= c1 c2) (or (nil? h*) (= h* h)))]
                (* w1 w2))))

;; ════════════════════════════════════════════════════════════════════════════════════════════════════
(deftest cross-engine-marginal-is-certified-variable-elimination
  (if-not (engines?)
    (is true "skipped — needs :datahike + :stratum engines and the full Init env")
    (let [{:keys [g lctx] :as D} (build)
          sz {7001 1000 7002 1000}
          r (opt/optimize-cost (a/env) g :lctx lctx :sizes sz)
          run (fn [t p1 p2] (long (((compile2 D t) (mapv ->f1 p1)) (mapv ->f2 p2))))]

      (testing "the VE step (sum out Region & Channel) is a kernel-certified factorization"
        (is (contains? (set (:rewrites r)) :fold-factor)
            "eliminating the shared variable = the aggregation-through-join factorization")
        (is (true? (:verified? r)) "factored ≡ naive — the variable-elimination certificate")
        (is (not (cost/mentions-const? (:term r) "Map.join"))
            "the φ₁·φ₂ (Region×Channel×HighValue) joint is never materialized")
        (is (< (double (cost/pipeline-cost (:term r) {:sizes sz}))
               (double (cost/pipeline-cost g {:sizes sz})))
            "cheaper than materializing the cross-engine joint"))

      (let [dh   (fresh-datahike-phi1! 1)
            p1   (read-phi1 dh)
            p2   (read-phi2 (stratum-phi2-reader 1 nil))
            p2h1 (read-phi2 (stratum-phi2-reader 1 1))
            p2h0 (read-phi2 (stratum-phi2-reader 1 0))]
        (testing "factors really came from two different engines"
          (is (= (set (map vec phi1-rows)) (set (map vec p1))) "φ₁ read from datahike")
          (is (= (set (map vec phi2-rows)) (set (map vec p2))) "φ₂ read from stratum"))

        (testing "the certified factored plan computes the same marginal weights as brute force"
          (is (= (brute p1 p2 nil)  (run (:term r) p1 p2))  "Z (partition) — naive == factored")
          (is (= (brute p1 p2 nil)  (run g        p1 p2))   "Z — naive plan agrees too")
          (is (= (brute p1 p2h1 1)  (run (:term r) p1 p2h1)) "g(H=1) via certified VE")
          (is (= (brute p1 p2h0 0)  (run (:term r) p1 p2h0)) "g(H=0) via certified VE"))

        (testing "the normalized marginal P(HighValue) is a valid distribution"
          (let [g1 (run (:term r) p1 p2h1) g0 (run (:term r) p1 p2h0) Z (+ g0 g1)
                p-high (/ (double g1) Z)]
            (is (= Z (run (:term r) p1 p2)) "g(0)+g(1) = Z (H partitions the joint)")
            (is (< 0.0 p-high 1.0) "P(H=1) is a probability")
            (println (format "  P(HighValue=yes) = %.4f  (g1=%d g0=%d Z=%d), cross-engine VE, certified"
                             p-high g1 g0 Z))))))))

;; ── timed: the VE win WIDENS with data size (naive joint grows ~|φ₁|·|φ₂|, factored stays linear) ─────
(deftest cross-engine-ve-scales
  (if-not (engines?)
    (is true "skipped — needs engines")
    (let [{:keys [g lctx] :as D} (build)
          r (opt/optimize-cost (a/env) g :lctx lctx :sizes {7001 1000 7002 1000})
          naive (compile2 D g) fact (compile2 D (:term r))
          time-ms (fn [f] (let [t0 (System/nanoTime)] (dotimes [_ 3] (f)) (/ (- (System/nanoTime) t0) 3.0 1e6)))]
      (is (:verified? r))
      (println "  scale  |φ₁|·|φ₂|     naive ms   factored ms   speedup")
      (doseq [scale [40 80 160]]
        (let [dh (fresh-datahike-phi1! scale)
              p1 (mapv ->f1 (read-phi1 dh))
              p2 (mapv ->f2 (read-phi2 (stratum-phi2-reader scale nil)))
              nm-fn #((naive p1) p2) ft-fn #((fact p1) p2)]
          (is (= (long (nm-fn)) (long (ft-fn))) "same Z at every scale")
          (let [tn (time-ms nm-fn) tf (time-ms ft-fn)]
            (println (format "  %-6d %-12d %-10.2f %-12.2f %.1f×"
                             scale (* (count p1) (count p2)) tn tf (/ tn (max tf 1e-3)))))))
      (is true))))
