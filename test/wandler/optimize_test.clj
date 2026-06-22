(ns wandler.optimize-test
  "The verified optimizer's certify layer: simp-driven fusion over a pipeline
   kernel term returns a rewritten term + a kernel-checked proof orig = result.
   Term-as-IR; the independent `verified?` gate must hold. Gated on an Init env."
  (:require [wandler.core]
            [ansatz.core :as a]
            [wandler.optimize :as opt]
            [wandler.surface.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

(deftest pipeline-cost-models-cardinality
  ;; The cost that drives the search GATE counts elements PROCESSED, not ops.
  ;; No kernel/Init env needed — it's a pure walk over the term structure.
  (let [nat (e/const' (nm "Nat") [])
        prodNN (e/app* (e/const' (nm "Prod") [z z]) nat nat)
        deceq (e/const' (nm "instDecidableEqNat") [])
        pp (e/fvar 1) kf (e/fvar 2) lf (e/fvar 3) ys (e/fvar 4) xs (e/fvar 5)
        predPair (e/lam "pr" prodNN (e/app pp (e/app* (e/const' (nm "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
        join (fn [l] (e/app* (e/const' (nm "Map.join") []) nat nat nat deceq kf lf l ys))
        filt (fn [pred l] (e/app* (e/const' (nm "List.filter") [z]) prodNN pred l))
        filtN (fn [l] (e/app* (e/const' (nm "List.filter") [z]) nat pp l))
        ;; filter (p∘fst) (join xs ys)  vs  join (filter p xs) ys
        unpushed (filt predPair (join xs))
        pushed   (join (filtN xs))]
    ;; filtering BEFORE the join is cheaper (smaller join input)
    (is (< (opt/pipeline-cost pushed) (opt/pipeline-cost unpushed))
        "filter-before-join has lower cardinality cost")
    ;; SOAC-count is the SAME for both (the gate that used to stall)
    (is (= (opt/soac-cost pushed) (opt/soac-cost unpushed))
        "op-count can't distinguish them — why the search needs pipeline-cost")
    ;; a measured/refinement profile can override per-predicate selectivity
    (let [cheap (opt/pipeline-cost unpushed {:selectivity {(e/->string predPair) 0.01}})
          dear  (opt/pipeline-cost unpushed {:selectivity {(e/->string predPair) 0.99}})]
      (is (number? cheap)) (is (number? dear)))))

(deftest fusion-rewrites-are-kernel-certified
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [env (a/env)
            nat (e/const' (nm "Nat") [])
            succ (e/const' (nm "Nat.succ") [])
            listNat (e/app (e/const' (nm "List") [z]) nat)
            xs (e/fvar 70001)
            lctx {70001 {:name "xs" :type listNat}}
            mapp (fn [f l] (e/app* (e/const' (nm "List.map") [z z]) nat nat f l))
            foldl (fn [s i l] (e/app* (e/const' (nm "List.foldl") [z z]) nat nat s i l))
            ;; map∘map and foldl∘map pipelines (abstract over xs)
            t1 (mapp succ (mapp succ xs))
            t2 (foldl (e/const' (nm "Nat.add") []) (e/lit-nat 0) (mapp succ xs))
            r1 (opt/optimize env t1 :lctx lctx)
            r2 (opt/optimize env t2 :lctx lctx)]
        ;; each fused (the term changed) and the rewrite carries a real proof…
        (is (:changed? r1))
        (is (:changed? r2))
        (is (some? (:proof r1)))
        (is (some? (:proof r2)))
        ;; …that INDEPENDENTLY kernel-checks orig = result
        (is (true? (:verified? r1)))
        (is (true? (:verified? r2)))
        ;; map∘map collapsed to a single map; the intermediate list is gone
        (let [[h _] (e/get-app-fn-args (:term r1))]
          (is (= "List.map" (name/->string (e/const-name h)))))))
    (do (println "SKIP fusion-rewrites-are-kernel-certified: no Init env") (is true))))

(deftest verified-rewrite-rejects-bogus-proof
  ;; The SOUNDNESS GATE must REJECT a proof that does not certify orig = term.
  ;; This is the property that protects every adopted rewrite: a lenient inferType
  ;; would silently accept ill-typed / wrong-claim proofs (see lenient-check-audit);
  ;; verified-rewrite? now runs the authoritative check-constant.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [env (a/env)
            nat (e/const' (nm "Nat") [])
            succ (e/const' (nm "Nat.succ") [])
            listNat (e/app (e/const' (nm "List") [z]) nat)
            xs (e/fvar 70011)                       ;; FREE var → map∘map xs is NOT def-eq to xs
            lctx {70011 {:name "xs" :type listNat}}
            mapp (fn [f l] (e/app* (e/const' (nm "List.map") [z z]) nat nat f l))
            t1 (mapp succ (mapp succ xs))
            refl-xs (e/app* (e/const' (nm "Eq.refl") [(lvl/succ z)]) listNat xs)]
        ;; the genuine fusion verifies …
        (is (true? (:verified? (opt/optimize env t1 :lctx lctx))))
        ;; … but a WRONG claim (t1 = xs, "proved" by xs = xs) must be rejected,
        ;; because map succ (map succ xs) is not definitionally xs for a free xs.
        (is (false? (opt/verified-rewrite? env t1 {:term xs :proof refl-xs} :lctx lctx))
            "wrong rewrite with a non-certifying proof is rejected")
        ;; a structurally malformed proof term is also rejected (not accepted/throwing)
        (is (false? (opt/verified-rewrite? env t1 {:term xs :proof (e/const' (nm "Nat.zero") [])} :lctx lctx))
            "ill-typed proof term is rejected")))
    (do (println "SKIP verified-rewrite-rejects-bogus-proof: no Init env") (is true))))

(deftest three-stage-pipeline-deforests-to-one-pass
  ;; sum ∘ map succ ∘ filter (2≤·) — a realistic map/filter/reduce pipeline —
  ;; deforests to a SINGLE foldl (stream fusion), kernel-verified, and the
  ;; optimized runtime matches the unoptimized one AND native Clojure.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [env (a/env)
            nat (e/const' (nm "Nat") [])
            listNat (e/app (e/const' (nm "List") [z]) nat)
            lctx {70001 {:name "xs" :type listNat}}
            pred (e/lam "x" nat (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 2) (e/bvar 0)) :default)
            filt (e/app* (e/const' (nm "List.filter") [z]) nat pred (e/fvar 70001))
            mapped (e/app* (e/const' (nm "List.map") [z z]) nat nat (e/const' (nm "Nat.succ") []) filt)
            term (e/app* (e/const' (nm "List.foldl") [z z]) nat nat (e/const' (nm "Nat.add") []) (e/lit-nat 0) mapped)
            r (opt/optimize env term :lctx lctx)
            [h inner-args] (e/get-app-fn-args (:term r))
            mkfn (fn [t] (eval (a/ansatz->clj env (e/lam "xs" listNat (e/abstract1 t 70001) :default) [])))
            orig-fn (mkfn term) opt-fn (mkfn (:term r))
            sample (list 1 2 3 4 5 6)
            native (reduce + 0 (mapv inc (filterv #(<= 2 %) sample)))]
        ;; one foldl, nothing left inside it (no List.map / List.filter operand)
        (is (= "List.foldl" (name/->string (e/const-name h))))
        (is (not-any? #(and (e/app? %)
                            (let [[ih _] (e/get-app-fn-args %)]
                              (and (e/const? ih)
                                   (#{"List.map" "List.filter"} (name/->string (e/const-name ih))))))
                      inner-args))
        (is (true? (:verified? r)))
        ;; runtime: optimized = unoptimized = native Clojure
        (is (= 25N (orig-fn sample)))
        (is (= 25N (opt-fn sample)))
        (is (= 25 native))))
    (do (println "SKIP three-stage-pipeline-deforests-to-one-pass: no Init env") (is true))))

(deftest a-defn-optimize-flag-wires-through
  ;; With wandler.core/*optimize* on, idiomatic surface code is fused-with-proof at define
  ;; time; the optimized runtime must compute exactly the unoptimized + native result.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn opt-pipe-plain [xs :- (List Nat)] Nat
                 (reduce + 0 (mapv Nat.succ (filterv (fn [x] (Nat.ble 2 x)) xs)))))
        (binding [wandler.core/*optimize* true]
          (eval '(ansatz.core/defn opt-pipe-fused [xs :- (List Nat)] Nat
                   (reduce + 0 (mapv Nat.succ (filterv (fn [x] (Nat.ble 2 x)) xs)))))))
      (let [sample (apply list (range 1 20))
            native (reduce + 0 (mapv inc (filterv #(<= 2 %) (range 1 20))))]
        (is (= 207N ((resolve 'opt-pipe-plain) sample)))
        (is (= 207N ((resolve 'opt-pipe-fused) sample)))
        (is (= 207 native))))
    (do (println "SKIP a-defn-optimize-flag-wires-through: no Init env") (is true))))

(deftest relational-rewrite-registers-and-certifies
  ;; The rule-from-theorem loop is rule-agnostic: a relational/reordering law
  ;; registered via :extra-lemmas becomes a certified optimizer rewrite, just like
  ;; the fusion laws. Here filter_map pushes a filter before a map, kernel-verified.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [env (a/env)
            nat (e/const' (nm "Nat") [])
            listNat (e/app (e/const' (nm "List") [z]) nat)
            lctx {70001 {:name "xs" :type listNat}}
            p (e/lam "y" nat (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 5) (e/bvar 0)) :default)
            mapped (e/app* (e/const' (nm "List.map") [z z]) nat nat (e/const' (nm "Nat.succ") []) (e/fvar 70001))
            term (e/app* (e/const' (nm "List.filter") [z]) nat p mapped)
            r (opt/optimize env term :lctx lctx :extra-lemmas (vec opt/cost-rewrites))
            [h _] (e/get-app-fn-args (:term r))]
        (is (:changed? r))
        (is (true? (:verified? r)))
        ;; filter(map …) became map(filter …) — filter now runs before the map
        (is (= "List.map" (name/->string (e/const-name h))))))
    (do (println "SKIP relational-rewrite-registers-and-certifies: no Init env") (is true))))

(deftest cost-directed-search-adopts-rewrite-when-cheaper
  ;; map∘filter∘map: confluent fusion alone can't fuse the two maps (filter between).
  ;; The cost driver adopts filter_map (a cost-rewrite) ONLY because it lowers the
  ;; SOAC count (enabling map_map), and the adopted step is kernel-certified.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [env (a/env)
            nat (e/const' (nm "Nat") [])
            listNat (e/app (e/const' (nm "List") [z]) nat)
            lctx {70001 {:name "xs" :type listNat}}
            succ (e/const' (nm "Nat.succ") [])
            mp (fn [l] (e/app* (e/const' (nm "List.map") [z z]) nat nat succ l))
            p (e/lam "y" nat (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 3) (e/bvar 0)) :default)
            flt (fn [l] (e/app* (e/const' (nm "List.filter") [z]) nat p l))
            p4 (mp (flt (mp (e/fvar 70001))))
            conf (opt/optimize env p4 :lctx lctx)
            costr (opt/optimize-cost env p4 :lctx lctx)
            mkfn (fn [t] (eval (a/ansatz->clj env (e/lam "xs" listNat (e/abstract1 t 70001) :default) [])))
            sample (apply list (range 0 12))
            native (mapv inc (filterv #(<= 3 %) (mapv inc (range 0 12))))]
        ;; confluent stalls at 3 SOAC ops; cost search gets to 2 by adopting filter_map
        (is (= 3 (opt/soac-cost (:term conf))))
        (is (= 2 (:cost costr)))
        (is (= ["List.filter_map"] (:rewrites costr)))
        (is (true? (:verified? costr)))
        (is (= native (vec ((mkfn (:term costr)) sample))))))
    (do (println "SKIP cost-directed-search-adopts-rewrite-when-cheaper: no Init env") (is true))))

(deftest measured-selectivity-refines-the-cost
  ;; The JIT/profile hook: MEASURE a predicate's pass-rate on a real workload and
  ;; feed it to the cost model. A wrong estimate only changes which (certified)
  ;; plan is picked — never the result. Needs an Init env to compile the predicate.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [nat (e/const' (nm "Nat") [])
            succ (e/const' (nm "Nat.succ") [])
            pred (e/lam "x" nat (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 900) (e/bvar 0)) :default)
            ;; map succ (filter (x>=900) xs) — the map consumes the filter's OUTPUT
            term (e/app* (e/const' (nm "List.map") [z z]) nat nat succ
                         (e/app* (e/const' (nm "List.filter") [z]) nat pred (e/fvar 90001)))
            workload (range 1000)                         ; x>=900 ⇒ exactly 10% pass
            measured (wandler.core/measure-selectivity (a/env) pred workload)
            profile  (wandler.core/profile-selectivity (a/env) term workload)]
        ;; measured rate is the real 0.1, not the static 0.33 heuristic
        (is (< 0.09 measured 0.11) "measured selectivity ≈ 0.1")
        (is (= 1 (count profile)) "profile has the one filter predicate")
        ;; with the measured profile the downstream map's cost is lower (and accurate):
        ;; it really processes ~100 elements, not the heuristic ~330
        (is (< (opt/pipeline-cost term {:selectivity profile})
               (opt/pipeline-cost term))
            "measured cost < static-heuristic cost")))
    (do (println "SKIP measured-selectivity-refines-the-cost: no Init env") (is true))))

(deftest closed-measure-replan-loop
  ;; #2: the CLOSED measure→replan loop (wandler.core/optimize-measured) in ONE call — measure the
  ;; filter's real selectivity on a workload, re-optimize with it, kernel-RE-CERTIFIED.
  ;; The verified JIT: the plan adapts to the observed workload and stays sound.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (let [nat (e/const' (nm "Nat") [])
            succ (e/const' (nm "Nat.succ") [])
            pred (e/lam "x" nat (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 900) (e/bvar 0)) :default)
            term (e/app* (e/const' (nm "List.map") [z z]) nat nat succ
                         (e/app* (e/const' (nm "List.filter") [z]) nat pred (e/fvar 90001)))
            lctx {90001 {:name "xs" :type (e/app (e/const' (nm "List") [z]) nat)}}
            workload (range 1000)                          ; x>=900 ⇒ ~10% pass
            res (wandler.core/optimize-measured (a/env) term workload :lctx lctx :compare? true)]
        ;; the loop measured the real ~0.1 selectivity into its profile
        (is (= 1 (count (:profile res))) "measured one filter predicate")
        (is (< 0.09 (first (vals (:profile res))) 0.11) "profile carries the measured ~0.1 rate")
        ;; and produced a kernel-CERTIFIED plan — adapting to data can't make it unsound
        (is (:verified? res) "the measured-replanned plan is kernel-certified")
        (is (:verified? (:static res)) "the static-plan baseline is also certified")))
    (do (println "SKIP closed-measure-replan-loop: no Init env") (is true))))

(deftest explain-reports-the-optimization
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]                 ; *optimize* is on by default
        (eval '(ansatz.core/defn ex-fused [xs :- (List Nat)] Nat
                 (reduce + 0 (mapv Nat.succ (filterv (fn [x] (Nat.ble 3 x)) xs)))))
        (eval '(ansatz.core/defn ex-mfm [xs :- (List Nat)] (List Nat)
                 (mapv Nat.succ (filterv (fn [x] (Nat.ble 3 x)) (mapv Nat.succ xs)))))
        (eval '(ansatz.core/defn ex-noop [x :- Nat] Nat (Nat.add x x))))
      ;; a fusible pipeline is rewritten + verified
      (is (= {:changed? true :verified? true :rewrites []} (select-keys (wandler.core/explain 'ex-fused) [:changed? :verified? :rewrites])))
      ;; map∘filter∘map adopts the map+filter→filterMap cost-rewrite (a single-pass win on the
      ;; inner map∘filter: map→filter→map ⇒ filterMap→map, kernel-certified)
      (is (= {:changed? true :verified? true :rewrites ["List.map_filter_filterMap"]} (select-keys (wandler.core/explain 'ex-mfm) [:changed? :verified? :rewrites])))
      ;; a non-pipeline body is left untouched (skipped cheaply)
      (is (= {:changed? false :verified? true :rewrites []} (select-keys (wandler.core/explain 'ex-noop) [:changed? :verified? :rewrites]))))
    (do (println "SKIP explain-reports-the-optimization: no Init env") (is true))))

(deftest optimize-on-by-default-differential
  ;; A battery of realistic pipelines, *optimize* ON by default: the verified-fused
  ;; runtime must equal native Clojure for every shape/terminal.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (coll/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn d-sum  [xs :- (List Nat)] Nat (reduce + 0 xs)))
        (eval '(ansatz.core/defn d-fmf  [xs :- (List Nat)] Nat (reduce + 0 (mapv Nat.succ (filterv (fn [x] (Nat.ble 2 x)) xs)))))
        (eval '(ansatz.core/defn d-mff  [xs :- (List Nat)] Nat (reduce + 0 (filterv (fn [x] (Nat.ble 2 x)) (mapv Nat.succ xs)))))
        (eval '(ansatz.core/defn d-5map [xs :- (List Nat)] (List Nat) (mapv Nat.succ (mapv Nat.succ (mapv Nat.succ (mapv Nat.succ (mapv Nat.succ xs)))))))
        (eval '(ansatz.core/defn d-prod [xs :- (List Nat)] Nat (reduce * 1 (mapv Nat.succ xs)))))
      (let [in (apply list (range 0 20)) v (vec (range 0 20))]
        (is (= (reduce + 0 v) ((resolve 'd-sum) in)))
        (is (= (reduce + 0 (mapv inc (filterv #(<= 2 %) v))) ((resolve 'd-fmf) in)))
        (is (= (reduce + 0 (filterv #(<= 2 %) (mapv inc v))) ((resolve 'd-mff) in)))
        (is (= (mapv inc (mapv inc (mapv inc (mapv inc (mapv inc v))))) (vec ((resolve 'd-5map) in))))
        (is (= (reduce * 1 (mapv inc v)) ((resolve 'd-prod) in)))))
    (do (println "SKIP optimize-on-by-default-differential: no Init env") (is true))))
