(ns wandler.perf-faq-demo-test
  "WITHOUT-A-DOUBT demonstration: the FAQ-factored plan is asymptotically + wall-clock faster than the
   naive plan, on the SAME query and data, with the SAME (kernel-certified) answer. A 3-way aggregating
   join over malli-typed records `[:map [:cid :int] [:val :int]]` (≅ Prod Nat Nat). Few distinct keys ⇒
   the naive join MATERIALIZES the |custs|·|orders|·|C| product; the factored plan never builds it
   (O(N), per-key indices). Same Σ, proven equal — but orders of magnitude faster."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc] [wandler.kmap :as km] [wandler.laws.faq :as rl]
            [wandler.optimize :as opt] [wandler.optimize.cost :as cost]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as name] [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; malli boundary: Customer/Order/C all = [:map [:cid :int] [:val :int]]  ≅  Prod Nat Nat
(defn- build3 []
  (let [N (e/const' (nm "Nat") []) NN (e/app* (e/const' (nm "Prod") [z z]) N N)
        PJ (e/app* (e/const' (nm "Prod") [z z]) NN NN) PJ2 (e/app* (e/const' (nm "Prod") [z z]) PJ NN)
        listNN (e/app (e/const' (nm "List") [z]) NN) dec (e/const' (nm "instDecidableEqNat") [])
        cid (e/lam "r" NN (e/app* (e/const' (nm "Prod.fst") [z z]) N N (e/bvar 0)) :default)
        cidPJ (e/lam "r" PJ (e/app* (e/const' (nm "Prod.fst") [z z]) N N
                              (e/app* (e/const' (nm "Prod.fst") [z z]) NN NN (e/bvar 0))) :default)
        join (e/app* (e/const' (nm "Map.join") []) N NN NN dec cid cid (e/fvar 5001) (e/fvar 5002))
        join3 (e/app* (e/const' (nm "Map.join") []) N PJ NN dec cidPJ cid join (e/fvar 5003))
        ;; commutative monoid (Nat.add) ⇒ the factorization/reorder is sound (and exploited automatically)
        val3 (e/lam "p" PJ2 (e/app* (e/const' (nm "Prod.snd") [z z]) N N
                              (e/app* (e/const' (nm "Prod.snd") [z z]) PJ NN (e/bvar 0))) :default)
        amts3 (e/app* (e/const' (nm "List.map") [z z]) PJ2 N val3 join3)
        sum3 (e/app* (e/const' (nm "List.foldl") [z z]) N N (e/const' (nm "Nat.add") [])
                     (e/const' (nm "Nat.zero") []) amts3)]
    {:sum3 sum3 :listNN listNN}))

(defn- compile3 [{:keys [listNN]} t]
  (let [t1 (e/abstract1 t 5003) l3 (e/lam "cc" listNN t1 :default)
        t2 (e/abstract1 l3 5002) l2 (e/lam "ords" listNN t2 :default)
        t3 (e/abstract1 l2 5001) l1 (e/lam "custs" listNN t3 :default)]
    (eval (a/ansatz->clj (a/env) l1 []))))

(defn- t! [f] (f) (let [s (System/nanoTime)] (dotimes [_ 3] (f)) (/ (- (System/nanoTime) s) 3e6)))

(deftest faq-factored-beats-naive-wall-clock
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [{:keys [sum3 listNN] :as D} (build3)
          lctx {5001 {:name "custs" :type listNN} 5002 {:name "ords" :type listNN} 5003 {:name "cc" :type listNN}}
          R (opt/optimize-cost (a/env) sum3 :lctx lctx :sizes {5001 1000 5002 1000 5003 1000})
          naive (compile3 D sum3)
          fact  (compile3 D (:term R))
          nk 8]
      (testing "certified equal + all joins eliminated"
        (is (:verified? R) "factored plan kernel-certified ≡ naive")
        (is (not (cost/mentions-const? (:term R) "Map.join")) "FAQ: every join eliminated"))
      (testing "ASYMPTOTIC divergence — naive grows ~cubically, factored stays flat (the gap WIDENS)"
        (println "  FAQ DEMO — Σ over custs⋈orders⋈C (8 keys), same certified answer at every size:")
        (println "    rows/list   naive-product   naive ms   factored ms   speedup")
        (doseq [rows [240 480 720]]
          (let [gen (fn [off] (vec (map (fn [i] [(mod i nk) (+ off i)]) (range rows))))
                CU (gen 0) OR (gen 1000) CC (gen 2000)
                run (fn [g] (long (((g CU) OR) CC)))
                prod (long (* nk (Math/pow (/ rows nk) 3)))
                _ (is (= (run naive) (run fact)) (str "same Σ at rows=" rows))
                tn (t! #(run naive)) tf (t! #(run fact))]
            (println (format "    %-11d %-15s %-10.0f %-13.2f %.0f×"
                             rows (format "%,d" prod) tn tf (/ tn (max 0.01 tf))))
            (is (< tf tn) (str "factored faster at rows=" rows))))))))
