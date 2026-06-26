(ns wandler.jit-pgo-test
  "Verified PGO across the problem types, on non-trivial synthetic data. For each query we measure cost
   params from a representative sample, jit-compile a CERTIFIED workload-tuned plan, then REPLAY the stored
   plan over MANY synthetic datasets (skewed / uniform / empty / large) asserting it equals the clojure.core
   ground truth every time AND re-verifies. The point: the plan tuned for the profiled workload is correct
   on ALL workloads (soundness is independent of the measurement), and the cache/replay is reliable across
   joins (FAQ), fusion, CSE, and deep pipelines."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.jit.pgo :as pgo]
            [wandler.jit.estimate :as est]
            [wandler.kmap :as km]
            [wandler.laws.faq :as rl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is use-fixtures]]))

(def ^:private z lvl/zero)
(defn- c [s] (e/const' (nm/from-string s) []))
(defn- setup [f]
  (when-let [k @test-env/init-full-env]
    (reset! a/ansatz-env k) (w/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; ── kernel-term builders over Nat ────────────────────────────────────────────
(def ^:private N (delay (c "Nat")))
(defn- idf  [] (e/lam "x" @N (e/bvar 0) :default))
(defn- sq   [] (e/lam "x" @N (e/app* (c "Nat.mul") (e/bvar 0) (e/bvar 0)) :default))
(defn- gt2  [] (e/lam "x" @N (e/app* (c "Nat.blt") (e/lit-nat 2) (e/bvar 0)) :default))
(defn- mul2 [] (e/lam "x" @N (e/app* (c "Nat.mul") (e/bvar 0) (e/lit-nat 2)) :default))
(defn- le   [] (e/lam "a" @N (e/lam "b" @N (e/app* (c "Nat.ble") (e/bvar 1) (e/bvar 0)) :default) :default))
(defn- fold+ [l] (e/app* (e/const' (nm/from-string "List.foldl") [z z]) @N @N (c "Nat.add") (c "Nat.zero") l))
(defn- mapN [f l] (e/app* (e/const' (nm/from-string "List.map") [z z]) @N @N f l))
(defn- filt [p l] (e/app* (e/const' (nm/from-string "List.filter") [z]) @N p l))
(defn- sort1 [l] (e/app* (e/const' (nm/from-string "List.mergeSort") [z]) @N l (le)))
(defn- listN [] (e/app (e/const' (nm/from-string "List") [z]) @N))

;; ── the PGO harness: jit-compile once (profiled), replay over many datasets ──
(defn- check [label term lctx params truth datasets]
  (let [art (pgo/jit-compile (a/env) term lctx :params params)]
    (is (:verified? art) (str label ": stored plan kernel-certified ≡ original"))
    (doseq [[i ds] (map-indexed vector datasets)]
      (is (= (long (truth ds)) (long (pgo/replay (a/env) art ds :reverify? (zero? i))))
          (str label " dataset#" i " (" (mapv count ds) "): replay = clojure.core ground truth")))
    art))

;; ── P1: aggregating JOIN (FAQ) — Σ of order-keys over (xs ⋈ ys on identity) ──
(deftest pgo-aggregating-join
  (when (ready?)
    (let [dec (c "instDecidableEqNat")
          NN  (e/app* (e/const' (nm/from-string "Prod") [z z]) @N @N)
          join (e/app* (c "Map.join") @N @N @N dec (idf) (idf) (e/fvar 1) (e/fvar 2))
          sndf (e/lam "p" NN (e/app* (e/const' (nm/from-string "Prod.snd") [z z]) @N @N (e/bvar 0)) :default)
          term (fold+ (e/app* (e/const' (nm/from-string "List.map") [z z]) NN @N sndf join))
          lctx {1 {:name "xs" :type (listN)} 2 {:name "ys" :type (listN)}}
          truth (fn [[xs ys]] (reduce + 0 (for [x xs y ys :when (= x y)] y)))
          ;; PROFILE on a skewed representative sample → measured ndv (few keys ⇒ big product ⇒ factorize)
          rep '(1 1 2 2 1 3)
          params {:sizes {1 1000.0 2 1000.0} :ndv (est/measure-ndv (a/env) (idf) rep)}
          datasets [['(1 1 2 2 1 3)   '(1 2 2 3 3 3)]           ; skewed
                    ['(1 2 3 4 5)     '(3 4 5 6 7)]             ; uniform, partial overlap
                    ['()              '(1 2 3)]                  ; empty left
                    ['(5)             '(5 5 5)]                  ; singleton ⋈ dup
                    [(range 40)       (map #(mod % 8) (range 60))]]]  ; non-trivial: 40 keys ⋈ 60 skewed
      (check "agg-join" term lctx params truth datasets))))

;; ── P2: transducer fusion — Σ x² over (filter (>2) xs) ──
(deftest pgo-transducer-fusion
  (when (ready?)
    (let [xs (e/fvar 1)
          term (fold+ (mapN (sq) (filt (gt2) xs)))
          lctx {1 {:name "xs" :type (listN)}}
          truth (fn [[w]] (reduce + 0 (map #(* % %) (filter #(< 2 %) w))))
          rep '(1 2 3 4 5 6 7 8)
          params {:selectivity (est/cost-params (a/env) term {:sample rep})}
          datasets [['(1 2 3 4 5 6)] ['()] ['(1 2)] ['(3 3 3 3)] [(range 50)] [(map #(mod % 5) (range 80))]]]
      ;; cost-params returns {:selectivity {...}} — flatten into params
      (check "transducer" term lctx {:selectivity (:selectivity (est/cost-params (a/env) term {:sample rep}))}
             truth datasets))))

;; ── P3: CSE over a shared barrier — (Σ sort xs) + (Σ map ×2 (sort xs)) ──
(deftest pgo-cse-shared-sort
  (when (ready?)
    (let [xs (e/fvar 1)
          term (e/app* (c "Nat.add") (fold+ (sort1 xs)) (fold+ (mapN (mul2) (sort1 xs))))
          lctx {1 {:name "xs" :type (listN)}}
          truth (fn [[w]] (+ (reduce + 0 (sort w)) (reduce + 0 (map #(* 2 %) (sort w)))))
          datasets [['(3 1 2)] ['()] ['(5)] ['(9 1 8 2 7 3)] [(reverse (range 30))] [(map #(mod (* 7 %) 13) (range 40))]]]
      (check "cse-sort" term lctx {:sizes {1 1000.0}} truth datasets))))

;; ── P4: deep pipeline (4 stages) — Σ (×2) over filter (<20) (×x over filter (>2)) ──
(deftest pgo-deep-pipeline
  (when (ready?)
    (let [xs (e/fvar 1)
          lt20 (e/lam "x" @N (e/app* (c "Nat.blt") (e/bvar 0) (e/lit-nat 20)) :default)
          term (fold+ (mapN (mul2) (filt lt20 (mapN (sq) (filt (gt2) xs)))))
          lctx {1 {:name "xs" :type (listN)}}
          truth (fn [[w]] (reduce + 0 (map #(* 2 %) (filter #(< % 20) (map #(* % %) (filter #(< 2 %) w))))))
          datasets [['(1 2 3 4 5)] ['()] ['(3)] [(range 10)] [(map #(mod % 6) (range 60))]]]
      (check "deep4" term lctx {} truth datasets))))

;; ── P5: MULTI-WAY join (recursive FAQ) — Σ cc.v over (custs ⋈ orders ⋈ cc), all on key ──
(deftest pgo-multiway-join
  (when (ready?)
    (let [dec (c "instDecidableEqNat")
          NN  (e/app* (e/const' (nm/from-string "Prod") [z z]) @N @N)
          PJ  (e/app* (e/const' (nm/from-string "Prod") [z z]) NN NN)
          PJ2 (e/app* (e/const' (nm/from-string "Prod") [z z]) PJ NN)
          fst (fn [t a b x] (e/app* (e/const' (nm/from-string "Prod.fst") [z z]) a b x))
          snd (fn [t a b x] (e/app* (e/const' (nm/from-string "Prod.snd") [z z]) a b x))
          cid   (e/lam "r" NN (fst nil @N @N (e/bvar 0)) :default)
          cidPJ (e/lam "r" PJ (fst nil @N @N (fst nil NN NN (e/bvar 0))) :default)
          join  (e/app* (c "Map.join") @N NN NN dec cid cid (e/fvar 1) (e/fvar 2))
          join3 (e/app* (c "Map.join") @N PJ NN dec cidPJ cid join (e/fvar 3))
          amt   (e/lam "p" PJ2 (snd nil @N @N (snd nil PJ NN (e/bvar 0))) :default)
          term  (fold+ (e/app* (e/const' (nm/from-string "List.map") [z z]) PJ2 @N amt join3))
          listNN (e/app (e/const' (nm/from-string "List") [z]) NN)
          lctx {1 {:name "cu" :type listNN} 2 {:name "or" :type listNN} 3 {:name "cc" :type listNN}}
          truth (fn [[cu orr cc]]
                  (reduce + 0 (for [c cu o orr d cc :when (= (first c) (first o) (first d))] (second d))))
          params {:sizes {1 1000.0 2 1000.0 3 1000.0} :ndv 8}
          datasets [[[[1 10] [2 20]] [[1 100] [2 50]] [[1 5] [1 7] [2 3]]]            ; → 15
                    [[[1 1]] [[1 1] [1 1]] [[1 9]]]                                    ; fan-out
                    [[[3 1]] [[4 1]] [[5 1]]]                                          ; no match → 0
                    [(mapv (fn [i] [(mod i 4) i]) (range 20))
                     (mapv (fn [i] [(mod i 4) i]) (range 24))
                     (mapv (fn [i] [(mod i 4) i]) (range 16))]]]                       ; non-trivial 4-key
      (check "multiway" term lctx params truth datasets))))
