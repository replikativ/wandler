(ns wandler.jit.swap-test
  "The verified-JIT spine (wandler.jit.swap): the mode-indexed PSwapNode mechanism + the
   substrate-agnostic guarded-adaptive policy. The scenario is faithful to Path 2b: the OPTIMIZED
   operator is distinct-count WITHOUT dedup (sound only when the key is unique in the batch — the
   abduced refinement); the GUARD is `unique-key?`; the ORIGINAL always dedups. A drifting stream
   (unique batches, then duplicate-key batches) exercises the fast path, the lossless fallback, the
   anti-thrash pin, and state continuity across the swap. Pure Clojure — the certified operator pair
   stands in for what wandler.adaptive supplies."
  (:require [wandler.jit.swap :as swap]
            [wandler.adaptive :as ad]
            [clojure.test :refer [deftest is testing]]))

;; streaming distinct-count over batches of rows {:k …}, as a Mealy step (running total, output=total):
(defn- original  [s batch] (let [n (count (distinct (map :k batch)))] [(+ s n) (+ s n)]))  ; always correct
(defn- optimized [s batch] (let [n (count batch)]                     [(+ s n) (+ s n)]))  ; assumes unique key
(def   guard #(ad/unique-key? :k %))                                                       ; the hypothesis

(defn- u [& ks] (mapv (fn [k] {:k k}) ks))   ; a batch with the given keys

(defn- ground-truth
  "The always-original outputs + final state (the spec the JIT must match exactly)."
  [batches]
  (reduce (fn [{:keys [s outs]} b] (let [[s' o] (original s b)] {:s s' :outs (conj outs o)}))
          {:s 0 :outs []} batches))

(deftest guarded-adaptive-drift
  (let [batches [(u 1 2 3) (u 4 5 6) (u 7 8 9)        ; unique → optimized is correct
                 (u 1 1 2) (u 3 3 4) (u 5 5 6) (u 7 7 8)]  ; dup key → guard fails → fallback, then pin
        node    (swap/atom-node original)
        gt      (ground-truth batches)
        r       (swap/run-adaptive node {:original original :optimized optimized
                                         :guard guard :state0 0 :cutoff 3} batches)]
    (testing "SOUND: outputs match the always-original ground truth exactly (guard+fallback lossless)"
      (is (= (:outs gt) (:outputs r)))
      (is (= (:s gt) (:final-state r)) "running aggregate is continuous ACROSS the pin swap"))
    (testing "fast path ran on the unique batches; fallback on the duplicate batches"
      (is (= 3 (:opt-runs r))  "3 unique batches took the optimized path")
      (is (= 4 (:orig-runs r)) "4 duplicate batches ran the original (3 fallbacks + 1 pinned)"))
    (testing "anti-thrash: after `cutoff` violations the node PINS to original (HotSpot trap-history)"
      (is (= 3 (:violations r)))
      (is (true? (:pinned? r)))
      (is (= 2 (:generation r))
          "two installs: initial optimized + the pin to original"))))

(deftest no-drift-stays-optimized
  (let [batches [(u 1 2) (u 3 4) (u 5 6) (u 7 8) (u 9 10)]   ; always unique
        node    (swap/atom-node original)
        r       (swap/run-adaptive node {:original original :optimized optimized
                                         :guard guard :state0 0 :cutoff 3} batches)]
    (testing "no violation → never pins, optimized runs throughout, result still correct"
      (is (= (:outs (ground-truth batches)) (:outputs r)))
      (is (= 5 (:opt-runs r)))
      (is (= 0 (:orig-runs r)))
      (is (false? (:pinned? r))))))

(deftest async-seq-swap-between-pulls
  ;; the partial-cps GeneratorSeq shape: a swappable generator-fn read THROUGH the cell, so a swap
  ;; between pulls takes effect on the NEXT element; already-yielded elements are untouched; the
  ;; counter state is carried across the swap (transparent transferable tail value).
  (let [node   (swap/generator-node (fn [n] (when (< n 5) [(* n 10)  (inc n)])))
        s      (swap/pull-seq node 0)
        first2 (doall (take 2 s))]                   ; realize 0,10 under v1
    (swap/swap-op! node (fn [n] (when (< n 5) [(* n 100) (inc n)])))  ; swap to v2 between pulls
    (let [all (doall (take 5 s))]
      (testing "the swap takes effect on the next element; prior elements unchanged; state carried"
        (is (= [0 10] first2))
        (is (= [0 10 200 300 400] all) "elems 3-5 use v2, counter continued from n=2")
        (is (= 1 (swap/generation node)))))))

(deftest state-and-input-guards-both-required
  (let [calls (atom [])
        original (fn [st in] [(inc st) [:original in]])
        optimized (fn [st in] [(inc st) [:optimized in]])
        node (swap/atom-node original)
        r (swap/run-adaptive node
                             {:original original :optimized optimized :state0 0 :cutoff 2
                              :guard pos?
                              :state-guard (fn [st in] (swap! calls conj [st in]) (even? st))}
                             [1 1 -1 1])]
    (is (= [[:optimized 1] [:original 1] [:original -1] [:original 1]] (:outputs r)))
    (is (= [[0 1] [1 1]] @calls) "input failures short-circuit; pinned execution stops guarding")
    (is (:pinned? r))
    (is (= 4 (:final-state r)))))

(deftest adaptive-requires-a-guard
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"requires an input or state guard"
                        (swap/run-adaptive (swap/atom-node identity)
                                           {:original identity :optimized identity} []))))
