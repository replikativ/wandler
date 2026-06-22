(ns wandler.jit.async-seq-test
  "The REAL partial-cps adapter (wandler.jit.async-seq): a verified hot-swap at the genuine
   `(await (anext s))` boundary of an `is.simm.partial-cps` async sequence. Proves a swap between
   pulls lands on the next element, the generator state is carried across, and already-yielded
   elements are untouched — the async corner of the mode lattice on the substrate spindel builds on."
  (:require [wandler.jit.async-seq :as aseq]
            [wandler.jit.swap :as swap]
            [is.simm.partial-cps.sequence :as pseq]
            [clojure.test :refer [deftest is testing]]))

(def ^:private v1 (fn [n] (when (< n 5) [(* n 10)  (inc n)])))   ; 0 10 20 30 40
(def ^:private v2 (fn [n] (when (< n 5) [(* n 100) (inc n)])))   ; 0 10 200 300 400 (×100 from swap point)

(deftest realizes-like-the-plain-generator
  (testing "a swappable async-seq with no swap realizes exactly the underlying generator"
    (let [node (swap/generator-node v1)
          s    (aseq/swappable-aseq node 0)]
      (is (= [0 10 20 30 40] (aseq/realize s)))
      (is (= 0 (swap/generation node)) "no swap performed"))))

(deftest purely-functional-tail
  (testing "the partial-cps tail is persistent: re-realizing the same seq (no swap) is idempotent"
    (let [node (swap/generator-node v1)
          s    (aseq/swappable-aseq node 0)]
      (is (= (aseq/realize s) (aseq/realize s))))))

(deftest swap-between-pulls-lands-on-next-element
  (testing "swap-op! between two anext pulls takes effect on the NEXT element; state carried; prior untouched"
    (let [node (swap/generator-node v1)
          s    (aseq/swappable-aseq node 0)
          ;; after the 2nd element (idx 1) swap the operator to v2 at the real anext boundary
          out  (aseq/realize s (fn [i] (when (= i 1) (swap/swap-op! node v2))))]
      (is (= [0 10 200 300 400] out)
          "elems 0,1 used v1 (untouched); elems 2-4 used v2; generator counter continued from n=2")
      (is (= 1 (swap/generation node)) "exactly one swap landed"))))

(deftest swap-is-at-the-genuine-anext-boundary
  (testing "manual anext drive: a swap after pulling element 0 changes element 1, proving the cell is read per-anext"
    (let [node           (swap/generator-node v1)
          s0             (aseq/swappable-aseq node 0)
          [v0 s1]        (aseq/run-sync (pseq/anext s0))]   ; pull element 0 under v1
      (swap/swap-op! node v2)                               ; swap at the quiescent boundary
      (let [[v1* _]      (aseq/run-sync (pseq/anext s1))]   ; pull element 1 under v2
        (is (= 0 v0)   "element 0 produced by v1")
        (is (= 100 v1*) "element 1 produced by v2 (1×100), so the operator was read at THIS anext")))))
