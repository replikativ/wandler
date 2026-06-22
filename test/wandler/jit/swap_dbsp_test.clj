(ns wandler.jit.swap-dbsp-test
  "DBSP (differential) PSwapNode adapter, Case A — recompute-free swaps (wandler.jit.swap-dbsp). The
   integrator ∫ (a linear node's running `out`, a join node's `[L R V]`) is owned by the node and carried
   VERBATIM across a certified-≡ leaf-operator swap; the output stream is identical to never-swapping
   (δQ=δQ' because Q≡Q'). The honesty test shows a NON-≡ swap corrupts the integrator — so the kernel ≡
   certificate is the precondition for the carry, not decoration. Pure Clojure Z-set runtime."
  (:require [wandler.jit.swap-dbsp :as d]
            [wandler.jit.swap :as swap]
            [wandler.exec.zset :as zs]
            [clojure.test :refer [deftest is testing]]))

(deftest linear-integrator-carried
  (testing "streaming weighted SUM: swap the sum fn mid-stream; the running accumulator is carried"
    (let [f   (fn [r] (:n r))
          f'  (fn [r] (get r :n))                       ; extensionally ≡ f
          opn (swap/atom-node [[:sum f]])  ln  (d/swappable-linear-node opn)
          ref (swap/atom-node [[:sum f]])  lrf (d/swappable-linear-node ref)
          step! (fn [delta] ((:push! ln) delta) ((:push! lrf) delta))]
      (step! {{:n 10} 1 {:n 20} 1})
      (step! {{:n 5} 1})
      (is (= 35 @(:out ln)) "integrator after two deltas")
      (swap/swap-op! opn [[:sum f']])                   ; ⟵ swap between deltas
      (is (= 35 @(:out ln)) "swap-op! does NOT touch the integrator")
      (is (= 1 (swap/generation opn)))
      (step! {{:n 100} 1})
      (step! {{:n 50} -1})                              ; retraction
      (is (= 85 @(:out ln)) "running sum continues across the swap")
      (is (= @(:out lrf) @(:out ln)) "identical to the never-swapped ground truth"))))

(deftest join-integrator-carried
  (testing "incremental join + retraction + fan-out: swap kf/lf mid-stream; [L R V] carried verbatim"
    (let [kf  (fn [r] (:k r))
          kf' (fn [r] (get r :k))                       ; ≡ kf
          opn (swap/atom-node [kf kf])   jn  (d/swappable-join-node opn)
          ref (swap/atom-node [kf kf])   rf  (d/swappable-join-node ref)
          views (atom [])
          step! (fn [delta] (let [v ((:push! jn) delta) vr ((:push! rf) delta)]
                              (swap! views conj [(= v vr) (count v)])))]
      (step! [{{:k 1 :v "a"} 1} {{:k 1 :w "x"} 1}])     ; +k1 pair
      (step! [{{:k 2 :v "b"} 1} {{:k 2 :w "y"} 1}])     ; +k2 pair
      (swap/swap-op! opn [kf' kf'])                     ; ⟵ swap between deltas
      (step! [{{:k 1 :v "a"} -1} {}])                   ; retract left k1 → drop the k1 pair
      (step! [{} {{:k 2 :w "z"} 1}])                    ; second right k2 → fan-out
      (is (every? first @views) "every step's view matches the never-swapped ground truth")
      (is (= [1 2 1 2] (mapv second @views)) "view sizes: +k1, +k2, −k1, +k2-fanout"))))

(deftest non-equiv-swap-corrupts
  (testing "a NON-≡ swap mixes the keying — the integrator carry is sound ONLY for certified-≡ ops"
    (let [kf  (fn [r] (:k r))
          bad (constantly :ALL)                         ; NOT ≡ kf — collapses all keys
          opn (swap/atom-node [kf kf])   jn (d/swappable-join-node opn)
          ref (swap/atom-node [kf kf])   rf (d/swappable-join-node ref)]
      (doseq [dl [[{{:k 1 :v "a"} 1} {{:k 1 :w "x"} 1}]
                  [{{:k 2 :v "b"} 1} {{:k 2 :w "y"} 1}]]]
        ((:push! jn) dl) ((:push! rf) dl))
      (swap/swap-op! opn [bad bad])                     ; ⟵ non-≡ swap
      (let [v-bad ((:push! jn) [{{:k 3 :v "c"} 1} {{:k 3 :w "z"} 1}])
            v-ok  ((:push! rf) [{{:k 3 :v "c"} 1} {{:k 3 :w "z"} 1}])]
        (is (not= v-bad v-ok) "the non-≡ swap diverges from ground truth")
        (is (> (count v-bad) (count v-ok)) "mixed keying over-joins the carried inputs")))))

(deftest state-reducing-carry-output
  (testing "A2: carry the running view into a leaner node (group-by-elim direction), drop old ∫"
    (let [opn (swap/atom-node [[:map (fn [r] (assoc r :seen true))]])
          old (d/swappable-linear-node opn)]
      ((:push! old) {{:k 1} 1 {:k 2} 1})                ; accumulate a running view
      (let [running @(:out old)
            new-opn (swap/atom-node [[:map (fn [r] (assoc r :seen true))]])
            new (d/swappable-linear-node new-opn)]
        (d/carry-output! old new)
        (is (= running @(:out new)) "the running view is carried into the new node (continuity)")
        ((:push! new) {{:k 3} 1})                        ; new node continues from the carried view
        (is (contains? @(:out new) {:k 3 :seen true}) "new deltas accumulate onto the carried view")
        (is (= 3 (count @(:out new))))))))

(deftest rematerialize-reconstructs-the-integrator
  (testing "Case B: rematerialize rebuilds [L R V] from carried sources = a node built from scratch"
    (let [kf  (fn [r] (:k r))
          opn (swap/atom-node [kf kf])  jn (d/swappable-join-node opn)
          deltas [[{{:k 1 :v "a"} 1} {{:k 1 :w "x"} 1}]
                  [{{:k 2 :v "b"} 1} {{:k 2 :w "y"} 1}]
                  [{{:k 1 :v "a"} -1} {{:k 2 :w "z"} 1}]]]   ; retraction + fan-out
      (doseq [dl deltas] ((:push! jn) dl))
      (let [[L R V] @(:state jn)
            re  (d/rematerialize-join (swap/atom-node [kf kf]) L R)]   ; rebuild from carried L,R
        (is (= V @(:out re)) "rematerialized view = the incrementally-maintained view")
        (is (= [L R V] @(:state re)) "full integrator reconstructed from the sources")))))

(deftest rematerialize-handles-a-rekey-that-carry-cannot
  (testing "Case B is sound for a target that changes the materialized intermediate (re-key)"
    (let [kf  (fn [r] (:k r))
          kf2 (fn [r] (:g r))                                ; a DIFFERENT key — a new intermediate
          opn (swap/atom-node [kf kf])  jn (d/swappable-join-node opn)]
      (doseq [dl [[{{:k 1 :g 9 :v "a"} 1} {{:k 1 :g 9 :w "x"} 1}]
                  [{{:k 2 :g 9 :v "b"} 1} {{:k 2 :g 9 :w "y"} 1}]]]
        ((:push! jn) dl))
      (let [[L R _] @(:state jn)
            re (d/rematerialize-join (swap/atom-node [kf2 kf2]) L R)]
        ;; rematerialized view = the from-scratch kf2-join of the carried sources (sound), independent of
        ;; the OLD kf-keyed history — exactly what carrying V (Case A) could not give.
        (is (= (zs/z-join kf2 kf2 L R) @(:out re)))
        (is (= 4 (count @(:out re))) "both rows share :g 9 → 2×2 join, rebuilt correctly")))))

(defn- drive-mealy
  "Ground truth: thread `op` (a Mealy step) over `deltas`, collecting the per-delta output."
  [op deltas]
  (loop [ds deltas st [{} {} {}] out []]
    (if (empty? ds) out
      (let [[st' v] (op st (first ds))] (recur (rest ds) st' (conj out v))))))

(deftest adaptive-join-end-to-end
  (testing "run-adaptive drives a DBSP join: integrator threaded across guard-driven op swaps + pin"
    ;; optimized uses the refinement-fast key (:k directly, sound iff every row HAS :k); original is the
    ;; robust key (unique fallback for a missing :k). The guard discharges 'every row has :k' per delta.
    (let [optk (fn [r] (:k r))
          robk (fn [r] (or (:k r) (- (hash r))))
          opt  (d/join-mealy optk optk)
          org  (d/join-mealy robk robk)
          guard (fn [[dL dR]] (every? #(contains? % :k) (concat (keys dL) (keys dR))))
          deltas [[{{:k 1 :v "a"} 1} {{:k 1 :w "x"} 1}]      ; well-formed → optimized
                  [{{:k 2 :v "b"} 1} {{:k 2 :w "y"} 1}]      ; well-formed → optimized
                  [{{:v "c"} 1}      {{:k 1 :w "z"} 1}]      ; MALFORMED (no :k) → fallback to original
                  [{{:v "d"} 1}      {}]                     ; MALFORMED → fallback; 2nd violation → PIN
                  [{{:k 3 :v "e"} 1} {{:k 3 :w "q"} 1}]]     ; well-formed but PINNED → original
          node (swap/atom-node org)
          r    (swap/run-adaptive node {:original org :optimized opt :guard guard
                                        :state0 [{} {} {}] :cutoff 2} deltas)]
      (testing "the running views match the all-original ground truth at every step (integrator carried)"
        (is (= (drive-mealy org deltas) (:outputs r))))
      (testing "fast path on the well-formed deltas, fallback on the malformed, pin after cutoff"
        (is (= 2 (:opt-runs r))  "two well-formed deltas took the optimized key")
        (is (= 3 (:orig-runs r)) "two malformed (fallback) + one pinned")
        (is (= 2 (:violations r)))
        (is (true? (:pinned? r))))
      (testing "the final integrator equals a from-scratch robust-key join over the whole stream"
        (is (= (last (drive-mealy org deltas)) (nth (:final-state r) 2)))))))

(deftest rematerialize-cost-gate
  (testing "the one-time rematerialize cost is amortized over expected remaining deltas"
    (let [L {:a 1 :b 1 :c 1} R {:x 1 :y 1}]                 ; cost = 3×2 = 6
      (is (= 6 (d/rematerialize-cost L R)))
      (is (true?  (d/rematerialize-worth-it? L R 0.5 100)) "0.5×100=50 > 6 → adopt")
      (is (false? (d/rematerialize-worth-it? L R 0.5 5))   "0.5×5=2.5 < 6 → decline (too few deltas left)"))))
