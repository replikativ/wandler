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
