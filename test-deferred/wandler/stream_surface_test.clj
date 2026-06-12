(ns wandler.stream-surface-test
  "Systematic tracing of infinite (coinductive) sources through the TYPE (wandler.surface.streams):
   `Strm A` is distinct from `List A`, so `(range)` / a passed-in `Strm` is detected by its type, and
   the verbs route — map stays a stream, take WINDOWS it to a List, reduce/filter over a raw stream are
   rejected (the productivity gate). `Strm.take_smap` certifies the window commutes; it runs over the
   infinite source forcing only the window."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.surface.collections :as coll]
            [wandler.surface.edn :as edn]
            [wandler.gradual :as g]
            [wandler.surface.streams :as ss]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (coll/install!) (edn/install-core!) (edn/install-surface!) (ss/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest take-smap-certified
  (when (ready?)
    (testing "Strm + take_smap admitted (kernel check-constant'd)"
      (doseq [n ["Strm" "Strm.range" "Strm.smap" "Strm.take" "Strm.take_smap"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present"))))))

(deftest range-is-traced-as-a-stream-and-routes
  (when (ready?)
    (testing "(range) elaborates to Strm.range, map stays a stream, take windows to a List, reduce certifies"
      (let [{:keys [term lctx]} (g/elaborate (a/env) '[]
                                  '(reduce + 0 (take 5 (map (fn [x :- Nat] (* 2 x)) (range)))))
            res (g/plan (a/env) term :lctx lctx)
            s (e/->string term)]
        (is (clojure.string/includes? s "Strm.take") "the window Strm.take appears")
        (is (clojure.string/includes? s "Strm.smap") "map over a stream stays Strm.smap")
        (is (:verified? res) "the windowed stream pipeline kernel-certifies")))))

(deftest productivity-gate-rejects-unwindowed-reduce
  (when (ready?)
    (testing "reduce over a RAW infinite stream is rejected — window it first"
      (is (thrown-with-msg? Exception #"not productive"
            (g/elaborate (a/env) '[] '(reduce + 0 (map (fn [x :- Nat] (* 2 x)) (range)))))))))

(deftest runs-over-the-infinite-source
  (when (ready?)
    (testing "windowed stream pipelines RUN over (range) and over a passed-in Strm, forcing only the window"
      (eval '(ansatz.core/defn ss-sum5 [] Nat (reduce + 0 (take 5 (map (fn [x :- Nat] (* 2 x)) (range))))))
      (is (= 20 @(resolve 'ss-sum5)) "0+2+4+6+8 over the infinite naturals")
      (eval '(ansatz.core/defn ss-firstk [s :- (Strm Nat), k :- Nat] (List Nat)
               (take k (map (fn [x :- Nat] (* x x)) s))))
      (is (= [0 1 4 9] ((resolve 'ss-firstk) identity 4)) "squares of a passed-in stream, windowed to 4"))))

(deftest bisimulation-coinduction-principle
  (when (ready?)
    (testing "bisim + the coinduction principle (bisim_eq via funext) + converse — all check-constant'd"
      (doseq [n ["Strm.bisim" "Strm.bisim_eq" "Strm.eq_bisim"
                 "LSeq.bisim" "LSeq.bisim_eq" "LSeq.eq_bisim"
                 ;; a genuine stream equality proven BY coinduction (smap extensionality)
                 "Strm.smap_congr"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present + kernel-verified"))))))

(deftest bilinear-streaming-join
  (when (ready?)
    (ss/install-join!)
    (testing "the DBSP differential join: joinCount2 + the 4-term bilinear recurrence — check-constant'd"
      (doseq [n ["Strm.joinCount2" "Strm.joinCount2_step"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present + kernel-verified"))))
    (testing "the bilinear recurrence RUNS: incremental (only new elements' cross-terms) == batch"
      (let [jcount (fn [kf lf xs ys] (count (for [x xs y ys :when (= (kf x) (lf y))] [x y])))
            S (fn [n] {:k (mod n 3) :v n}) T (fn [n] {:k (mod n 2) :w n}) kf :k lf :k
            batch (fn [n] (jcount kf lf (mapv S (range (inc n))) (mapv T (range (inc n)))))
            incr  (fn [n] (reduce (fn [acc k]
                                    (+ acc (jcount kf lf [(S k)] (mapv T (range k)))        ; new_x ⋈ old_y
                                           (jcount kf lf (mapv S (range k)) [(T k)])        ; old_x ⋈ new_y
                                           (jcount kf lf [(S k)] [(T k)])))                 ; new_x ⋈ new_y
                                  0 (range (inc n))))]
        (is (= (mapv batch (range 6)) (mapv incr (range 6))) "incremental differential join == batch recompute")))))

(deftest scan-incremental-running-aggregate
  (when (ready?)
    (testing "scan + scan_step (the O(1) incremental recurrence — DBSP integrate) — check-constant'd"
      (doseq [n ["Strm.scan" "Strm.scan_step"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present + kernel-verified"))))
    (testing "reductions over a stream → the running aggregate (productive), windowed; runs over (range)"
      (eval '(ansatz.core/defn ss-runsum [k :- Nat] (List Nat) (take k (reductions + 0 (range)))))
      (is (= [0 1 3 6 10 15] ((resolve 'ss-runsum) 6)) "running sum of the naturals (triangular numbers)")
      (eval '(ansatz.core/defn ss-runsq [s :- (Strm Nat), k :- Nat] (List Nat)
               (take k (reductions + 0 (map (fn [x :- Nat] (* x x)) s)))))
      (is (= [0 1 5 14 30] ((resolve 'ss-runsq) identity 5)) "running sum of squares over a passed-in stream"))))

(deftest lseq-possibly-finite-real-lazy-seqs
  (when (ready?)
    (testing "LSeq A = Nat → Option A: a real PASSED-IN lazy seq is traced, mapped + windowed (lazy, O(n))"
      (doseq [n ["LSeq" "LSeq.smap" "LSeq.take" "LSeq.take_smap"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present")))
      (eval '(ansatz.core/defn ss-lwin [s :- (LSeq Nat), k :- Nat] (List Nat)
               (take k (map (fn [x :- Nat] (* x x)) s))))
      (is (= [0 1 4 9 16] ((resolve 'ss-lwin) (iterate inc 0) 5)) "infinite lazy seq, windowed to 5")
      (is (= [9 16] ((resolve 'ss-lwin) [3 4] 5)) "possibly-FINITE: take stops at the seq's end"))
    (testing "an EDN-value lazy seq, projected + windowed; gate still fires"
      (eval '(ansatz.core/defn ss-lfeed [s :- (LSeq Value), k :- Nat] (List Value)
               (take k (for [v s] (get v :amount)))))
      (let [src (map (fn [n] (edn/edn->value {:amount (* n 7)})) (range))]
        (is (= [0 7 14] (mapv edn/value->edn ((resolve 'ss-lfeed) src 3)))))
      (is (thrown-with-msg? Exception #"not productive"
            (g/elaborate (a/env) '[s :- (LSeq Nat)] '(reduce + 0 s)))))))

(deftest general-edn-values-not-just-nat
  (when (ready?)
    (testing "NOT type-limited: a Strm of general EDN Values works (field projection → vget), windowed"
      (eval '(ansatz.core/defn ss-feed [s :- (Strm Value), k :- Nat] (List Value)
               (take k (for [v s] (get v :amount)))))      ; `for` + stream + EDN, all unified
      (let [src (fn [n] (edn/edn->value {:id n :amount (* n 100)}))]
        (is (= [0 100 200] (mapv edn/value->edn ((resolve 'ss-feed) src 3)))
            "for-comprehension over an infinite EDN-value stream, windowed")))
    (testing "the productivity gate fires through `for` over an EDN-value stream too"
      (is (thrown-with-msg? Exception #"not productive"
            (g/elaborate (a/env) '[s :- (Strm Value)] '(reduce + 0 (for [v s] (get v :amount)))))))))
