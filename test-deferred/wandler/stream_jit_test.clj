(ns wandler.stream-jit-test
  "Rung 2 of the streaming ladder: the SAMPLE-BASED verified JIT over a live stream + the fork
   substrate. `wandler.stream/jit-window` pulls a window from a live coalgebra (sampled on a FORK so
   the live system is untouched), MEASURES the pipeline's filter selectivities on it, and
   certified-REPLANS (optimize-measured). As the stream's distribution DRIFTS, the measured profile
   changes and the plan re-adapts — every window's plan kernel-certified ≡ the naive query, so results
   never change. Also covers the `wandler.fork/Forkable` substrate (trivial atom-cell) and that the
   optional `wandler.bridge.spindel` adapter loads with or without spindel. See wandler.stream,
   wandler.fork, [[windowed-stream-coalgebra]]."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.stream :as stream]
            [wandler.fork :as fork]
            [wandler.test-env :as test-env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (stream/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; pipeline over a free window var #20:  sum (map snd (filter (λr. 50 < fst r) win))  — "sum amt where id>50"
(defn- pipeline []
  (let [Nat (e/const' (nm "Nat") []) Rec (e/app* (e/const' (nm "Prod") [z z]) Nat Nat)
        fstR (e/app* (e/const' (nm "Prod.fst") [z z]) Nat Nat (e/bvar 0))
        sndR (e/app* (e/const' (nm "Prod.snd") [z z]) Nat Nat (e/bvar 0))
        pred (e/lam "r" Rec (e/app* (e/const' (nm "Nat.blt") []) (e/lit-nat 50) fstR) :default)
        proj (e/lam "r" Rec sndR :default)
        win (e/fvar 20)
        filtered (e/app* (e/const' (nm "List.filter") [z]) Rec pred win)
        mapped (e/app* (e/const' (nm "List.map") [z z]) Rec Nat proj filtered)
        sm (e/app* (e/const' (nm "List.foldl") [z z]) Nat Nat (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) mapped)]
    {:term sm :win-id 20 :lctx {20 {:name "win" :type (e/app (e/const' (nm "List") [z]) Rec)}}}))

(def ^:private uncons (fn [l] (when (seq l) [(first l) (rest l)])))
(defn- naive [window] (reduce + (map second (filter #(> (long (first %)) 50) window))))

(deftest jit-window-adapts-to-drift-each-plan-certified
  (when (ready?)
    (testing "two windows with drifting selectivity → different measured profiles, both certified, both correct"
      (let [{:keys [term win-id lctx]} (pipeline)
            small (map (fn [i] [i 1]) (range 10 60 10))    ; ids 10..50  (none > 50)
            large (map (fn [i] [i 1]) (range 60 110 10))   ; ids 60..100 (all  > 50)
            r1 (stream/jit-window (a/env) term win-id lctx (fork/atom-cell small) uncons 5)
            r2 (stream/jit-window (a/env) term win-id lctx (fork/atom-cell large) uncons 5)]
        (is (true? (:verified? r1)) "window 1 plan kernel-certified ≡ naive")
        (is (true? (:verified? r2)) "window 2 plan kernel-certified ≡ naive")
        (is (= (naive (:window r1)) (:result r1)) "window 1 result = naive")
        (is (= (naive (:window r2)) (:result r2)) "window 2 result = naive")
        (is (= 0 (:result r1)) "low-selectivity window: nothing passes id>50")
        (is (= 5 (:result r2)) "high-selectivity window: all pass")
        (is (not= (:profile r1) (:profile r2))
            "the JIT measured the distribution DRIFT (selectivity 0.01 vs 1.0) from the live windows")))))

(deftest fork-atom-cell-supports-nondestructive-speculation
  (testing "Forkable atom-cell: snapshot/current/restore + fork independence + speculate is non-destructive"
    (let [c (fork/atom-cell [1 2 3])]
      (is (= [1 2 3] (fork/current c)))
      (let [snap (fork/snapshot c)
            spec (fork/speculate c (fn [fk] (fork/restore! fk [9 9]) (fork/current fk)))]
        (is (= [9 9] spec) "speculation ran on the fork")
        (is (= [1 2 3] (fork/current c)) "the live cell is UNTOUCHED by speculation")
        (fork/restore! c [4 5])
        (is (= [4 5] (fork/current c)) "restore! mutates the live cell")
        (is (= [1 2 3] snap) "the earlier snapshot is immutable")))))

(deftest spindel-adapter-loads-with-or-without-spindel
  (testing "the optional spindel Forkable adapter loads regardless; detect? is graceful when absent"
    (require 'wandler.bridge.spindel)
    (let [detect? @(requiring-resolve 'wandler.bridge.spindel/detect?)
          mk      @(requiring-resolve 'wandler.bridge.spindel/spindel-cell)]
      (is (boolean? (detect?)) "detect? returns a boolean")
      (when-not (detect?)
        (is (thrown? clojure.lang.ExceptionInfo (mk :ctx))
            "spindel-cell throws a clear error when spindel is not on the classpath")))))
