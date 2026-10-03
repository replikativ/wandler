(ns wandler.adaptive-test
  "The adaptive dependently-typed planning loop (wandler.adaptive): ABDUCE a unique key from a data
   sample, let the kernel PROVE the group-by-elimination rewrite sound under it, GUARD the key at the
   runtime boundary (fall back if violated), and BENCHMARK both plans to decide adoption. Asserts the
   loop is SOUND (always correct, guard-protected) and HONEST (selection follows the empirical cost,
   charging the runtime guard on every query)."
  (:require [wandler.adaptive :as ad]
            [wandler.laws.groupby :as groupby]
            [wandler.test-env :as test-env]
            [wandler.runtime]
            [ansatz.core :as a]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is testing]]))

(defn- C [s ls] (e/const' (name/from-string s) ls))

(deftest unique-key-abduction
  (testing "unique-key? is the abduction probe AND the runtime guard"
    (is (true?  (ad/unique-key? inc [1 2 3])))
    (is (true?  (ad/unique-key? inc [])))
    (is (false? (ad/unique-key? even? [1 2 3])))      ; even? collides → not a key
    (is (false? (ad/unique-key? :k [{:k 1} {:k 1}]))))) ; duplicate key value

(deftest adaptive-groupby-loop
  (if-let [ke0 @test-env/init-full-env]
    (do (reset! a/ansatz-env ke0)
        (groupby/install!)
        (let [ke  (a/env)
              u   lvl/zero
              Nat (C "Nat" []) listNat (e/app (C "List" [u]) Nat)
              dec (C "instDecidableEqNat" []) kf (C "Nat.succ" [])
              ;; the denormalize-each-row-with-its-own-group plan, over a relation term `xs`
              make-plan (fn [xs]
                          (e/app* (C "List.map" [u u]) Nat listNat
                                  (e/lam "r" Nat
                                         (e/app* (C "Option.getD" [u]) listNat
                                                 (e/app* (C "Map.lookup" []) Nat listNat dec (e/app kf (e/bvar 0))
                                                         (e/app* (C "Map.group_by" []) Nat Nat dec kf xs))
                                                 (e/app (C "List.nil" [u]) Nat)) :default)
                                  xs))
              sample (range 64)            ; abduce: succ is unique over the sample
              big    (range 6000)]         ; the relation the plan will run over
          (testing "ABDUCE + DEDUCE: unique key found, group-by-elim kernel-certified"
            (let [r (ad/adaptive-groupby ke Nat Nat kf inc make-plan sample :data big)]
              (is (true? (:abduced-unique? r)) "succ is a unique key over the sample")
              (is (true? (:verified? r))       "the rewrite is kernel-certified under the key")
              (is (= [:groupby-elim] (:rewrites r)))
              (is (some? (:certificate r))     "carries the kernel proof term")
              (testing "SOUND: the chosen plan is correct on unique data"
                (is (= [[1] [2] [3]] ((:run r) (list 1 2 3)))))
              (testing "GUARD: a duplicate-key relation falls back to the original (still correct)"
                ;; original group_by puts both 1s in one bucket → each row sees [1 1]
                (is (= [[1 1] [1 1] [2]] ((:run r) (list 1 1 2)))))))
          (testing "HONEST selection charges the full per-invocation guard regardless of amortize"
            (doseq [amortize [1 100000]]
              (let [r (ad/adaptive-groupby ke Nat Nat kf inc make-plan sample :data big :amortize amortize)
                    {:keys [original-ns rewritten-ns guard-ns]} (:bench r)]
                (is (true? (:verified? r)))
                (is (= (if (< (+ rewritten-ns guard-ns) original-ns) :rewritten :original)
                       (:strategy r)))
                (is (= [[1] [2] [3]] ((:run r) (list 1 2 3)))))))
          (testing "abduction FAILS on a non-unique sample → no speculation, run the original"
            (let [r (ad/adaptive-groupby ke Nat Nat kf even? make-plan [1 2 3] :data [1 2 3])]
              (is (false? (:abduced-unique? r)))
              (is (= :original (:strategy r)))))))
    (println "SKIP adaptive-groupby-loop: no Init env")))
