(ns wandler.clean.diff-test
  "Phase 0 gate: the differential harness (wandler.clean.diff) itself, plus its first live subjects.
   Exercises all three parities (WANDLER_REIMPL_PLAN §0.2):
     (c) PROOF  — the clean laws (wandler.clean.laws.frame) check-constant-verify.
     (b) RESULT — the certified optimizer preserves the executed result (fused ≡ naive).
     (a) PLAN   — and it actually changed the plan (fused: fewer passes, kernel-certified).
   The fused-vs-naive subject is old wandler against itself — the same machinery that will take
   old-vs-clean subjects as the runtime/optimizer modules land in Phases 2+."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.clean.diff :as diff]
            [wandler.clean.laws.frame :as frame]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (w/install!)
    (binding [a/*verbose* false] (frame/install!)))
  (f))
(use-fixtures :once setup)

(defn- ready? [] (some? @test-env/init-full-env))

;; A 3-stage pipeline that the certified optimizer fuses to one pass.
(def ^:private BODY
  '(reduce + 0 (map (fn [x] (* x x)) (filter (fn [x] (< 2 x)) xs))))
(def ^:private INPUTS [[] '(1 2 3 4 5) '(10 20 30) '(2 2 2) '(1) '(3 1 4 1 5 9 2 6)])

(defn- defpipe! [nm optimize?]
  (binding [a/*verbose* false, w/*optimize* optimize?]
    (eval (list 'ansatz.core/defn nm '[xs :- (List Nat)] 'Nat BODY)))
  @(resolve nm))

(deftest harness-primitives
  (testing "result-parity: agreeing fns pass, a deliberate disagreement is caught"
    (is (:ok? (diff/result-parity inc inc [1 2 3])))
    (let [r (diff/result-parity inc dec [1 2 3])]
      (is (not (:ok? r)))
      (is (= 3 (count (:mismatches r))))))
  (testing "result-parity normalizes sequential outputs (vector ≡ list of same elements)"
    (is (:ok? (diff/result-parity (fn [_] [1 2 3]) (fn [_] '(1 2 3)) [:x]))))
  (testing "plan-parity: a report agrees with itself, differs from a tweaked one"
    (let [p {:stages-after [:map] :rewrites ["map_map"] :verified? true}]
      (is (:ok? (diff/plan-parity p p)))
      (is (not (:ok? (diff/plan-parity p (assoc p :verified? false))))))))

(deftest proof-parity-clean-laws
  (when (ready?)
    (testing "(c) every clean law check-constant-verifies"
      (let [g (diff/proof-gate (a/env)
                ["aggJoin_split" "aggJoin_reorder" "sum_filter_map" "wsum"])]
        (is (:ok? g) (str "unverified clean laws: " (:failed g)))))))

(deftest result-and-plan-parity-optimizer
  (when (ready?)
    (let [fused (defpipe! 'dh-fused true)
          naive (defpipe! 'dh-naive false)
          fused-plan (diff/plan-of 'dh-fused)
          naive-plan (diff/plan-of 'dh-naive)]
      (testing "(b) the certified optimizer preserves the executed result (fused ≡ naive)"
        (let [r (diff/result-parity fused naive INPUTS)]
          (is (:ok? r) (str "fused/naive diverged: " (:mismatches r)))))
      (testing "(b) and both agree with clojure.core ground truth"
        (let [truth (fn [xs] (reduce + 0 (map (fn [x] (* x x)) (filter (fn [x] (< 2 x)) xs))))]
          (is (:ok? (diff/result-parity fused truth INPUTS)))))
      (testing "(a) the optimizer DID change the plan: fused is kernel-certified + ≤ naive passes"
        (is (:verified? fused-plan) "fused rewrite kernel-certified")
        (is (<= (long (:passes-after fused-plan)) (long (:passes-before fused-plan))))
        ;; fused vs naive are intentionally DIFFERENT plans — same result, different shape
        (is (not (:ok? (diff/plan-parity fused-plan naive-plan)))
            "fused and naive should be distinct plans"))
      (testing "the combined `differential` gate reports ok on a semantics-preserving subject"
        (let [d (diff/differential {:label "dh" :old-fn naive :new-fn fused :inputs INPUTS
                                    :kenv (a/env) :laws ["aggJoin_reorder"]})]
          (is (:ok? d) (str "differential failed: " d)))))))
