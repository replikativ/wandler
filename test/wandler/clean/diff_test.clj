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
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as nm]
            [wandler.core :as w]
            [wandler.clean.diff :as diff]
            [wandler.clean.laws.frame :as frame]
            [wandler.clean.surface.core :as surf]
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

;; ── the cutover gate: a REAL clean-surface subject, old-vs-clean, all three parities live ─────
;; A query written once in ordinary Clojure, run through (1) the OLD wandler surface+optimizer and
;; (2) the CLEAN surface+optimizer, asserting the strangler equivalence directly: identical executed
;; result (clean ≡ old ≡ clojure.core), and the clean plan is independently kernel-certified + fuses.
(def ^:private MM-BODY '(mapv (fn [x] (inc x)) (mapv (fn [x] (inc x)) xs)))
(def ^:private MM-INPUTS [[] [1 2 3] [10 20 30 40] [5] [0 0 0 7]])
(defn- mm-truth [xs] (mapv inc (mapv inc xs)))

(deftest clean-surface-subject-cutover-differential
  (when (ready?)
    ;; (1) OLD subject — the fixture left the OLD surface installed (w/install!); build + capture it FIRST.
    (let [old-fn (binding [a/*verbose* false]
                   (eval (list 'ansatz.core/defn 'dh-old '[xs :- (List Nat)] '(List Nat) MM-BODY))
                   @(resolve 'dh-old))]
      ;; (2) CLEAN subject — now install the CLEAN surface (overwrites the registry with clean copies),
      ;; build the clean fn + read its elaborated body for the clean optimizer.
      (surf/install!)
      (let [clean-fn (binding [a/*verbose* false]
                       (eval (list 'ansatz.core/defn 'dh-clean '[xs :- (List Nat)] '(List Nat) MM-BODY))
                       @(resolve 'dh-clean))
            clean-body (.value (kenv/lookup (a/env) (nm/from-string "dh-clean")))
            clean-plan (diff/clean-plan-report (a/env) clean-body)]
        (testing "(b) RESULT — clean ≡ old ≡ clojure.core on every input (the strangler equivalence)"
          (is (:ok? (diff/result-parity clean-fn old-fn MM-INPUTS))
              "clean-surface query result diverged from old wandler")
          (is (:ok? (diff/result-parity clean-fn mm-truth MM-INPUTS))
              "clean-surface query result diverged from clojure.core ground truth"))
        (testing "(a) PLAN — the CLEAN optimizer certifies + fuses (2 map passes → 1)"
          (is (:verified? clean-plan) "the clean fusion plan check-constant-verifies")
          (is (= [] (:rewrites clean-plan)))
          (is (= ["map"] (:stages-after clean-plan)) "fused to a single map stage")
          (is (< (long (:passes-after clean-plan)) (long (:passes-before clean-plan)))
              "fewer passes after fusion"))
        (testing "(c) PROOF — the clean laws backing the optimizer verify"
          (is (:ok? (diff/proof-gate (a/env) ["aggJoin_split" "aggJoin_reorder" "wsum"]))))
        (testing "the combined `differential` gate is green on the real clean subject"
          (let [d (diff/differential {:label "clean-mm" :old-fn old-fn :new-fn clean-fn :inputs MM-INPUTS
                                      :old-plan clean-plan :new-plan clean-plan
                                      :kenv (a/env) :laws ["aggJoin_split"]})]
            (is (:ok? d) (str "differential failed: " d))))))))

;; ── Phase 7 cutover GATE: the differential CORPUS ────────────────────────────────────────────
;; A representative corpus of ordinary-Clojure surface queries, each run through BOTH the old wandler
;; surface+optimizer and the clean surface+optimizer. For every subject we assert the strangler
;; equivalence (clean ≡ old ≡ clojure.core on a battery of inputs) AND that the clean optimizer produces
;; an independently kernel-certified plan. Passing this corpus is what justifies the cutover: the clean
;; core is a faithful drop-in for the old core across the surface it covers.
(def ^:private CORPUS-INPUTS [[] [1 2 3] [10 20 30 40] [5] [0 1 2 3 4 5] [2 2 2 2]])
(def ^:private CORPUS
  ;; {:label, :sig (return type form), :body (clojure query over `xs`), :truth (clojure.core reference)}
  [{:label "map∘map"       :sig '(List Nat)
    :body '(mapv (fn [x] (inc x)) (mapv (fn [x] (inc x)) xs))
    :truth (fn [xs] (mapv inc (mapv inc xs)))}
   {:label "filter∘filter" :sig '(List Nat)
    :body '(filterv (fn [x] (Nat.ble 2 x)) (filterv (fn [x] (Nat.ble 1 x)) xs))
    :truth (fn [xs] (filterv #(<= 2 %) (filterv #(<= 1 %) xs)))}
   {:label "map∘filter"    :sig '(List Nat)
    :body '(mapv (fn [x] (inc x)) (filterv (fn [x] (Nat.ble 2 x)) xs))
    :truth (fn [xs] (mapv inc (filterv #(<= 2 %) xs)))}
   {:label "filter→map→reduce" :sig 'Nat
    :body '(->> xs (filterv (fn [x] (Nat.ble 2 x))) (mapv (fn [x] (inc x))) (reduce + 0))
    :truth (fn [xs] (reduce + 0 (mapv inc (filterv #(<= 2 %) xs))))}
   {:label "map∘map∘map"   :sig '(List Nat)
    :body '(mapv (fn [x] (inc x)) (mapv (fn [x] (inc x)) (mapv (fn [x] (inc x)) xs)))
    :truth (fn [xs] (mapv inc (mapv inc (mapv inc xs))))}])

(deftest cutover-differential-corpus
  (when (ready?)
    ;; (1) build EVERY old subject first — the fixture left the OLD surface installed.
    (let [old-fns (binding [a/*verbose* false]
                    (into {} (map-indexed
                               (fn [i {:keys [label sig body]}]
                                 (let [nm (symbol (str "corp-old-" i))]
                                   (eval (list 'ansatz.core/defn nm '[xs :- (List Nat)] sig body))
                                   [label @(resolve nm)]))
                               CORPUS)))]
      ;; (2) switch to the CLEAN surface, build every clean subject + its certified plan.
      (surf/install!)
      (doseq [[i {:keys [label sig body truth]}] (map-indexed vector CORPUS)]
        (testing label
          (let [nm (symbol (str "corp-clean-" i))
                clean-fn (binding [a/*verbose* false]
                           (eval (list 'ansatz.core/defn nm '[xs :- (List Nat)] sig body))
                           @(resolve nm))
                clean-body (.value (kenv/lookup (a/env) (nm/from-string (str nm))))
                clean-plan (diff/clean-plan-report (a/env) clean-body)
                old-fn (get old-fns label)]
            (is (:ok? (diff/result-parity clean-fn old-fn CORPUS-INPUTS))
                (str label ": clean diverged from OLD wandler"))
            (is (:ok? (diff/result-parity clean-fn truth CORPUS-INPUTS))
                (str label ": clean diverged from clojure.core ground truth"))
            (is (:verified? clean-plan)
                (str label ": the clean optimizer plan is NOT kernel-certified"))))))))
