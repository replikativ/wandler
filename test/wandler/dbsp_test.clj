(ns wandler.dbsp-test
  "Verified INCREMENTAL view maintenance (DBSP, insert-only) — rung 4 of the streaming ladder. The two
   increment laws kernel-verify, and the runtime maintains a running count over delta batches that
   EQUALS the batch recomputation:
     LINEAR   count∘filter  — filter_count_incr.
     BILINEAR count∘join    — join_count_incr, the DIFFERENTIAL JOIN (semi-naive: join only the new
              build tuples against the fixed probe, accumulate). count(join xs (⋃ dys_i)) = Σ count(join xs dys_i).
   See wandler.dbsp + [[windowed-stream-coalgebra]]."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.rel-laws :as rl]
            [wandler.dbsp :as dbsp]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- natT [] (e/const' (nm "Nat") []))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (km/install!) (rl/install!) (dbsp/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest dbsp-laws-present-and-verified
  (when (ready?)
    (testing "the IVM laws are admitted (each kernel check-constant'd) — insert-only AND Z-set"
      (doseq [n ["List.filter_count_incr" "Map.join_count_incr"
                 "Map.join_count_incr_left" "Map.join_count_product" "List.sum_filter_incr"
                 "Zset.weight" "Zset.foldl_int_init" "Zset.weight_append" "Zset.filter_weight_incr"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present"))))))

(deftest sum-where-aggregate-incremental-equals-batch
  (when (ready?)
    (testing "COMPOSITION: incremental `SELECT sum(g) WHERE p` over delta batches = batch (sum_filter_incr)"
      (let [Nat (natT)
            p (e/lam "x" Nat (e/app* (e/const' (nm "Nat.blt") []) (e/lit-nat 2) (e/bvar 0)) :default)  ; x>2
            g (e/lam "x" Nat (e/app* (e/const' (nm "Nat.add") []) (e/bvar 0) (e/bvar 0)) :default)      ; 2·x
            win (e/fvar 50)
            agg (e/app* (e/const' (nm "List.foldl") [z z]) Nat Nat
                        (e/lam "a" Nat (e/lam "x" Nat (e/app* (e/const' (nm "Nat.add") []) (e/bvar 1)
                                          (e/app g (e/bvar 0))) :default) :default)
                        (e/const' (nm "Nat.zero") [])
                        (e/app* (e/const' (nm "List.filter") [z]) Nat p win))
            qfn (eval (a/ansatz->clj (a/env) (e/lam "win" (listOf Nat) (e/abstract1 agg 50) :default) []))
            naive (fn [xs] (reduce + 0 (map #(* 2 %) (filter #(> (long %) 2) xs))))
            deltas [[1 3 5] [2 4] [3 3]]]   ; windows of a stream; Σ 2x where x>2
        (is (= (qfn (apply concat deltas)) (naive (apply concat deltas))) "compiled agg = naive")
        (is (= (qfn (apply concat deltas)) (dbsp/ivm qfn + 0 deltas))
            "incremental Σ over delta windows = batch (the composition certificate)")))))

(deftest join-product-rule-both-sides-change
  (when (ready?)
    (testing "BILINEAR product rule: count(join (xs⊎dxs)(ys⊎dys)) = the 4-term cross-product (DBSP equi_join_bilinear)"
      (let [Nat (natT)
            dec (e/const' (nm "instDecidableEqNat") [])
            idf (e/lam "n" Nat (e/bvar 0) :default)
            xsv (e/fvar 41) ysv (e/fvar 42)
            q (e/app* (e/const' (nm "List.length") [z]) (e/app* (e/const' (nm "Prod") [z z]) Nat Nat)
                      (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xsv ysv))
            cnt (eval (a/ansatz->clj (a/env)
                        (e/lam "xs" (listOf Nat)
                          (e/abstract1 (e/lam "ys" (listOf Nat) (e/abstract1 q 42) :default) 41) :default) []))
            join-count (fn [xs ys] (long ((cnt xs) ys)))
            xs0 [1 2] dxs [2 3] ys0 [1 2] dys [2 3]]
        (is (= (join-count (concat xs0 dxs) (concat ys0 dys))            ; batch (both sides grown)
               (+ (join-count xs0 ys0)   (join-count dxs ys0)            ; old⋈old + new⋈old
                  (join-count xs0 dys)   (join-count dxs dys)))          ; old⋈new + new⋈new
            "join over both-side deltas = Σ of the 4 cross-products")
        (is (= 6 (join-count (concat xs0 dxs) (concat ys0 dys))) "the batch count")))))

(deftest zset-deletions-net-count-with-retractions
  (when (ready?)
    (testing "Z-set weight (with NEGATIVE weights = deletions) maintained incrementally = batch, AND can DECREASE"
      ;; entries are [element weight]; weight −1 retracts. ℤ is a group ⇒ weight_append handles deletes.
      (let [deltas [[[1 1] [2 1] [3 1]]    ; insert 1,2,3
                    [[2 -1]]               ; RETRACT 2
                    [[1 1]]]               ; insert another 1
            running (reductions + 0 (map dbsp/zweight deltas))]   ; 0,3,2,3
        (is (= (dbsp/zweight (apply concat deltas))               ; batch net weight
               (dbsp/ivm dbsp/zweight + 0 deltas)) "incremental net weight = batch (weight_append)")
        (is (= 3 (dbsp/ivm dbsp/zweight + 0 deltas)) "net = 3 insertions − 1 deletion + 1 = 3")
        (is (= [0 3 2 3] (vec running)) "the running count DROPS to 2 on the retraction — deletions work")))))

(deftest zset-filter-weight-incremental-with-deletions
  (when (ready?)
    (testing "incremental FILTERED weight (σ_P linear) with deletions = batch"
      (let [pred #(> (long %) 1)                       ; keep elements > 1
            deltas [[[2 1] [3 1] [1 1]]   ; +2,+3,+1
                    [[2 -1]]              ; retract 2
                    [[3 1]]]              ; +3
            q #(dbsp/zweight (dbsp/zfilter pred %))]
        (is (= (q (apply concat deltas)) (dbsp/ivm q + 0 deltas))
            "Σ weight(σ_P dD_i) = weight(σ_P (⋃ dD_i))  — filter_weight_incr")
        (is (= 2 (dbsp/ivm q + 0 deltas)) "elements>1: +2 +3 −2 +3 = net weight 2")))))

(deftest filter-count-incremental-equals-batch
  (when (ready?)
    (testing "LINEAR: count∘filter maintained incrementally over delta batches = batch recomputation"
      (let [Nat (natT)
            pred (e/lam "x" Nat (e/app* (e/const' (nm "Nat.blt") []) (e/lit-nat 1) (e/bvar 0)) :default) ; x>1
            win (e/fvar 30)
            q (e/app* (e/const' (nm "List.length") [z]) Nat
                      (e/app* (e/const' (nm "List.filter") [z]) Nat pred win))
            qfn (eval (a/ansatz->clj (a/env) (e/lam "win" (listOf Nat) (e/abstract1 q 30) :default) []))
            deltas [[1 2] [3 1] [2]]]
        (is (= (qfn (apply concat deltas))                 ; batch
               (dbsp/ivm qfn + 0 deltas))                  ; incremental
            "Σ count(filter p dD_i) = count(filter p (⋃ dD_i))")))))

(deftest join-count-incremental-equals-batch-differential-join
  (when (ready?)
    (testing "BILINEAR differential join (semi-naive): count(join xs (⋃ dys_i)) = Σ count(join xs dys_i)"
      (let [Nat (natT)
            dec (e/const' (nm "instDecidableEqNat") [])
            idf (e/lam "n" Nat (e/bvar 0) :default)          ; kf = lf = identity (join on equality)
            xsv (e/fvar 31) ysv (e/fvar 32)
            q (e/app* (e/const' (nm "List.length") [z]) (e/app* (e/const' (nm "Prod") [z z]) Nat Nat)
                      (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xsv ysv))
            ;; λxs ys. count (join xs ys)
            qfn2 (eval (a/ansatz->clj (a/env)
                         (e/lam "xs" (listOf Nat)
                           (e/abstract1 (e/lam "ys" (listOf Nat) (e/abstract1 q 32) :default) 31) :default) []))
            xs0 [1 2 3]                                       ; the FIXED probe relation
            qfn (fn [ys] ((qfn2 xs0) ys))                    ; per-delta query: join new build tuples
            deltas [[1 1] [2 3 3] [1 2]]]                    ; streamed build-side deltas
        (is (= (qfn (apply concat deltas)) 7) "batch count over the union")
        (is (= 7 (dbsp/ivm qfn + 0 deltas)) "incremental = batch (the join_count_incr certificate)")))))
