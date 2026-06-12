(ns wandler.grace-hash-test
  "Grace-hash spill join: the certified rewrite chain that lets `foldl op e (Map.join xs ys)` be
   evaluated in budget-sized BLOCKS of the build side (O(budget) peak memory). This test composes
   the exact certificate the optimizer applies —
       foldl op e (join xs ys)
       = [congrArg (flatten_chunk B ys).symm]  foldl op e (join xs (flatten (chunk B ys)))
       = [Map.foldl_join_blockfold]            foldl (λacc blk. foldl op acc (join xs blk)) e (chunk B ys)
   — for a COUNT aggregate (op = λacc _. succ acc, where the left-commutativity hypothesis is rfl),
   and kernel-verifies the result with the AUTHORITATIVE check-constant (env/verifies?).
   See [[rel-laws-installer]] and docs/SPILL_AND_FAQ_PLAN.md."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.kmap :as km]
            [wandler.laws.relational :as rl]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [wandler.optimize :as opt]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- consOf [a x l] (e/app* (e/const' (nm "List.cons") [z]) a x l))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- natT [] (e/const' (nm "Nat") []))
(defn- flattenOf [a ls] (e/app* (e/const' (nm "List.flatten") [z]) a ls))
(defn- chunkOf [Y B l] (e/app* (e/const' (nm "List.chunk") []) Y B l))
(defn- joinOf [K X Y dec kf lf xs ys] (e/app* (e/const' (nm "Map.join") []) K X Y dec kf lf xs ys))
(defn- foldlG [B A op init l] (e/app* (e/const' (nm "List.foldl") [z z]) B A op init l))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (km/install!)
    (rl/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest grace-hash-laws-present-and-verified
  (when (ready?)
   (testing "every grace-hash law is admitted and present in the env"
    (doseq [n ["List.foldl_perm_lcomm" "Map.join_filter_form_perm" "Map.join_append_perm"
               "Map.join_nil_right" "Map.join_blockfold_perm" "Map.foldl_join_blockfold"
               "List.chunk" "List.flatten_chunk_step" "List.flatten_chunk"]]
      (is (some? (kenv/lookup (a/env) (nm n))) (str n " present"))))))

(deftest chunk-reduces-correctly
  (when (ready?)
   (testing "flatten (chunk B l) ≡ l definitionally on concrete data (the runtime carrier is sound)"
    (let [mkN (fn [n] (reduce (fn [acc _] (e/app (e/const' (nm "Nat.succ") []) acc))
                              (e/const' (nm "Nat.zero") []) (range n)))
          lst (fn [xs] (reduce (fn [acc x] (consOf (natT) x acc)) (nilOf (natT)) (reverse xs)))
          L (lst [(mkN 10) (mkN 20) (mkN 30) (mkN 40) (mkN 50)])
          st (tc/mk-tc-state (a/env))]
      (is (tc/is-def-eq st (flattenOf (natT) (chunkOf (natT) (mkN 2) L)) L))))))

(deftest grace-hash-auto-selected-by-optimizer
  (when (ready?)
    (testing "optimize-cost auto-selects grace-hash for a count-over-join when the index exceeds budget"
      (let [Nat (natT)
            PXY (prodT Nat Nat)
            dec (e/const' (nm "instDecidableEqNat") [])
            idf (e/lam "n" Nat (e/bvar 0) :default)              ; kf = lf = identity : Nat → Nat
            xs (e/fvar 71001) ys (e/fvar 71002)
            op (e/lam "acc" Nat (e/lam "p" PXY (e/app (e/const' (nm "Nat.succ") []) (e/bvar 1)) :default) :default)
            e0 (e/const' (nm "Nat.zero") [])
            join (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xs ys)
            term (e/app* (e/const' (nm "List.foldl") [z z]) Nat PXY op e0 join)
            lctx {71001 {:name "xs" :type (listOf Nat)} 71002 {:name "ys" :type (listOf Nat)}}
            res (opt/optimize-cost (a/env) term :lctx lctx :memory-budget 100.0)]
        (is (:verified? res) "grace-hash rewrite kernel-certified")
        (is (some #{:grace-hash} (:rewrites res)) "grace-hash adopted")
        (is (= :grace-hash (get-in res [:physical :strategy])) "physical strategy = grace-hash")
        (is (= "List.chunk" (let [[h _] (e/get-app-fn-args (let [[_ a] (e/get-app-fn-args (:term res))] (last a)))]
                              (when (e/const? h) (name/->string (e/const-name h)))))
            "optimized term folds over List.chunk")))))

(deftest grace-hash-executes-correctly
  (when (ready?)
    (testing "the auto-selected grace-hash plan RUNS (chunk→partition-all) and equals the naive count"
      (let [Nat (natT) PXY (prodT Nat Nat)
            dec (e/const' (nm "instDecidableEqNat") [])
            idf (e/lam "n" Nat (e/bvar 0) :default)
            xs (e/fvar 71001) ys (e/fvar 71002)
            op (e/lam "acc" Nat (e/lam "p" PXY (e/app (e/const' (nm "Nat.succ") []) (e/bvar 1)) :default) :default)
            e0 (e/const' (nm "Nat.zero") [])
            join (e/app* (e/const' (nm "Map.join") []) Nat Nat Nat dec idf idf xs ys)
            term (e/app* (e/const' (nm "List.foldl") [z z]) Nat PXY op e0 join)
            lctx {71001 {:name "xs" :type (listOf Nat)} 71002 {:name "ys" :type (listOf Nat)}}
            res (opt/optimize-cost (a/env) term :lctx lctx :memory-budget 100.0)
            ;; abstract xs,ys into a 2-arg fn term, codegen, eval
            mk-fn (fn [t] (let [t1 (e/abstract1 t 71002)
                                ly (e/lam "ys" (listOf Nat) t1 :default)
                                t2 (e/abstract1 ly 71001)
                                lx (e/lam "xs" (listOf Nat) t2 :default)]
                            (eval (a/ansatz->clj (a/env) lx []))))
            gh-fn (mk-fn (:term res))
            naive-fn (mk-fn term)
            XS [1 2 3] YS [1 1 2 3 3]]          ; matches: 1→2, 2→1, 3→2  ⇒ 5 join pairs
        (is (:verified? res) "grace-hash certified")
        (is (= 5 (long ((naive-fn XS) YS))) "naive count")
        (is (= 5 (long ((gh-fn XS) YS))) "grace-hash blockwise count equals naive")))))

(deftest grace-hash-rewrite-certified
  (when (ready?)
   (testing "the optimizer's grace-hash rewrite (count over join → blockwise) kernel-verifies"
    ;; symbolic K X Y dec kf lf xs ys B  — the rewrite is proven for all of them at once
    (let [K (e/fvar 1) X (e/fvar 2) Y (e/fvar 3) dec (e/fvar 4) kf (e/fvar 5) lf (e/fvar 6)
          xs (e/fvar 7) ys (e/fvar 8) B (e/fvar 9) e0 (e/fvar 10)
          PXY (prodT X Y) Nat (natT)
          deceqK (e/app (e/const' (nm "DecidableEq") [L1]) K)
          xToK (e/forall' "_" X K :default) yToK (e/forall' "_" Y K :default)
          ;; COUNT: op = λ(acc:Nat)(p:X×Y). Nat.succ acc
          op (e/lam "acc" Nat (e/lam "p" PXY (e/app (e/const' (nm "Nat.succ") []) (e/bvar 1)) :default) :default)
          J (fn [zs] (joinOf K X Y dec kf lf xs zs))
          chunked (chunkOf Y B ys)
          innerStep (e/lam "acc" Nat (e/lam "blk" (listOf Y)
                      (foldlG Nat PXY op (e/bvar 1) (J (e/bvar 0))) :default) :default)
          lhs (foldlG Nat PXY op e0 (J ys))
          rhs (foldlG Nat (listOf Y) innerStep e0 chunked)
          goal (-> (e/app* (e/const' (nm "Eq") [L1]) Nat lhs rhs)
                   (#(e/forall' "e" Nat (e/abstract1 % 10) :default))
                   (#(e/forall' "B" Nat (e/abstract1 % 9) :default))
                   (#(e/forall' "ys" (listOf Y) (e/abstract1 % 8) :default))
                   (#(e/forall' "xs" (listOf X) (e/abstract1 % 7) :default))
                   (#(e/forall' "lf" yToK (e/abstract1 % 6) :default))
                   (#(e/forall' "kf" xToK (e/abstract1 % 5) :default))
                   (#(e/forall' "dec" deceqK (e/abstract1 % 4) :default))
                   (#(e/forall' "Y" type0 (e/abstract1 % 3) :default))
                   (#(e/forall' "X" type0 (e/abstract1 % 2) :default))
                   (#(e/forall' "K" type0 (e/abstract1 % 1) :default)))
          ;; PROOF: Eq.trans (congrArg (λw. foldl op e (join xs w)) (flatten_chunk Y B ys).symm)
          ;;                 (Map.foldl_join_blockfold … (chunk Y B ys))
          fc (e/app* (e/const' (nm "List.flatten_chunk") []) Y B ys)        ; flatten(chunk Y B ys) = ys
          fcSym (e/app* (e/const' (nm "Eq.symm") [L1]) (listOf Y) (flattenOf Y chunked) ys fc)
          motive (e/lam "w" (listOf Y) (foldlG Nat PXY op e0 (J (e/bvar 0))) :default)
          congr (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf Y) Nat ys (flattenOf Y chunked) motive fcSym)
          ;; left-commutativity for count is rfl (succ(succ a) on both sides)
          lc (e/lam "a" Nat (e/lam "u" PXY (e/lam "v" PXY
               (e/app* (e/const' (nm "Eq.refl") [L1]) Nat
                       (e/app* op (e/app* op (e/bvar 2) (e/bvar 1)) (e/bvar 0))) :default) :default) :default)
          ;; NOTE: blockfold's "B" param is the ACCUMULATOR TYPE (Nat here), not the block size.
          bf (e/app* (e/const' (nm "Map.foldl_join_blockfold") []) K X Y dec kf lf Nat op lc e0 xs chunked)
          midL (foldlG Nat PXY op e0 (J ys))
          midR (foldlG Nat PXY op e0 (J (flattenOf Y chunked)))
          result (e/app* (e/const' (nm "Eq.trans") [L1]) Nat midL midR rhs congr bf)
          ;; close over the 10 binders to match `goal`
          close (fn [t]
                  (-> t
                      (#(e/lam "e" Nat (e/abstract1 % 10) :default))
                      (#(e/lam "B" Nat (e/abstract1 % 9) :default))
                      (#(e/lam "ys" (listOf Y) (e/abstract1 % 8) :default))
                      (#(e/lam "xs" (listOf X) (e/abstract1 % 7) :default))
                      (#(e/lam "lf" yToK (e/abstract1 % 6) :default))
                      (#(e/lam "kf" xToK (e/abstract1 % 5) :default))
                      (#(e/lam "dec" deceqK (e/abstract1 % 4) :default))
                      (#(e/lam "Y" type0 (e/abstract1 % 3) :default))
                      (#(e/lam "X" type0 (e/abstract1 % 2) :default))
                      (#(e/lam "K" type0 (e/abstract1 % 1) :default))))
          proof (close result)]
      (is (kenv/verifies? (a/env) goal proof)
          "grace-hash rewrite (foldl-count over join = blockwise fold over chunk) is kernel-certified")))))
