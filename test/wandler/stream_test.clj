(ns wandler.stream-test
  "Windowed stream processing over a coalgebra (seed,step): the kernel-certified boundary law
   `Stream.take_smap` (mapping a stream then windowing = windowing then List.map), and an end-to-end
   demo where the windowed pipeline `sum (window n (smap double source))` is certified equal to
   `sum (map double (window n source))` AND executes over an INFINITE Clojure lazy seq `(range)` —
   forcing only the window. See wandler.stream + [[architecture-and-lift-plan]]."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.stream :as stream]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- consOf [a x l] (e/app* (e/const' (nm "List.cons") [z]) a x l))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- mkP [X Y x y] (e/app* (e/const' (nm "Prod.mk") [z z]) X Y x y))
(defn- optionOf [A] (e/app (e/const' (nm "Option") [z]) A))
(defn- someOf [A x] (e/app* (e/const' (nm "Option.some") [z]) A x))
(defn- natT [] (e/const' (nm "Nat") []))
(defn- mapL [A B f l] (e/app* (e/const' (nm "List.map") [z z]) A B f l))
(defn- ut [A S step n s] (e/app* (e/const' (nm "Stream.unfoldTake") []) A S step n s))

(defn- setup [f]
  (when-let [kenv @test-env/init-full-env]
    (reset! a/ansatz-env kenv)
    (stream/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest stream-laws-present
  (when (ready?)
    (testing "unfoldTake (def) + take_smap (law) are admitted"
      (is (some? (kenv/lookup (a/env) (nm "Stream.unfoldTake"))))
      (is (some? (kenv/lookup (a/env) (nm "Stream.take_smap")))))))

(deftest unfold-take-reduces-on-a-concrete-stream
  (when (ready?)
    (testing "the naturals coalgebra step s = some (s, s+1): take 3 from 0 ≡ [0,1,2]"
      (let [stepNat (e/lam "s" (natT) (someOf (prodT (natT) (natT))
                      (mkP (natT) (natT) (e/bvar 0) (e/app (e/const' (nm "Nat.succ") []) (e/bvar 0)))) :default)
            lhs (ut (natT) (natT) stepNat (e/lit-nat 3) (e/lit-nat 0))
            rhs (consOf (natT) (e/lit-nat 0) (consOf (natT) (e/lit-nat 1) (consOf (natT) (e/lit-nat 2) (nilOf (natT)))))
            st (tc/mk-tc-state (a/env))]
        (is (tc/is-def-eq st lhs rhs))))))

(deftest windowed-stream-pipeline-certified-and-runs-over-infinite-source
  (when (ready?)
    (testing "sum∘window∘smap = sum∘map∘window (certified for all step,source) AND runs over (range)"
      (let [A (natT) S (listOf (natT))
            stepFv (e/fvar 10) sFv (e/fvar 11) n (e/lit-nat 5)
            double (e/lam "x" (natT) (e/app* (e/const' (nm "Nat.add") []) (e/bvar 0) (e/bvar 0)) :default)
            addC (e/const' (nm "Nat.add") []) zeroN (e/const' (nm "Nat.zero") [])
            foldlG (fn [l] (e/app* (e/const' (nm "List.foldl") [z z]) (natT) (natT) addC zeroN l))
            sm (stream/smap-step A A S double stepFv)
            pre  (foldlG (ut A S sm n sFv))                         ; sum (window (smap double src))
            post (foldlG (mapL A A double (ut A S stepFv n sFv)))   ; sum (map double (window src))
            tsm (e/app* (e/const' (nm "Stream.take_smap") []) A A S double stepFv n sFv)
            cert (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf A) (natT)
                         (ut A S sm n sFv) (mapL A A double (ut A S stepFv n sFv))
                         (e/lam "l" (listOf A) (foldlG (e/bvar 0)) :default) tsm)
            stepTy (e/forall' "_" S (optionOf (prodT A S)) :default)
            goalC (-> (e/app* (e/const' (nm "Eq") [L1]) (natT) pre post)
                      (#(e/forall' "s" S (e/abstract1 % 11) :default))
                      (#(e/forall' "step" stepTy (e/abstract1 % 10) :default)))
            proofC (-> cert
                       (#(e/lam "s" S (e/abstract1 % 11) :default))
                       (#(e/lam "step" stepTy (e/abstract1 % 10) :default)))
            mk-fn (fn [t] (let [t1 (e/abstract1 t 11) ls (e/lam "s" S t1 :default)
                                t2 (e/abstract1 ls 10) lst (e/lam "step" stepTy t2 :default)]
                            (eval (a/ansatz->clj (a/env) lst []))))
            uncons (fn [l] (when (seq l) [(first l) (rest l)]))
            pre-fn (mk-fn pre) post-fn (mk-fn post)]
        (is (kenv/verifies? (a/env) goalC proofC)
            "windowed-smap = window-then-map is kernel-certified (∀ step, source)")
        ;; runs over the INFINITE (range) — unfold-take forces only the 5-element window
        (is (= 20 (long ((pre-fn uncons) (range)))) "sum∘window∘smap over (range) window 5")
        (is (= 20 (long ((post-fn uncons) (range)))) "sum∘map∘window over (range) window 5")
        (is (= 20 (reduce + (map #(* 2 %) (take 5 (range))))) "naive reference")))))
