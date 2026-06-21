(ns wandler.filter-elim-test
  "Step 3c — certified refinement filter-elimination folded into the Subsystem-A optimizer cascade.
   A `List.filter` whose predicate the element TYPE proves redundant (always-true) is dropped with a
   kernel-checked whole-term proof (congrArg over List.filter_eq_self.mpr ∘ prove-const). Gated on
   an Init env."
  (:require [wandler.clean.optimize.filter-elim :as fe]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is testing]]))

(defn- C [s ls] (e/const' (name/from-string s) ls))

(deftest refinement-filter-eliminated
  (if-let [ke @test-env/init-full-env]
    (let [u lvl/zero u1 (lvl/succ lvl/zero)
          Nat (C "Nat" [])
          ;; element type {v:Nat // 5 ≤ v}; the filter (5 ≤ x) is redundant over it
          P (e/lam "v" Nat (e/app* (C "Nat.le" []) (e/lit-nat 5) (e/bvar 0)) :default)
          T (e/app* (C "Subtype" [u1]) Nat P)
          valx (e/app* (C "Subtype.val" [u1]) Nat P (e/bvar 0))
          pred (e/lam "x" T (e/app* (C "Nat.ble" []) (e/lit-nat 5) valx) :default)
          listT (e/app (C "List" [u]) T)
          xs (e/fvar 1)
          lctx {1 {:name "xs" :type listT}}
          ;; nested: length (filter (5≤·) xs) — the filter sits under length (true subterm congruence)
          orig (e/app* (C "List.length" [u]) T (e/app* (C "List.filter" [u]) T pred xs))
          res (fe/try-filter-elim ke orig :lctx lctx)]
      (testing "a filter the element type proves redundant is eliminated, kernel-certified"
        (is (some? res) "filter-elim fired")
        (is (true? (:verified? res)) "the whole-term rewrite re-checks via verified-rewrite?")
        (is (= (:term res) (e/app* (C "List.length" [u]) T xs)) "filter dropped → length xs")
        (is (= [:filter-elim] (:rewrites res))))
      (testing "a NON-constant filter (= x 7) is left untouched (sound: only redundant ones drop)"
        (let [pred2 (e/lam "x" T (e/app* (C "Nat.beq" []) valx (e/lit-nat 7)) :default)
              orig2 (e/app* (C "List.length" [u]) T (e/app* (C "List.filter" [u]) T pred2 xs))]
          (is (nil? (fe/try-filter-elim ke orig2 :lctx lctx))))))
    (println "SKIP refinement-filter-eliminated: no Init env")))
