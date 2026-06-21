(ns wandler.filter-elim-test
  "Step 3c — certified refinement filter-elimination folded into the Subsystem-A optimizer cascade.
   A `List.filter` whose predicate the element TYPE proves redundant (always-true) is dropped with a
   kernel-checked whole-term proof (congrArg over List.filter_eq_self.mpr ∘ prove-const). Gated on
   an Init env."
  (:require [wandler.clean.optimize.filter-elim :as fe]
            [wandler.clean.laws.uniqueness :as uniq]
            [wandler.test-env :as test-env]
            [ansatz.core :as a]
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
          (is (nil? (fe/try-filter-elim ke orig2 :lctx lctx)))))
      (testing "a CONTRADICTORY filter (val x < 5 over {v // 5≤v}) empties → length [], certified"
        (let [pred3 (e/lam "x" T (e/app* (C "Nat.blt" []) valx (e/lit-nat 5)) :default)  ; provably false
              orig3 (e/app* (C "List.length" [u]) T (e/app* (C "List.filter" [u]) T pred3 xs))
              res3 (fe/try-filter-elim ke orig3 :lctx lctx)]
          (is (some? res3) "filter-elim-empty fired")
          (is (true? (:verified? res3)) "the empty-rewrite re-checks")
          (is (= [:filter-elim-empty] (:rewrites res3)))
          (is (= (:term res3) (e/app* (C "List.length" [u]) T (e/app (C "List.nil" [u]) T)))
              "filter → [] → length []"))))
    (println "SKIP refinement-filter-eliminated: no Init env")))

(deftest distinct-eliminated-on-nodup-refinement
  (if-let [ke0 @test-env/init-full-env]
    (do (reset! a/ansatz-env ke0)
        (uniq/install!)
        ;; Env is immutable — install! produced a NEW env in the atom; use the post-install one.
        (let [ke (a/env)
              u lvl/zero u1 (lvl/succ lvl/zero)
              C C
              Nat (C "Nat" [])
              instBEq (e/app* (C "instBEqOfDecidableEq" [u]) Nat (C "instDecidableEqNat" []))
              listNat (e/app (C "List" [u]) Nat)
              ;; {l : List Nat // Nodup l} — a declared `:set`
              P (e/lam "l" listNat (e/app* (C "List.Nodup" [u]) Nat (e/bvar 0)) :default)
              subT (e/app* (C "Subtype" [u1]) listNat P)
              s (e/fvar 1)
              lctx {1 {:name "s" :type subT}}
              xs (e/app* (C "Subtype.val" [u1]) listNat P s)   ; the underlying List Nat
              orig (e/app* (C "List.length" [u]) Nat
                           (e/app* (C "List.eraseDups" [u]) Nat instBEq xs))
              res (fe/try-distinct-elim ke orig :lctx lctx)]
          (testing "eraseDups over a Nodup-refined (declared :set) list is dropped, kernel-certified"
            (is (some? res) "distinct-elim fired")
            (is (true? (:verified? res)) "the whole-term rewrite re-checks (LawfulBEq synthesized)")
            (is (= [:distinct-elim] (:rewrites res)))
            (is (= (:term res) (e/app* (C "List.length" [u]) Nat xs)) "dedup gone → length (val s)"))
          (testing "an eraseDups over a PLAIN (non-refined) list is NOT eliminated (sound)"
            (let [plain (e/fvar 2)
                  lctx2 {2 {:name "ys" :type listNat}}
                  orig2 (e/app* (C "List.length" [u]) Nat
                                (e/app* (C "List.eraseDups" [u]) Nat instBEq plain))]
              (is (nil? (fe/try-distinct-elim ke orig2 :lctx lctx2)))))))
    (println "SKIP distinct-eliminated-on-nodup-refinement: no Init env")))
