(ns wandler.groupby-test
  "Path 2b — GROUP-BY ELIMINATION capability proofs: under a declared unique key, a group-by bucket is
   a singleton, so denormalize-each-row-with-its-group collapses to a map over rows. Installs +
   kernel-verifies the laws. Gated on the full Init env (needs Map/group_by/bucket machinery)."
  (:require [wandler.clean.laws.groupby :as groupby]
            [wandler.clean.optimize.filter-elim :as fe]
            [wandler.clean.optimize :as opt]
            [wandler.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is testing]]))

(defn- verifies? [s]
  (let [c (env/lookup (a/env) (name/from-string s))]
    (boolean (and c (env/verifies? (a/env) (.type c) (.value c))))))

(defn- C [s ls] (e/const' (name/from-string s) ls))

(deftest groupby-elimination-laws-kernel-verify
  (if-let [ke @test-env/init-full-env]
    (do (reset! a/ansatz-env ke)
        (groupby/install!)
        (testing "explicit-argument map_congr_left wrapper (lift bridge)"
          (is (verifies? "List.map_congr_left_expl")
              "∀a∈l, f a = g a ⊢ map f l = map g l"))
        (testing "a unique-key bucket lookup returns the singleton (bucket_content ∘ bucket_singleton)"
          (is (verifies? "Map.bucket_singleton_lookup")
              "Nodup (map kf l) → r ∈ l → getD (lookup (kf r) (group_by kf l)) [] = [r]"))
        (testing "THE group-by-elimination law: group_by + per-row lookup collapses to map-over-rows"
          (is (verifies? "Map.groupby_self_elim")
              "Nodup (map kf xs) → map (λr. lookup (kf r) (group_by kf xs)) xs = map (λr. [r]) xs — sound only with the key")))
    (println "SKIP groupby-elimination-laws-kernel-verify: no Init env")))

(deftest groupby-elim-strategy
  ;; The optimizer strategy `try-groupby-elim`: a `map (λr. getD (lookup (kf r) (group_by kf xs)) []) xs`
  ;; over a declared-unique-key (`Nodup (map kf ·)`-refined) relation collapses to `map (λr. [r]) xs`,
  ;; kernel-certified by Map.groupby_self_elim. UNSOUND without the key — only a proof licenses it.
  (if-let [ke0 @test-env/init-full-env]
    (do (reset! a/ansatz-env ke0)
        (groupby/install!)
        (let [ke (a/env)
              u lvl/zero u1 (lvl/succ lvl/zero)
              Nat (C "Nat" []) listNat (e/app (C "List" [u]) Nat)
              dec (C "instDecidableEqNat" []) kf (C "Nat.succ" [])          ; a non-trivial key projection
              ;; carrier: {xs : List Nat // Nodup (map kf xs)} — a declared UNIQUE KEY
              P (e/lam "l" listNat (e/app* (C "List.Nodup" [u]) Nat
                                           (e/app* (C "List.map" [u u]) Nat Nat kf (e/bvar 0))) :default)
              s (e/fvar 1) lctx {1 {:name "s" :type (e/app* (C "Subtype" [u1]) listNat P)}}
              xs (e/app* (C "Subtype.val" [u1]) listNat P s)
              ;; map (λr. getD (lookup (kf r) (group_by kf xs)) []) xs  (Map ops are level-monomorphic)
              pred (e/lam "r" Nat
                          (e/app* (C "Option.getD" [u]) listNat
                                  (e/app* (C "Map.lookup" []) Nat listNat dec (e/app kf (e/bvar 0))
                                          (e/app* (C "Map.group_by" []) Nat Nat dec kf xs))
                                  (e/app (C "List.nil" [u]) Nat)) :default)
              orig (e/app* (C "List.length" [u]) listNat (e/app* (C "List.map" [u u]) Nat listNat pred xs))
              rhs-map (e/app* (C "List.map" [u u]) Nat listNat
                              (e/lam "r" Nat (e/app* (C "List.cons" [u]) Nat (e/bvar 0) (e/app (C "List.nil" [u]) Nat)) :default)
                              xs)
              expected (e/app* (C "List.length" [u]) listNat rhs-map)
              res (fe/try-groupby-elim ke orig :lctx lctx)]
          (testing "group_by self-lookup over a key-refined relation is eliminated, kernel-certified"
            (is (some? res) "groupby-elim fired")
            (is (true? (:verified? res)) "the whole-term rewrite re-checks (LawfulBEq synthesized)")
            (is (= [:groupby-elim] (:rewrites res)))
            (is (= (:term res) expected) "group_by + lookups gone → map (λr. [r]) xs"))
          (testing "the full cost-driven cascade ADOPTS groupby-elim"
            (let [oc (opt/optimize-cost ke orig :lctx lctx)]
              (is (= [:groupby-elim] (vec (:rewrites oc))))
              (is (true? (:verified? oc)))
              (is (= (:term oc) expected))))
          (testing "a group_by self-lookup over a PLAIN (non-key-refined) relation is NOT eliminated"
            (let [plain (e/fvar 2) lctx2 {2 {:name "ys" :type listNat}}
                  pred2 (e/lam "r" Nat
                               (e/app* (C "Option.getD" [u]) listNat
                                       (e/app* (C "Map.lookup" []) Nat listNat dec (e/app kf (e/bvar 0))
                                               (e/app* (C "Map.group_by" []) Nat Nat dec kf plain))
                                       (e/app (C "List.nil" [u]) Nat)) :default)
                  orig2 (e/app* (C "List.length" [u]) listNat (e/app* (C "List.map" [u u]) Nat listNat pred2 plain))]
              (is (nil? (fe/try-groupby-elim ke orig2 :lctx lctx2)))))))
    (println "SKIP groupby-elim-strategy: no Init env")))
