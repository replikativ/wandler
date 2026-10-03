(ns wandler.laws.reorder
  "Phase 8 Level 2 (clean tree) — the COUNT drive-direction reorder, re-proven as a THIN corollary of
   the Perm-FREE aggregate capstone `Map_aggJoin_reorder` (wandler.laws.bucket). This RETIRES the
   entire old `List.Perm` cluster (~1030 LOC in wandler.laws.proofs: join_comm/bucket_perm/flatMap_*_perm
   /Perm.length_eq …): the old engine proved `Map.join_length_comm` by bag-permutation of the
   materialized pairs; here it is the count instance of the aggregate Fubini.

   Chain:
     instWAddMonoid_Nat / instWSemiring_Nat — the Nat carrier instances (ansatz.prelude.algebra).
     instCommNatAdd                          — Std.Commutative Nat (+) (from Nat.add_comm, defeq).
     List.length_eq_wsum_one                 — length l = wsum ℕ⁺ (map (λ_.1) l)  (count = Σ 1).
     Map.join_length_comm                    — length(join kf lf xs ys) = length(join lf kf ys xs):
       rewrite both lengths to the Σ-of-1 form, then `Map_aggJoin_reorder` at the count monoid
       (Nat,+,0, commutative) with weight f = λx y. 1 closes it by def-eq. NO List.Perm."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.prelude.algebra :as alg]
            [wandler.algebra :as algebra]
            [wandler.laws.bucket :as bucket]))

(def ^:private L1 (lvl/succ lvl/zero))
(defn- kc [s] (e/const' (nm/from-string s) []))

(defn install!
  "Install the count drive-direction reorder + its Nat-carrier instances (idempotent). Builds on
   `bucket/install!` (which proves the aggregate `Map_aggJoin_reorder`). Returns :installed."
  []
  (bucket/install!)

  ;; Nat WAddMonoid / WSemiring instances — kernel-verified from Init lemmas (ansatz.prelude.algebra).
  (algebra/install-semiring-instance! "Nat" alg/nat-row)

  ;; Std.Commutative Nat (+): the commutativity instance the aggregate Fubini reorder needs. The op is
  ;; `WAddMonoid.add Nat instWAddMonoid_Nat` (≡ Nat.add); `Nat.add_comm` discharges it by def-eq.
  (a/install-guarded! "instCommNatAdd"
                      (swap! a/ansatz-env env/check-constant
                             (env/mk-def (nm/from-string "instCommNatAdd") []
                                         (e/app* (e/const' (nm/from-string "Std.Commutative") [L1]) (kc "Nat")
                                                 (e/app* (kc "WAddMonoid.add") (kc "Nat") (kc "instWAddMonoid_Nat")))
                                         (e/app* (e/const' (nm/from-string "Std.Commutative.mk") [L1]) (kc "Nat")
                                                 (e/app* (kc "WAddMonoid.add") (kc "Nat") (kc "instWAddMonoid_Nat"))
                                                 (kc "Nat.add_comm")))))
  (algebra/register-instance! "instCommNatAdd")

  ;; length l = wsum ℕ⁺ (map (λ_.1) l) — count expressed as the additive aggregate of ones. The bridge
  ;; that lets the materialized `List.length` ride the aggregate reorder. (Unfold instWAddMonoid_Nat so
  ;; the `WAddMonoid.add` projection reduces to `Nat.add` for `omega`.)
  (a/deftheorem List.length_eq_wsum_one [T :- Type, l :- (List T)]
    (= Nat (List.length T l)
       (wsum (List.map (fn [_ :- T] (Nat.succ Nat.zero)) l)))
    (induction l)
    (all_goals (simp_all [List.length_nil List.length_cons List.map_nil List.map_cons
                          wsum.eq_1 wsum.eq_2 instWAddMonoid_Nat WAddMonoid.add WAddMonoid.zero]))
    (all_goals (try (omega))))

  ;; Map.join_length_comm — the count drive-direction reorder, as the count instance of the aggregate
  ;; Fubini `Map_aggJoin_reorder`. What the optimizer's `try-join-reorder` consumes. No List.Perm.
  (a/deftheorem Map.join_length_comm
    [K :- Type, X :- Type, Y :- Type, dec :- (DecidableEq K),
     kf :- (=> X K), lf :- (=> Y K), xs :- (List X), ys :- (List Y)]
    (= Nat (List.length (Prod X Y) (Map.join K X Y dec kf lf xs ys))
       (List.length (Prod Y X) (Map.join K Y X dec lf kf ys xs)))
    (rw [(List.length_eq_wsum_one (Prod X Y) (Map.join K X Y dec kf lf xs ys))])
    (rw [(List.length_eq_wsum_one (Prod Y X) (Map.join K Y X dec lf kf ys xs))])
    (exact (Map_aggJoin_reorder K X Y Nat dec instWAddMonoid_Nat instCommNatAdd kf lf
                                (fn [x :- X] (fn [y :- Y] (Nat.succ Nat.zero))) xs ys)))
  :installed)
