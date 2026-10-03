(ns wandler.laws.groupby-join
  "Capstone #184 — GROUP-BY-OVER-JOIN factorization foundation.

   The optimizer's group-by analytics shape is `map (λg. reduce ⊕ e (map h g)) (vals (group-by key
   zs))` — aggregate each bucket of a grouping. When `zs` is a `Map.join`, the naive plan MATERIALIZES
   the join (the |xs|·|ys| product) just to bucket+sum it. To factor that away we need to rewrite the
   driver into a SCATTER (foldByKey) that never builds the pairs — which rests on the theorem proved
   here:

     Map.scatter_groupby_entries (LEMMA A) :  the entries of a `scatter` (a foldl that ⊕-accumulates
       h(z) into bucket key(z)) correspond, value-by-value, to the entries of `group_by key zs` with
       each bucket replaced by its `wsum`.  i.e.  group-then-reduce  =  reduce-by-key.

   The proof spine: an entries-correspondence invariant R(Mgb,Mgs) := `entries Mgs = map T (entries
   Mgb)` (T = (k,g) ↦ (k, wsum (map h g))) is preserved by ONE scatter/group_by step (Map.scatter_
   groupby_step), so a single induction over `zs` lifts it from the empty maps to the whole fold.

   COMMUTATIVITY-FREE: `Map.group_by`/`Map.insert` PREPEND into a bucket (z :: bucket), so the gb-bucket
   aggregate is `⊕ (h z) (wsum old)`. We therefore define the scatter step in the SAME order — `add (h z)
   (lookup-val)` — and the per-step head equation (Map.scatter_head_val) closes DEFINITIONALLY, needing
   no monoid commutativity. So LEMMA A holds for ANY WAddMonoid, not just commutative ones.

   Map = `{ l : List (K×V) // NodupKeys l }`; `Map.entries` = `.val`; `Map.insert k v m` =
   `⟨(k,v) :: m.val.filter (·.fst≠k), _⟩` (prepend + drop old key). The foundation lemmas
   (insert/empty/lookup ↔ entries) are all `rfl`. Requires the Init store + wandler.kmap + the wsum
   prelude (wandler.laws.frame).

   The Map-unfolding rewrites below use explicit `rw` (fully-applied, levels pinned) for controlled
   single-step rewriting under binders — clearer than `simp only` for a one-shot unfold."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.prelude.algebra :as alg]
            [wandler.algebra :as algebra]
            [wandler.laws.bucket :as bucket]
            [wandler.laws.frame :as frame]
            [wandler.kmap :as kmap]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))
(defn installed? [] (has? "Map.groupby_reduce_join_factor"))

(defn- gbj-foundation!
  "Foundation + keystone lemmas (Map↔entries rfl bridges, lookup/filter plumbing, the
   scatter/group_by correspondence keystone). Split out of install! to keep each JVM method
   under the bytecode size limit."
  []
    ;; ── foundation: Map ops ↔ entries (all rfl; entries = Subtype.val) ──────────
  (a/deftheorem Map.insert_entries
    [K :- Type, V :- Type, dec :- (DecidableEq K), k :- K, v :- V, m :- (Map K V)]
    (= (List (Prod K V))
       (Map.entries K V (Map.insert K V dec k v m))
       (List.cons (Prod K V) (Prod.mk K V k v)
                  (List.filter (Prod K V)
                               (fn [p :- (Prod K V)] (Bool.not (BEq.beq K (instBEqOfDecidableEq K dec) (Prod.fst K V p) k)))
                               (Map.entries K V m))))
    (rfl))
  (a/deftheorem Map.empty_entries
    [K :- Type, V :- Type]
    (= (List (Prod K V)) (Map.entries K V (Map.empty K V)) (List.nil (Prod K V)))
    (rfl))
  (a/deftheorem Map.lookup_entries
    [K :- Type, V :- Type, dec :- (DecidableEq K), k :- K, m :- (Map K V)]
    (= (Option V) (Map.lookup K V dec k m)
       (List.lookup K V (instBEqOfDecidableEq K dec) k (Map.entries K V m)))
    (rfl))

    ;; ── lookup through a key-preserving value map, getD form ────────────────────
    ;; getD (lookup k (map (λp.(fst p, φ(snd p))) l)) (φ d) = φ (getD (lookup k l) d)
  (a/deftheorem List.getD_lookup_map_val
    [A :- Type, W :- Type, S :- Type, be :- (BEq A) :inst, k :- A, phi :- (=> W S), d :- W, l :- (List (Prod A W))]
    (= S
       (Option.getD S (List.lookup A S be k
                                   (List.map (Prod A W) (Prod A S)
                                             (fn [p :- (Prod A W)] (Prod.mk A S (Prod.fst A W p) (phi (Prod.snd A W p)))) l)) (phi d))
       (phi (Option.getD W (List.lookup A W be k l) d)))
    (induction l)
    (all_goals (try (cases head)))
    (all_goals (try (simp [List.map_nil List.map_cons List.lookup_nil List.lookup_cons Prod.fst Prod.snd Option.getD])))
    (all_goals (try (by_cases (BEq.beq A be k fst))))
    (all_goals (try (simp_all [List.lookup_cons Prod.fst Prod.snd cond_true cond_false Option.getD]))))

    ;; same, specialised to φ = (λg. wsum (map h g)), defaults zero / nil (so the
    ;; defaults match SYNTACTICALLY where the head equation needs them)
  (a/deftheorem List.getD_lookup_map_wsum
    [K2 :- Type, Z :- Type, S :- Type, be :- (BEq K2) :inst, mon :- (WAddMonoid S) :inst,
     h :- (=> Z S), k :- K2, l :- (List (Prod K2 (List Z)))]
    (= S
       (Option.getD S (List.lookup K2 S be k
                                   (List.map (Prod K2 (List Z)) (Prod K2 S)
                                             (fn [p :- (Prod K2 (List Z))] (Prod.mk K2 S (Prod.fst K2 (List Z) p)
                                                                                    (wsum (List.map Z S h (Prod.snd K2 (List Z) p))))) l))
                    (WAddMonoid.zero mon))
       (wsum (List.map Z S h (Option.getD (List Z) (List.lookup K2 (List Z) be k l) (List.nil Z)))))
    (induction l)
    (all_goals (try (cases head)))
    (all_goals (try (simp [List.map_nil List.map_cons List.lookup_nil List.lookup_cons Prod.fst Prod.snd
                           Option.getD wsum.eq_1])))
    (all_goals (try (by_cases (BEq.beq K2 be k fst))))
    (all_goals (try (simp_all [Option.getD Prod.fst Prod.snd cond_true cond_false wsum.eq_1 List.map_nil]))))

    ;; filter-by-fst commutes with a key-preserving value map (T preserves fst ⇒ filter_map fuses)
  (a/deftheorem List.filter_fst_map_comm
    [A :- Type, W :- Type, S :- Type, be :- (BEq A) :inst, k :- A, phi :- (=> W S), l :- (List (Prod A W))]
    (= (List (Prod A S))
       (List.filter (Prod A S) (fn [p :- (Prod A S)] (Bool.not (BEq.beq A be (Prod.fst A S p) k)))
                    (List.map (Prod A W) (Prod A S)
                              (fn [p :- (Prod A W)] (Prod.mk A S (Prod.fst A W p) (phi (Prod.snd A W p)))) l))
       (List.map (Prod A W) (Prod A S)
                 (fn [p :- (Prod A W)] (Prod.mk A S (Prod.fst A W p) (phi (Prod.snd A W p))))
                 (List.filter (Prod A W) (fn [p :- (Prod A W)] (Bool.not (BEq.beq A be (Prod.fst A W p) k))) l)))
    (simp [List.filter_map Function.comp Prod.fst Prod.snd]))

    ;; ── HEAD: the per-key value equation (commutativity-free, flipped scatter order) ──
    ;; ⊕ (h z) (getD (lookup kz Mgs) 0) = wsum (map h (z :: getD (lookup kz Mgb) []))
  (a/deftheorem Map.scatter_head_val
    [K2 :- Type, Z :- Type, S :- Type, dec2 :- (DecidableEq K2), mon :- (WAddMonoid S) :inst,
     h :- (=> Z S), kz :- K2, z :- Z, Mgb :- (Map K2 (List Z)), Mgs :- (Map K2 S)]
    (=> (= (List (Prod K2 S)) (Map.entries K2 S Mgs)
           (List.map (Prod K2 (List Z)) (Prod K2 S)
                     (fn [p :- (Prod K2 (List Z))] (Prod.mk K2 S (Prod.fst K2 (List Z) p)
                                                            (wsum (List.map Z S h (Prod.snd K2 (List Z) p))))) (Map.entries K2 (List Z) Mgb)))
        (= S
           (WAddMonoid.add mon (h z) (Option.getD S (Map.lookup K2 S dec2 kz Mgs) (WAddMonoid.zero mon)))
           (wsum (List.map Z S h (List.cons Z z (Option.getD (List Z) (Map.lookup K2 (List Z) dec2 kz Mgb) (List.nil Z)))))))
    (intro hcorr)
    (rw (Map.lookup_entries K2 S dec2 kz Mgs))
    (rw (Map.lookup_entries K2 (List Z) dec2 kz Mgb))
    (rw hcorr)
    (rw (List.getD_lookup_map_wsum K2 Z S (instBEqOfDecidableEq K2 dec2) mon h kz (Map.entries K2 (List Z) Mgb))))

    ;; ── STEP: one scatter/group_by step preserves the entries-correspondence ─────
  (a/deftheorem Map.scatter_groupby_step
    [K2 :- Type, Z :- Type, S :- Type, dec2 :- (DecidableEq K2), mon :- (WAddMonoid S) :inst,
     key :- (=> Z K2), h :- (=> Z S), z :- Z, Mgb :- (Map K2 (List Z)), Mgs :- (Map K2 S)]
    (=> (= (List (Prod K2 S)) (Map.entries K2 S Mgs)
           (List.map (Prod K2 (List Z)) (Prod K2 S)
                     (fn [p :- (Prod K2 (List Z))] (Prod.mk K2 S (Prod.fst K2 (List Z) p)
                                                            (wsum (List.map Z S h (Prod.snd K2 (List Z) p))))) (Map.entries K2 (List Z) Mgb)))
        (= (List (Prod K2 S))
           (Map.entries K2 S
                        (Map.insert K2 S dec2 (key z)
                                    (WAddMonoid.add mon (h z) (Option.getD S (Map.lookup K2 S dec2 (key z) Mgs) (WAddMonoid.zero mon))) Mgs))
           (List.map (Prod K2 (List Z)) (Prod K2 S)
                     (fn [p :- (Prod K2 (List Z))] (Prod.mk K2 S (Prod.fst K2 (List Z) p)
                                                            (wsum (List.map Z S h (Prod.snd K2 (List Z) p)))))
                     (Map.entries K2 (List Z)
                                  (Map.insert K2 (List Z) dec2 (key z)
                                              (List.cons Z z (Option.getD (List Z) (Map.lookup K2 (List Z) dec2 (key z) Mgb) (List.nil Z))) Mgb)))))
    (intro hcorr)
    (rw (Map.insert_entries K2 S dec2 (key z)
                            (WAddMonoid.add mon (h z) (Option.getD S (Map.lookup K2 S dec2 (key z) Mgs) (WAddMonoid.zero mon))) Mgs))
    (rw (Map.insert_entries K2 (List Z) dec2 (key z)
                            (List.cons Z z (Option.getD (List Z) (Map.lookup K2 (List Z) dec2 (key z) Mgb) (List.nil Z))) Mgb))
    (rw (Map.scatter_head_val K2 Z S dec2 mon h (key z) z Mgb Mgs hcorr))
    (rw hcorr)
    (rw (List.filter_fst_map_comm K2 (List Z) S (instBEqOfDecidableEq K2 dec2) (key z)
                                  (fn [g :- (List Z)] (wsum (List.map Z S h g))) (Map.entries K2 (List Z) Mgb))))

    ;; ── LEMMA A: group-then-reduce = reduce-by-key (scatter), at the entries level ──
    ;; ∀ Mgb Mgs, R(Mgb,Mgs) → entries (scatter zs Mgs) = map T (entries (group_by zs Mgb))
  (a/deftheorem Map.scatter_groupby_entries
    [K2 :- Type, Z :- Type, S :- Type, dec2 :- (DecidableEq K2), mon :- (WAddMonoid S) :inst,
     key :- (=> Z K2), h :- (=> Z S), zs :- (List Z)]
    (forall [Mgb :- (Map K2 (List Z))]
            (forall [Mgs :- (Map K2 S)]
                    (=> (= (List (Prod K2 S)) (Map.entries K2 S Mgs)
                           (List.map (Prod K2 (List Z)) (Prod K2 S)
                                     (fn [p :- (Prod K2 (List Z))] (Prod.mk K2 S (Prod.fst K2 (List Z) p)
                                                                            (wsum (List.map Z S h (Prod.snd K2 (List Z) p))))) (Map.entries K2 (List Z) Mgb)))
                        (= (List (Prod K2 S))
                           (Map.entries K2 S
                                        (List.foldl (Map K2 S) Z
                                                    (fn [m :- (Map K2 S) z :- Z]
                                                      (Map.insert K2 S dec2 (key z)
                                                                  (WAddMonoid.add mon (h z) (Option.getD S (Map.lookup K2 S dec2 (key z) m) (WAddMonoid.zero mon))) m)) Mgs zs))
                           (List.map (Prod K2 (List Z)) (Prod K2 S)
                                     (fn [p :- (Prod K2 (List Z))] (Prod.mk K2 S (Prod.fst K2 (List Z) p)
                                                                            (wsum (List.map Z S h (Prod.snd K2 (List Z) p)))))
                                     (Map.entries K2 (List Z)
                                                  (List.foldl (Map K2 (List Z)) Z
                                                              (fn [m :- (Map K2 (List Z)) z :- Z]
                                                                (Map.insert K2 (List Z) dec2 (key z)
                                                                            (List.cons Z z (Option.getD (List Z) (Map.lookup K2 (List Z) dec2 (key z) m) (List.nil Z))) m)) Mgb zs)))))))
    (induction zs)
    (all_goals (intro Mgb Mgs hcorr))
    (all_goals (try (simp only [List.foldl_nil List.foldl_cons])))
    (all_goals (try (exact hcorr)))
    (all_goals (try (exact (ih_tail
                            (Map.insert K2 (List Z) dec2 (key head)
                                        (List.cons Z head (Option.getD (List Z) (Map.lookup K2 (List Z) dec2 (key head) Mgb) (List.nil Z))) Mgb)
                            (Map.insert K2 S dec2 (key head)
                                        (WAddMonoid.add mon (h head) (Option.getD S (Map.lookup K2 S dec2 (key head) Mgs) (WAddMonoid.zero mon))) Mgs)
                            (Map.scatter_groupby_step K2 Z S dec2 mon key h head Mgb Mgs hcorr))))))

    ;; ── INTEGRATION BRIDGES: connect LEMMA A to the actual query shape ──────────
    ;; The cross-engine GROUP-BY query elaborates to
    ;;   map (λp. reduce + 0 (map h (snd p))) (entries (group_by KEY (join …)))
    ;; (the `reduce + 0` aggregate is `List.foldl Nat.add 0`, NOT wsum). The bridges below take
    ;; the keystone (over wsum, any monoid) to that concrete Nat-foldl query and finally to a
    ;; scatter that never materializes the join product.

    ;; foldl Nat.add ↔ wsum (Nat is a commutative monoid, so foldl = foldr). Two rfl cons/nil
    ;; rules + an accumulator-general induction (closed by omega) + the e=0 corollary.
  )

(defn- gbj-bridges!
  "foldl↔wsum bridges (incl. the deforested fused aggregate) + the integration laws (query
   shape = vals of scatter, scatter∘join fusion). Split out for the same method-size reason."
  []
  (a/deftheorem Nat_wsum_cons
    [x :- Nat, xs :- (List Nat)] (= Nat (wsum (List.cons Nat x xs)) (Nat.add x (wsum xs))) (rfl))
  (a/deftheorem Nat_wsum_nil
    [] (= Nat (wsum (List.nil Nat)) Nat.zero) (rfl))
  (a/deftheorem List.foldl_Natadd_acc
    [l :- (List Nat)]
    (forall [acc :- Nat] (= Nat (List.foldl Nat Nat Nat.add acc l) (Nat.add acc (wsum l))))
    (induction l)
    (all_goals (intro acc))
    (all_goals (try (simp_all [List.foldl_nil List.foldl_cons Nat_wsum_cons Nat_wsum_nil])))
    (all_goals (try (omega))))
  (a/deftheorem List.foldl_add_eq_wsum
    [l :- (List Nat)] (= Nat (List.foldl Nat Nat Nat.add Nat.zero l) (wsum l))
    (rw (List.foldl_Natadd_acc l Nat.zero)) (omega))

    ;; FUSED aggregate bridge: the elaborator DEFORESTS `reduce + 0 ∘ map h` into a single
    ;; `foldl (λacc z. acc + h z) 0` (h inlined into the fold step). That fused form is the one the
    ;; query recognizer actually sees, so we bridge it to wsum too. The per-case residuals are pure
    ;; Nat linear arithmetic over the function-application atoms `h z` / `wsum (map h l)`, so `omega`
    ;; closes them directly (#187 fixed omega's atom abstraction — it no longer mistakes the in-scope
    ;; function binder `h : Z → Nat` for a logical implication, the bug these proofs once worked around).
  (a/deftheorem List.foldl_inlineh_acc
    [Z :- Type, h :- (=> Z Nat), l :- (List Z)]
    (forall [acc :- Nat]
            (= Nat (List.foldl Nat Z (fn [a :- Nat z :- Z] (Nat.add a (h z))) acc l)
               (Nat.add acc (wsum (List.map Z Nat h l)))))
    (induction l)
    (all_goals (intro acc))
    (all_goals (try (simp_all [List.foldl_nil List.foldl_cons Nat_wsum_cons Nat_wsum_nil List.map_cons List.map_nil])))
    (all_goals (try (omega))))
  (a/deftheorem List.foldl_inlineh_eq_wsum
    [Z :- Type, h :- (=> Z Nat), l :- (List Z)]
    (= Nat (List.foldl Nat Z (fn [a :- Nat z :- Z] (Nat.add a (h z))) Nat.zero l)
       (wsum (List.map Z Nat h l)))
    (rw (List.foldl_inlineh_acc Z h l Nat.zero)) (omega))

    ;; COROLLARY: keystone at the empty maps — entries(scatter) = map T (entries (group_by)).
    ;; (`Map.group_by key zs` is definitionally `foldl gb_step empty zs`, so the keystone's RHS
    ;; matches by def-eq; the R(empty,empty) hypothesis is `[] = map T []` = rfl.)
  (a/deftheorem Map.scatter_groupby_entries_empty
    [K2 :- Type, Z :- Type, S :- Type, dec2 :- (DecidableEq K2), mon :- (WAddMonoid S) :inst,
     key :- (=> Z K2), h :- (=> Z S), zs :- (List Z)]
    (= (List (Prod K2 S))
       (Map.entries K2 S
                    (List.foldl (Map K2 S) Z
                                (fn [m :- (Map K2 S) z :- Z]
                                  (Map.insert K2 S dec2 (key z)
                                              (WAddMonoid.add mon (h z) (Option.getD S (Map.lookup K2 S dec2 (key z) m) (WAddMonoid.zero mon))) m))
                                (Map.empty K2 S) zs))
       (List.map (Prod K2 (List Z)) (Prod K2 S)
                 (fn [p :- (Prod K2 (List Z))] (Prod.mk K2 S (Prod.fst K2 (List Z) p) (wsum (List.map Z S h (Prod.snd K2 (List Z) p)))))
                 (Map.entries K2 (List Z) (Map.group_by K2 Z dec2 key zs))))
    (exact (Map.scatter_groupby_entries K2 Z S dec2 mon key h zs (Map.empty K2 (List Z)) (Map.empty K2 S) (rfl))))

    ;; LAW-A (query shape = vals of scatter): the actual Nat `reduce + 0` per-group aggregate over
    ;; the group_by = the values of a scatter (foldByKey). Composes foldl→wsum (under the map binder)
    ;; with the COROLLARY (+ map_map to collapse the snd∘T).
  (a/deftheorem Map.groupby_reduce_eq_scatter
    [K2 :- Type, Z :- Type, dec2 :- (DecidableEq K2), key :- (=> Z K2), h :- (=> Z Nat), zs :- (List Z)]
    (= (List Nat)
       (List.map (Prod K2 (List Z)) Nat
                 (fn [p :- (Prod K2 (List Z))]
                   (List.foldl Nat Nat Nat.add Nat.zero (List.map Z Nat h (Prod.snd K2 (List Z) p))))
                 (Map.entries K2 (List Z) (Map.group_by K2 Z dec2 key zs)))
       (List.map (Prod K2 Nat) Nat (fn [p :- (Prod K2 Nat)] (Prod.snd K2 Nat p))
                 (Map.entries K2 Nat
                              (List.foldl (Map K2 Nat) Z
                                          (fn [m :- (Map K2 Nat) z :- Z]
                                            (Map.insert K2 Nat dec2 (key z)
                                                        (WAddMonoid.add (WSemiring.toWAddMonoid Nat instWSemiring_Nat) (h z)
                                                                        (Option.getD Nat (Map.lookup K2 Nat dec2 (key z) m) (WAddMonoid.zero (WSemiring.toWAddMonoid Nat instWSemiring_Nat)))) m))
                                          (Map.empty K2 Nat) zs))))
    (simp [List.foldl_add_eq_wsum])
    (rw (Map.scatter_groupby_entries_empty K2 Z Nat dec2 (WSemiring.toWAddMonoid Nat instWSemiring_Nat) key h zs))
    (simp [List.map_map Function.comp Prod.fst Prod.snd]))

    ;; LAW-A FUSED: the recognizer sees the DEFORESTED aggregate `foldl (λacc z. acc + h z) 0` (the
    ;; elaborator fuses `reduce+0 ∘ map h`), which is NOT def-eq to LAW-A's `foldl + 0 (map h ·)` —
    ;; they differ by `foldl_map` (a lemma). `Map.gbreduce_funeq` bridges the two map-functions via
    ;; `funext` + the two foldl↔wsum bridges; then LAW-A applies. This is the law the recognizer
    ;; instantiates (its LHS is def-eq to the elaborated `map (comp (foldl-inline-h) snd) (entries …)`).
  (a/deftheorem Map.gbreduce_funeq
    [K2 :- Type, Z :- Type, h :- (=> Z Nat)]
    (= (=> (Prod K2 (List Z)) Nat)
       (fn [p :- (Prod K2 (List Z))] (List.foldl Nat Z (fn [a :- Nat z :- Z] (Nat.add a (h z))) Nat.zero (Prod.snd K2 (List Z) p)))
       (fn [p :- (Prod K2 (List Z))] (List.foldl Nat Nat Nat.add Nat.zero (List.map Z Nat h (Prod.snd K2 (List Z) p)))))
    (funext p)
    (rw (List.foldl_inlineh_eq_wsum Z h (Prod.snd K2 (List Z) p)))
    (rw (List.foldl_add_eq_wsum (List.map Z Nat h (Prod.snd K2 (List Z) p)))))
  (a/deftheorem Map.groupby_reduce_eq_scatter_fused
    [K2 :- Type, Z :- Type, dec2 :- (DecidableEq K2), key :- (=> Z K2), h :- (=> Z Nat), zs :- (List Z)]
    (= (List Nat)
       (List.map (Prod K2 (List Z)) Nat
                 (fn [p :- (Prod K2 (List Z))]
                   (List.foldl Nat Z (fn [a :- Nat z :- Z] (Nat.add a (h z))) Nat.zero (Prod.snd K2 (List Z) p)))
                 (Map.entries K2 (List Z) (Map.group_by K2 Z dec2 key zs)))
       (List.map (Prod K2 Nat) Nat (fn [p :- (Prod K2 Nat)] (Prod.snd K2 Nat p))
                 (Map.entries K2 Nat
                              (List.foldl (Map K2 Nat) Z
                                          (fn [m :- (Map K2 Nat) z :- Z]
                                            (Map.insert K2 Nat dec2 (key z)
                                                        (WAddMonoid.add (WSemiring.toWAddMonoid Nat instWSemiring_Nat) (h z)
                                                                        (Option.getD Nat (Map.lookup K2 Nat dec2 (key z) m) (WAddMonoid.zero (WSemiring.toWAddMonoid Nat instWSemiring_Nat)))) m))
                                          (Map.empty K2 Nat) zs))))
    (rw (Map.gbreduce_funeq K2 Z h))
    (exact (Map.groupby_reduce_eq_scatter K2 Z dec2 key h zs)))

    ;; LAW-B (scatter ∘ join fusion): a foldl (any step) over a real `Map.join` fuses to a nested
    ;; foldl over xs that consumes each matched bucket directly — NO `Map.join` node survives (the
    ;; cost model's join materialization is gone). rw join_eq (→ flatMap) then foldl_flatMap + foldl_map.
  (a/deftheorem Map.foldl_scatter_join_fuse
    [K :- Type, X :- Type, Y :- Type, K2 :- Type, dec :- (DecidableEq K),
     step :- (=> (Map K2 Nat) (=> (Prod X Y) (Map K2 Nat))), e :- (Map K2 Nat),
     kf :- (=> X K), lf :- (=> Y K), xs :- (List X), ys :- (List Y)]
    (= (Map K2 Nat)
       (List.foldl (Map K2 Nat) (Prod X Y) step e (Map.join K X Y dec kf lf xs ys))
       (List.foldl (Map K2 Nat) X
                   (fn [acc :- (Map K2 Nat) x :- X]
                     (List.foldl (Map K2 Nat) Y
                                 (fn [acc2 :- (Map K2 Nat) y :- Y] (step acc2 (Prod.mk X Y x y)))
                                 acc
                                 (Option.getD (List Y) (Map.lookup K (List Y) dec (kf x) (Map.group_by K Y dec lf ys)) (List.nil Y))))
                   e xs))
    (rw (Map.join_eq K X Y dec kf lf xs ys))
    (simp only [List.foldl_flatMap List.foldl_map])))

(defn- gbj-capstone!
  "The recognizer-facing CAPSTONE law: the whole group-by-over-join analytics shape factorizes to a
   scatter that never materializes the join product. Composes LAW-A-fused (zs := the join) with LAW-B
   (scatter∘join fusion). The optimizer matches a query's elaborated term, instantiates THIS law with
   the extracted params, reads its RHS as the optimized term, and certifies the instance — no
   hand-built proof term needed."
  []
  (a/deftheorem Map.groupby_reduce_join_factor
    [K :- Type, X :- Type, Y :- Type, K2 :- Type, dec :- (DecidableEq K), dec2 :- (DecidableEq K2),
     kf :- (=> X K), lf :- (=> Y K), key :- (=> (Prod X Y) K2), h :- (=> (Prod X Y) Nat),
     xs :- (List X), ys :- (List Y)]
    (= (List Nat)
       (List.map (Prod K2 (List (Prod X Y))) Nat
                 (fn [p :- (Prod K2 (List (Prod X Y)))]
                   (List.foldl Nat (Prod X Y) (fn [a :- Nat z :- (Prod X Y)] (Nat.add a (h z))) Nat.zero (Prod.snd K2 (List (Prod X Y)) p)))
                 (Map.entries K2 (List (Prod X Y)) (Map.group_by K2 (Prod X Y) dec2 key (Map.join K X Y dec kf lf xs ys))))
       (List.map (Prod K2 Nat) Nat (fn [p :- (Prod K2 Nat)] (Prod.snd K2 Nat p))
                 (Map.entries K2 Nat
                              (List.foldl (Map K2 Nat) X
                                          (fn [acc :- (Map K2 Nat) x :- X]
                                            (List.foldl (Map K2 Nat) Y
                                                        (fn [acc2 :- (Map K2 Nat) y :- Y]
                                                          ((fn [m :- (Map K2 Nat) z :- (Prod X Y)]
                                                             (Map.insert K2 Nat dec2 (key z)
                                                                         (WAddMonoid.add (WSemiring.toWAddMonoid Nat instWSemiring_Nat) (h z)
                                                                                         (Option.getD Nat (Map.lookup K2 Nat dec2 (key z) m) (WAddMonoid.zero (WSemiring.toWAddMonoid Nat instWSemiring_Nat)))) m))
                                                           acc2 (Prod.mk X Y x y)))
                                                        acc
                                                        (Option.getD (List Y) (Map.lookup K (List Y) dec (kf x) (Map.group_by K Y dec lf ys)) (List.nil Y))))
                                          (Map.empty K2 Nat) xs))))
    (rw (Map.groupby_reduce_eq_scatter_fused K2 (Prod X Y) dec2 key h (Map.join K X Y dec kf lf xs ys)))
    (rw (Map.foldl_scatter_join_fuse K X Y K2 dec
                                     (fn [m :- (Map K2 Nat) z :- (Prod X Y)]
                                       (Map.insert K2 Nat dec2 (key z)
                                                   (WAddMonoid.add (WSemiring.toWAddMonoid Nat instWSemiring_Nat) (h z)
                                                                   (Option.getD Nat (Map.lookup K2 Nat dec2 (key z) m) (WAddMonoid.zero (WSemiring.toWAddMonoid Nat instWSemiring_Nat)))) m))
                                     (Map.empty K2 Nat) kf lf xs ys))))

(defn install!
  "Prove + register the group-by-over-join foundation lemmas (idempotent). Returns :installed."
  []
  (kmap/install!)
  (frame/install!)
  (bucket/install!)   ;; provides Map.join_eq (the rfl join→flatMap unfold LAW-B rewrites through)
  ;; the foldl↔wsum bridge + LAW-A are stated over Nat, so the Nat WSemiring instance must exist
  ;; (normally provided by install-laws!/faq; ensure it here so this foundation is self-sufficient).
  (algebra/install-semiring-instance! "Nat" alg/nat-row)
  (when-not (installed?) (gbj-foundation!) (gbj-bridges!) (gbj-capstone!))
  :installed)
