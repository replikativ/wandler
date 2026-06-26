(ns wandler.core.monoid
  "Phase 2 keystone — THE PARALLEL-FOLD LICENCE (clean tree; mirrors lean-wandler `Wandler/Monoid.lean`).

   wandler's thesis: the associativity proof IS the fork-join certificate. lean-reducers gates parallel
   reduction by API discipline (a `MonoidSpec` whose laws are a CONTRACT, never consumed); here the
   laws are CONSUMED — we PROVE that splitting a fold across a partition and combining equals the
   sequential fold, so the Task-tree fold (Par, Phase 2) is sound BY PROOF and its `@[csimp]` lowering
   is L0 at the swap.

   Two laws, both thin over the owned prelude's `WAddMonoid` (op := `WAddMonoid.add`, e := zero;
   assoc/zero_add/add_zero are its bundled axioms), each kernel `check-constant`-verified by `install!`:

     foldl_hom    ys.foldl op a = op a (ys.foldl op e)
                  — the homomorphism lemma underneath split: folding from an arbitrary accumulator `a`
                    factors as `op a (fold-from-identity)`. Induction generalizing `a`, then the
                    controlled `rw` chain through the monoid axioms (foldl_cons → ih → zero_add → assoc),
                    exactly lean-wandler's proof.
     foldl_split  (xs ++ ys).foldl op e = op (xs.foldl op e) (ys.foldl op e)
                  — THE LICENCE: folding two partitions independently and combining = the sequential
                    fold ⟹ fork-join is sound. One line: `simp [List.foldl_append, foldl_hom]`.

   This is the proof lean-reducers OMITS. Requires the algebra classes (WAddMonoid) + the Init List
   equations (full Init store). `install!` is idempotent."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.prelude.algebra :as alg]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn installed? [] (and (has? "foldl_hom") (has? "foldl_split")))

(defn install!
  "Prove + register the parallel-fold licence (`foldl_hom`, `foldl_split`) into the current env
   (idempotent). Installs the algebra classes first. Returns :installed."
  []
  (alg/install-classes!)
  ;; foldl_hom — fold-from-accumulator factors as op a (fold-from-identity). The homomorphism under split.
  (a/deftheorem foldl_hom
    [S :- Type, m :- (WAddMonoid S), a :- S, ys :- (List S)]
    (= S (List.foldl (WAddMonoid.add m) a ys)
         (WAddMonoid.add m a (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) ys)))
    (induction ys generalizing a)
    (all_goals (simp [List.foldl_nil List.foldl_cons]))
    (all_goals (try (rw (WAddMonoid.add_zero m a))))
    (all_goals (try (rw (ih_tail (WAddMonoid.add m a head)))))
    (all_goals (try (rw (ih_tail (WAddMonoid.add m (WAddMonoid.zero m) head)))))
    (all_goals (try (rw (WAddMonoid.zero_add m head))))
    (all_goals (try (rw (WAddMonoid.add_assoc m a head
                          (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) tail))))))
  ;; foldl_split — THE LICENCE: (xs ++ ys).fold = xs.fold ⊕ ys.fold. Fork-join is sound by proof.
  (a/deftheorem foldl_split
    [S :- Type, m :- (WAddMonoid S), xs :- (List S), ys :- (List S)]
    (= S
       (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m)
         (HAppend.hAppend (List S) (List S) (List S)
           (instHAppendOfAppend (List S) (List.instAppend S)) xs ys))
       (WAddMonoid.add m
         (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) xs)
         (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) ys)))
    (simp [List.foldl_append foldl_hom]))
  ;; split_certificate — THE FORK-JOIN STEP, CONSUMED. Folding the two halves at ANY split point `n`
  ;; (take n / drop n) and combining with `op` equals the sequential fold. This is `foldl_split`
  ;; CONSUMED into the soundness statement a parallel runtime actually needs: split anywhere, fold the
  ;; parts independently, combine — same answer. lean-wandler iterates this depth-many times in a
  ;; recursive `parFold` (Task fork-join) and proves `parFold_eq`; that recursive form is DEFERRED here
  ;; pending an ansatz gap — `a/defn` structural recursion rejects a recursive call that TRANSFORMS a
  ;; non-measured argument (`parFold m d (xs.take n)`), so the depth-bounded executable parFold + its
  ;; @[csimp] Task lowering land with the runtime phase. The certificate below is the algebraic content.
  (a/deftheorem split_certificate
    [S :- Type, m :- (WAddMonoid S), n :- Nat, xs :- (List S)]
    (= S
       (WAddMonoid.add m
         (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) (List.take S n xs))
         (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) (List.drop S n xs)))
       (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) xs))
    (rw <- (foldl_split S m (List.take S n xs) (List.drop S n xs)))
    (rw (List.take_append_drop S n xs)))
  :installed)
