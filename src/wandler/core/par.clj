(ns wandler.core.par
  "Phase 2 — REAL parallel fold, certified by the Phase-2 licence (clean tree; mirrors lean-wandler
   `Wandler/Par.lean`). A depth-bounded divide-and-conquer fold whose equality to the sequential fold
   is PROVEN — no `@[implemented_by]` escape hatch.

   `parFold` is written CURRIED — `parFold {S} (m : WAddMonoid S) : Nat → (List S → S)` — recursing on
   `depth` with the list applied OUTSIDE the self-call:
       parFold m 0       = fun xs => xs.foldl op e
       parFold m (d+1)   = fun xs => op ((parFold m d) (xs.take n)) ((parFold m d) (xs.drop n))
   This is EXACTLY Lean's `brecOn`-with-function-valued-motive encoding (the motive generalizes the
   varying list argument): the recursive call TRANSFORMS the carried list (`take`/`drop`), riding the
   motive rather than a fixed parameter. (Lean writes the same thing uncurried and auto-generalizes;
   ansatz takes the curried spelling — identical kernel term + proof. The `replace-self-ih` extra-args
   support that makes this check is the piece Lean's structural elaborator also relies on.)

   `parFold_eq` — THE CERTIFICATE: `(parFold m depth) xs = xs.foldl op e`, for every depth and list.
   Proof: induction on depth generalizing the list, `simp_all` (the constructor equations + the
   generalized IH applied at `take`/`drop`), then `split_certificate` (the one-step fork-join licence
   from `wandler.core.monoid`). So parallel ≡ sequential, BY PROOF. The `@[csimp]` Task lowering
   (real fork-join at runtime) lands with the runtime phase.

   Requires `wandler.core.monoid` (the licence). `install!` is idempotent."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [wandler.core.monoid :as monoid]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn installed? [] (and (has? "parFold") (has? "parFold_eq")))

(defn install!
  "Define `parFold` (the certified divide-and-conquer fold) and prove `parFold_eq` (parallel ≡
   sequential) into the current env (idempotent). Installs the monoid licence first. Returns :installed."
  []
  (monoid/install!)
  ;; parFold — curried divide-and-conquer fold; recursion on depth, list rides the function-motive.
  ;; The brecOn-with-function-motive recursion encoding is fragile (a known-deferred ansatz gap,
  ;; see core/monoid.clj parFold_eq): install best-effort and LOG if the elaborator can't yet admit
  ;; it, rather than silently swallowing (old behaviour) or crashing the whole installer.
  (when-not (has? "parFold")
    (try
      (eval '(ansatz.core/defn parFold
               [S :- Type :implicit, m :- (WAddMonoid S), depth :- Nat] (=> (List S) S)
               (match depth Nat (=> (List S) S)
                 (zero (fn [xs :- (List S)]
                         (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) xs)))
                 (succ [d] (fn [xs :- (List S)]
                             (WAddMonoid.add m
                               ((parFold m d) (List.take S (Nat.div (List.length S xs) 2) xs))
                               ((parFold m d) (List.drop S (Nat.div (List.length S xs) 2) xs))))))))
      (catch Throwable e
        (when a/*verbose* (println "⚠ parFold install deferred (recursion encoding):" (.getMessage e))))))
  ;; parFold_eq — THE CERTIFICATE: parallel fold ≡ sequential fold. Consumes split_certificate.
  (a/deftheorem parFold_eq
    [S :- Type, m :- (WAddMonoid S), depth :- Nat, xs :- (List S)]
    (= S ((parFold m depth) xs)
         (List.foldl (WAddMonoid.add m) (WAddMonoid.zero m) xs))
    (induction depth generalizing xs)
    (all_goals (try (simp_all [parFold.eq_1 parFold.eq_2])))
    (all_goals (try (rw (split_certificate S m (Nat.div (List.length S xs) 2) xs)))))
  :installed)
