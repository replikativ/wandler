(ns wandler.exec.dbsp-recursion
  "Verified RECURSIVE queries — the semi-naive / cycle-rule layer of DBSP (§8–9). A recursive relation
   is the least fixpoint of `F(R) = R0 ⊎ step(R)` (e.g. transitive closure: `step(R) = R ⋈ E`); the
   paper computes it via the CYCLE (feed the output back through z⁻¹) and incrementalizes the body to
   get SEMI-NAIVE evaluation — only the NEW tuples are processed each round.

   The value-level CERTIFIED essence (`Recursion.body_incr`): for a LINEAR step,
     F (R ⊎ Δ) = F R ⊎ step Δ.
   Feeding a delta to the recursive body yields the old output ⊎ `step(Δ)` — so the only NEW tuples
   come from applying `step` to the DELTA, not to all of R. That is exactly why semi-naive is sound:
   maintain the result by iterating `Δ ← step(Δ)` and accumulating, instead of recomputing `step(R)`.
   Proven from step linearity + `List.append_assoc` (exact; conditional on the step's linearity, which
   holds for the relational steps filter/map/join). The runtime `seminaive-fixpoint`/`naive-fixpoint`
   compute the least fixpoint both ways and (per body_incr) agree. The full STREAMING cycle rule over
   nested streams (DBSP cycle_incremental) is the streaming generalization — see ../dbsp-theory
   recursive.lean. Connects to ../datahike semi-naive datalog."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [wandler.exec.laws :as laws]
            [clojure.set :as set]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- appendL [A l r] (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) (listOf A) (listOf A) (listOf A)
                               (e/app* (e/const' (nm "instHAppendOfAppend") [z]) (listOf A) (e/app (e/const' (nm "List.instAppend") [z]) A)) l r))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- eqL [A x y] (e/app* (e/const' (nm "Eq") [L1]) (listOf A) x y))
(def ^:private natT (e/const' (nm "Nat") []))
(defn- nsucc [t] (e/app (e/const' (nm "Nat.succ") []) t))
(defn- naddF [a b] (e/app* (e/const' (nm "Nat.add") []) a b))
(defn- iterT [X T R0 n] (e/app* (e/const' (nm "Cycle.iter") []) X T R0 n))

(defn prove-body-incr []
  (let [X (e/fvar 1) listX (listOf (e/fvar 1))
        stepTy (e/forall' "_" listX listX :default)
        hlinTy (let [a (e/fvar 4) b (e/fvar 5) step (e/fvar 2)]
                 (-> (eqL X (e/app step (appendL X a b)) (appendL X (e/app step a) (e/app step b)))
                     (#(e/forall' "b" listX (e/abstract1 % 5) :default))
                     (#(e/forall' "a" listX (e/abstract1 % 4) :default))))
        F (fn [step R0 r] (appendL X R0 (e/app step r)))
        goal (-> (eqL X (F (e/fvar 2) (e/fvar 3) (appendL X (e/fvar 6) (e/fvar 7)))
                       (appendL X (F (e/fvar 2) (e/fvar 3) (e/fvar 6)) (e/app (e/fvar 2) (e/fvar 7))))
                 (#(e/forall' "D" listX (e/abstract1 % 7) :default))
                 (#(e/forall' "R" listX (e/abstract1 % 6) :default))
                 (#(e/forall' "hlin" hlinTy % :default))
                 (#(e/forall' "R0" listX (e/abstract1 % 3) :default))
                 (#(e/forall' "step" stepTy (e/abstract1 % 2) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "step" "R0" "hlin" "R" "D"])
        X (gf ps "X") step (gf ps "step") R0 (gf ps "R0") hlin (gf ps "hlin") R (gf ps "R") D (gf ps "D")
        listX (listOf X)
        sR (e/app step R) sD (e/app step D) sRD (e/app step (appendL X R D))
        congr (e/app* (e/const' (nm "congrArg") [L1 L1]) listX listX sRD (appendL X sR sD)
                      (e/lam "w" listX (appendL X R0 (e/bvar 0)) :default) (e/app* hlin R D))
        assoc (e/app* (e/const' (nm "List.append_assoc") [z]) X R0 sR sD)
        assocSym (e/app* (e/const' (nm "Eq.symm") [L1]) listX (appendL X (appendL X R0 sR) sD) (appendL X R0 (appendL X sR sD)) assoc)
        result (e/app* (e/const' (nm "Eq.trans") [L1]) listX
                       (appendL X R0 sRD) (appendL X R0 (appendL X sR sD)) (appendL X (appendL X R0 sR) sD)
                       congr assocSym)
        ps (basic/exact ps result)]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; Cycle.iter X T R0 n = T^n(R0) — the APPROXIMATION STREAM of the feedback cycle `fix α. T(z⁻¹ α)`
;; (the n-th Kleene iterate). DBSP models recursion as this feedback over a nested-stream time; here it
;; is the pointwise iteration. `Nat → List X` is itself a stream of relations.
(defn iter-def []
  (let [X (e/fvar 1) listX (listOf (e/fvar 1))
        body (e/app* (e/const' (nm "Nat.rec") [L1]) (e/lam "_" natT listX :default)
                     (e/fvar 3) (e/lam "k" natT (e/lam "acc" listX (e/app (e/fvar 2) (e/bvar 0)) :default) :default) (e/fvar 4))]
    (kenv/mk-def (nm "Cycle.iter") []
      (-> listX (#(e/forall' "n" natT % :default)) (#(e/forall' "R0" listX % :default))
          (#(e/forall' "T" (e/forall' "_" listX listX :default) % :default)) (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))
      (-> body (#(e/lam "n" natT (e/abstract1 % 4) :default)) (#(e/lam "R0" listX (e/abstract1 % 3) :default))
          (#(e/lam "T" (e/forall' "_" listX listX :default) (e/abstract1 % 2) :default)) (#(e/lam "X" type0 (e/abstract1 % 1) :default))))))

;; Cycle.iter_fixpoint_stable : if the cycle reaches a fixpoint (iter(n+1) = iter n), it STAYS there —
;;   iter(n+m) = iter n  for all m. The recursive query's least fixpoint is `iter n` (DBSP
;;   recursive_fixpoint_ok). Induction on m: congrArg T (ih) ∘ the fixpoint hypothesis.
(defn prove-fixpoint-stable []
  (let [X (e/fvar 1) T (e/fvar 2) R0 (e/fvar 3) n (e/fvar 4) m (e/fvar 5) listX (listOf X)
        hType (eqL X (iterT X T R0 (nsucc n)) (iterT X T R0 n))
        goal (-> (eqL X (iterT X T R0 (naddF n m)) (iterT X T R0 n))
                 (#(e/forall' "m" natT (e/abstract1 % 5) :default))
                 (#(e/forall' "h" hType % :default))
                 (#(e/forall' "n" natT (e/abstract1 % 4) :default))
                 (#(e/forall' "R0" listX (e/abstract1 % 3) :default))
                 (#(e/forall' "T" (e/forall' "_" listX listX :default) (e/abstract1 % 2) :default))
                 (#(e/forall' "X" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["X" "T" "R0" "n" "h" "m"])
        ps (basic/induction ps (fvid ps "m"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid) cg (proof/current-goal psg)
                    ihnm (some (fn [[_ d]] (when (clojure.string/starts-with? (str (:name d)) "ih") (:name d))) (:lctx cg))
                    X (gf psg "X") T (gf psg "T") R0 (gf psg "R0") nid (fvid psg "n") n (e/fvar nid) lX (listOf X)]
                (if ihnm
                  (let [h (gf psg "h") ih (e/fvar (fvid psg ihnm))
                        mp (some (fn [[id d]] (when (and (= "n" (:name d)) (not= id nid)) id)) (:lctx cg)) m' (e/fvar mp)
                        congrT (e/app* (e/const' (nm "congrArg") [L1 L1]) lX lX (iterT X T R0 (naddF n m')) (iterT X T R0 n) T ih)
                        result (e/app* (e/const' (nm "Eq.trans") [L1]) lX
                                       (iterT X T R0 (naddF n (nsucc m'))) (e/app T (iterT X T R0 n)) (iterT X T R0 n) congrT h)]
                    (basic/exact psg result))
                  (basic/exact psg (e/app* (e/const' (nm "Eq.refl") [L1]) lX (iterT X T R0 n))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defonce ^:private cache (atom nil))

(defn install!
  "Admit the recursion/cycle laws — `Recursion.body_incr` (semi-naive essence), `Cycle.iter` (the
   approximation stream) + `Cycle.iter_fixpoint_stable` (the cycle reaches and holds its fixpoint).
   Idempotent."
  []
  (laws/cached-install! cache "Cycle.iter_fixpoint_stable"
    (fn []
      (let [reg! (fn [ci] (swap! a/ansatz-env kenv/check-constant ci) ci)
            ;; build each proof ONCE — the tactic proof allocates fresh fvar/metavar state per call, so
            ;; calling it twice (once for goal, once for term) risks desyncing goal vs proof.
            [bi-g bi-p] (prove-body-incr)
            bi (reg! (kenv/mk-thm (nm "Recursion.body_incr") [] bi-g bi-p))
            it (reg! (iter-def))
            [fs-g fs-p] (prove-fixpoint-stable)
            fs (reg! (kenv/mk-thm (nm "Cycle.iter_fixpoint_stable") [] fs-g fs-p))]
        [bi it fs]))))

;; ── runtime: least-fixpoint of F(R)=R0 ∪ step(R), naive vs SEMI-NAIVE (delta-driven) ────────────
(defn naive-fixpoint
  "Least fixpoint by NAIVE iteration: R ← R0 ∪ step(R) until stable. `step` maps a coll of tuples to
   newly-derivable tuples; recomputes step over ALL of R each round."
  [step R0]
  (loop [R (set R0)]
    (let [R' (into R (step R))]
      (if (= R' R) R (recur R')))))

(defn seminaive-fixpoint
  "Least fixpoint by SEMI-NAIVE iteration: maintain R and the last delta Δ; each round derive only
   from Δ (Δ ← step(Δ) ∖ R) and fold it in. Sound by `Recursion.body_incr` (F(R⊎Δ)=F R⊎step Δ ⇒ the
   only new tuples come from step(Δ)). Processes O(Δ) per round instead of O(R)."
  [step R0]
  (loop [R (set R0), delta (set R0)]
    (let [nd (set/difference (set (step delta)) R)]
      (if (empty? nd) R (recur (into R nd) nd)))))
