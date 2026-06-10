(ns ansatz.stream
  "Verified WINDOWED stream processing — the coalgebraic on-ramp to lazy/infinite sources.

   A stream over `A` is a COALGEBRA `(seed : S, step : S → Option (A × S))` — exactly the shape of a
   Clojure lazy seq (`step` = uncons) or a partial-cps `GeneratorSeq` (`anext`). The kernel models a
   BOUNDED WINDOW of it as `Stream.unfoldTake A S step n s : List A` (pull ≤ n elements, stop on
   `none`) — an honest finite observation, defined by `Nat.rec` (no coinduction needed). A window is a
   `List`, so the ENTIRE verified List/relational optimizer applies to it; the only new content is the
   BOUNDARY law that connects stream ops to List ops:

     Stream.take_smap :  unfoldTake (smapStep f step) n s = List.map f (unfoldTake step n s)

   i.e. mapping a stream then windowing = windowing then `List.map`. This lets the existing fusion/
   relational machinery absorb a stream-side map across the window boundary. At runtime `unfoldTake`
   (codegen `ansatz.core/unfold-take`) forces only the window — so it runs over an INFINITE lazy seq.
   See docs/SPILL_AND_FAQ_PLAN.md, [[architecture-and-lift-plan]]; this is the first rung of the
   List → Stream → Incremental → Distributed ladder (the same fusion algebra, observed finitely)."
  (:require [ansatz.core :as a]
            [ansatz.fork :as fork]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- consOf [a x l] (e/app* (e/const' (nm "List.cons") [z]) a x l))
(defn- prodT [X Y] (e/app* (e/const' (nm "Prod") [z z]) X Y))
(defn- fstOf [X Y p] (e/app* (e/const' (nm "Prod.fst") [z z]) X Y p))
(defn- sndOf [X Y p] (e/app* (e/const' (nm "Prod.snd") [z z]) X Y p))
(defn- mkP [X Y x y] (e/app* (e/const' (nm "Prod.mk") [z z]) X Y x y))
(defn- optionOf [A] (e/app (e/const' (nm "Option") [z]) A))
(defn- natT [] (e/const' (nm "Nat") []))
(defn- mapL [A B f l] (e/app* (e/const' (nm "List.map") [z z]) A B f l))
(defn- optMap [A B f o] (e/app* (e/const' (nm "Option.map") [z z]) A B f o))
(defn- ut [A S step n s] (e/app* (e/const' (nm "Stream.unfoldTake") []) A S step n s))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- gf [ps n] (e/fvar (fvid ps n)))
(defn- focus [ps gid] (assoc ps :goals [gid]))

;; Stream.unfoldTake A S step n s : List A
;;   = Nat.rec (λ_. S→List A) (λs.[]) (λk ih s. casesOn (step s) [] (λp. fst p :: ih (snd p))) n s
(defn unfold-take-def
  "The ConstantInfo defining `Stream.unfoldTake` (windowed observation of a coalgebra)."
  []
  (let [A (e/fvar 1) S (e/fvar 2) step (e/fvar 3) AS (prodT A S)
        motive (e/lam "_" (natT) (e/forall' "_" S (listOf A) :default) :default)
        base   (e/lam "s" S (nilOf A) :default)
        someC  (e/lam "p" AS (consOf A (fstOf A S (e/bvar 0)) (e/app (e/bvar 2) (sndOf A S (e/bvar 0)))) :default)
        stepC  (e/lam "k" (natT)
                 (e/lam "ih" (e/forall' "_" S (listOf A) :default)
                   (e/lam "s" S
                     (e/app* (e/const' (nm "Option.casesOn") [L1 z]) AS
                             (e/lam "_" (optionOf AS) (listOf A) :default)
                             (e/app step (e/bvar 0)) (nilOf A) someC) :default) :default) :default)
        body (e/app (e/app* (e/const' (nm "Nat.rec") [L1]) motive base stepC (e/fvar 4)) (e/fvar 5))
        val (-> body
                (#(e/lam "s" S (e/abstract1 % 5) :default))
                (#(e/lam "n" (natT) (e/abstract1 % 4) :default))
                (#(e/lam "step" (e/forall' "_" S (optionOf AS) :default) (e/abstract1 % 3) :default))
                (#(e/lam "S" type0 (e/abstract1 % 2) :default))
                (#(e/lam "A" type0 (e/abstract1 % 1) :default)))
        ty (-> (listOf (e/fvar 1))
               (#(e/forall' "s" (e/fvar 2) % :default))
               (#(e/forall' "n" (natT) % :default))
               (#(e/forall' "step" (e/forall' "_" (e/fvar 2) (optionOf (prodT (e/fvar 1) (e/fvar 2))) :default) % :default))
               (#(e/forall' "S" type0 (e/abstract1 % 2) :default))
               (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))]
    (kenv/mk-def (nm "Stream.unfoldTake") [] ty val)))

(defn- pairf-lam [A B S f]                    ; λp:(A×S). (f (fst p), snd p)
  (e/lam "p" (prodT A S) (mkP B S (e/app f (fstOf A S (e/bvar 0))) (sndOf A S (e/bvar 0))) :default))
(defn smap-step [A B S f step]                 ; the stream-map'd step : S → Option(B×S)
  (e/lam "s" S (optMap (prodT A S) (prodT B S) (pairf-lam A B S f) (e/app step (e/bvar 0))) :default))

;; Stream.take_smap : unfoldTake (smapStep f step) n s = List.map f (unfoldTake step n s).
;; Induction on n (s generalized); zero = rfl ([] = map f []); succ = Option.casesOn on (step s):
;; none → rfl, some p → congrArg (f (fst p) :: ·) (ih (snd p)).  (Option.map f none/some reduces.)
(defn prove-take-smap []
  (let [A (e/fvar 1) B (e/fvar 2) S (e/fvar 3) f (e/fvar 4) step (e/fvar 5) n (e/fvar 6) s (e/fvar 7)
        stepTy (e/forall' "_" S (optionOf (prodT A S)) :default)
        concl (e/app* (e/const' (nm "Eq") [L1]) (listOf B)
                      (ut B S (smap-step A B S f step) n s)
                      (mapL A B f (ut A S step n s)))
        goal (-> concl
                 (#(e/forall' "s" S (e/abstract1 % 7) :default))
                 (#(e/forall' "n" (natT) (e/abstract1 % 6) :default))
                 (#(e/forall' "step" stepTy (e/abstract1 % 5) :default))
                 (#(e/forall' "f" (e/forall' "_" A B :default) (e/abstract1 % 4) :default))
                 (#(e/forall' "S" type0 (e/abstract1 % 3) :default))
                 (#(e/forall' "B" type0 (e/abstract1 % 2) :default))
                 (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["A" "B" "S" "f" "step" "n"])
        ps (basic/induction ps (fvid ps "n"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cg (proof/current-goal psg)
                    ihnm (some (fn [[_ d]] (when (clojure.string/starts-with? (str (:name d)) "ih") (:name d))) (:lctx cg))]
                (if ihnm
                  (let [psg (basic/intros psg ["s"])
                        A (gf psg "A") B (gf psg "B") S (gf psg "S") f (gf psg "f") step (gf psg "step")
                        s (gf psg "s") ih (gf psg ihnm)
                        kpred (some (fn [[id d]] (when (and (not= (:name d) ihnm)
                                                            (= "Nat" (e/->string (:type d)))) id)) (:lctx cg))
                        sm (smap-step A B S f step) AS (prodT A S) BS (prodT B S) pf (pairf-lam A B S f)
                        someC-B (e/lam "p" BS (consOf B (fstOf B S (e/bvar 0)) (ut B S sm (e/fvar kpred) (sndOf B S (e/bvar 0)))) :default)
                        someC-A (e/lam "p" AS (consOf A (fstOf A S (e/bvar 0)) (ut A S step (e/fvar kpred) (sndOf A S (e/bvar 0)))) :default)
                        lhs-with (fn [o] (e/app* (e/const' (nm "Option.casesOn") [L1 z]) BS
                                          (e/lam "_" (optionOf BS) (listOf B) :default)
                                          (optMap AS BS pf o) (nilOf B) someC-B))
                        rhs-with (fn [o] (e/app* (e/const' (nm "Option.casesOn") [L1 z]) AS
                                          (e/lam "_" (optionOf AS) (listOf A) :default)
                                          o (nilOf A) someC-A))
                        mu (e/lam "o" (optionOf AS)
                             (e/app* (e/const' (nm "Eq") [L1]) (listOf B)
                                     (lhs-with (e/bvar 0)) (mapL A B f (rhs-with (e/bvar 0)))) :default)
                        noneCase (e/app* (e/const' (nm "Eq.refl") [L1]) (listOf B) (nilOf B))
                        someCase (e/lam "p" AS
                                   (e/app* (e/const' (nm "congrArg") [L1 L1]) (listOf B) (listOf B)
                                           (ut B S sm (e/fvar kpred) (sndOf A S (e/bvar 0)))
                                           (mapL A B f (ut A S step (e/fvar kpred) (sndOf A S (e/bvar 0))))
                                           (e/lam "l" (listOf B) (consOf B (e/app f (fstOf A S (e/bvar 1))) (e/bvar 0)) :default)
                                           (e/app ih (sndOf A S (e/bvar 0)))) :default)
                        casesT (e/app* (e/const' (nm "Option.casesOn") [z z]) AS mu (e/app step s) noneCase someCase)]
                    (basic/exact psg casesT))
                  (let [psg (basic/intros psg ["s"]) B (gf psg "B")]
                    (basic/exact psg (e/app* (e/const' (nm "Eq.refl") [L1]) (listOf B) (nilOf B)))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(defonce ^:private cache (atom nil))

(defn install!
  "Admit `Stream.unfoldTake` (def) + `Stream.take_smap` (law) into the global env (idempotent).
   After this, windowed stream pipelines `sum (window n (smap f source))` certify via take_smap and
   run over infinite/lazy sources. First call proves; later calls replay the memoized CIs."
  []
  (when-not (kenv/lookup (a/env) (nm "Stream.unfoldTake"))
    (swap! a/ansatz-env kenv/check-constant (unfold-take-def)))
  (when-not (kenv/lookup (a/env) (nm "Stream.take_smap"))
    (if-let [c @cache]
      (swap! a/ansatz-env kenv/check-constant c)
      (let [[g p] (prove-take-smap)
            ci (kenv/mk-thm (nm "Stream.take_smap") [] g p)]
        (swap! a/ansatz-env kenv/check-constant ci)
        (reset! cache ci))))
  (a/env))

;; ── rung 2: sample-based verified JIT over a live stream + a fork substrate ──────
(defn jit-window
  "ONE step of the verified streaming JIT. Pull a window of `n` element VALUES from the live coalgebra
   `(step, seed-in-cell)` — sampled on a FORK of `cell`, so the live system is never disturbed (for a
   pure value-seed this is free; for a stateful spindel system it's an O(1) CoW fork) — then MEASURE
   the pipeline's filter selectivities on that window and certified-REPLAN via `optimize-measured`,
   finally run the adapted plan on the window. `pipeline-term` is a kernel pipeline over the free
   window variable `win-id` (its `:type` read from `lctx`). Returns
     {:result :verified? :profile :rewrites :plan :window}.
   Soundness: EVERY window's plan is kernel-certified ≡ the naive pipeline (verified-rewrite?), so the
   JIT may adopt a DIFFERENT certified plan as the stream's distribution drifts — results never change,
   only the plan. This is the adaptive/JIT story over a live stream; the same fork-and-commit shape
   serves the inference agenda (SMC resample / MCMC propose)."
  [env pipeline-term win-id lctx cell step n]
  (let [win-type (get-in lctx [win-id :type])
        window   (fork/speculate cell (fn [fk] (a/unfold-take step n (fork/current fk))))
        om       (a/optimize-measured env pipeline-term window :lctx lctx)
        plan-fn  (eval (a/ansatz->clj env (e/lam "win" win-type (e/abstract1 (:term om) win-id) :default) []))]
    {:result    (plan-fn window)
     :verified? (:verified? om)
     :profile   (:profile om)
     :rewrites  (:rewrites om)
     :plan      (:term om)
     :window    window}))
