(ns wandler.clean.laws.grace
  "The grace-hash spill laws of the CLEAN wandler core — the kernel certificate behind the
   optimizer's memory-bounded join spill (`wandler.clean.optimize.faq/try-grace-hash`). Two laws:

     List.flatten_chunk       — `flatten (chunk B l) = l`: block-partitioning the build side
                                 (`List.chunk`, the runtime carrier for the spill) preserves the
                                 data. Proved THIN (the #149 nested-scrutinee `cases`/`generalize`
                                 machinery + the recursive-field fix make the case-split clean):
                                 `(induction l)(rw[chunk_cons])(generalize c …)(cases c)
                                  (simp_all …)(subst_vars)(simp_all …)`.
     Map.foldl_join_blockfold — (Stage 2) `foldl op e (join xs (flatten blocks))
                                 = foldl (λacc blk. foldl op acc (join xs blk)) e blocks` for a
                                 left-commutative `op`.

   `List.chunk` is a hand-built structural-recursion def (Init-only, no Mathlib). Support lemmas
   (`List.casesOn_nil/_cons`, `List.chunk_cons/_nil`, `List.flatten_cond`) are rfl/thin and reused
   by the `flatten_chunk` proof. `install!` admits everything STRICTLY via `env/check-constant`,
   idempotent via `has?`. Replaces the grace-hash slice of the retired `wandler.laws.proofs`."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            ;; Stage 2 (blockfold) reuses the verified hand-built Perm-cluster builders. They sit on
            ;; the clean foundation (Map.join, Map.bucket_content) — only the Perm slice + blockfold
            ;; need admitting. (To be inlined here when wandler.laws.proofs is deleted.)
            [wandler.laws.proofs :as rp]))

;; ── helpers ─────────────────────────────────────────────────────────────────
(defn- nmk [s] (nm/from-string s))
(defn- has? [s] (some? (env/lookup (a/env) (nmk s))))
(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ z))
(def ^:private type0 (e/sort' L1))
(def ^:private natT (e/const' (nmk "Nat") []))
(defn- listOf [a] (e/app* (e/const' (nmk "List") [z]) a))
(defn- nilOf [a] (e/app* (e/const' (nmk "List.nil") [z]) a))
(defn- consOf [a x xs] (e/app* (e/const' (nmk "List.cons") [z]) a x xs))
(defn- eqOf [T a b] (e/app* (e/const' (nmk "Eq") [L1]) T a b))
(defn- refl [T x] (e/app* (e/const' (nmk "Eq.refl") [L1]) T x))
(defn- admit! [ci] (swap! a/ansatz-env env/check-constant ci))

;; ── List.chunk : List(List α) — block-partition l into pieces of size ≤ B, from the right ──
;;   chunk B [] = [] ; chunk B (x::xs) = case chunk B xs of
;;     [] => [[x]] | blk::rest => if length blk < B then (x::blk)::rest else [x]::blk::rest
;; Installed NON-opaque (regular hint) so `chunk_cons` reduces by rfl. (Copied verbatim from the
;; retired wandler.laws.proofs/chunk-def-ci — kernel-`check-constant`-verified; only the hint
;; differs.)
(defn- chunk-def-ci []
  (let [chunk-type (e/forall' "a" type0 (e/forall' "B" natT
                     (e/forall' "l" (listOf (e/bvar 1)) (listOf (listOf (e/bvar 2))) :default) :default) :default)
        motive (e/lam "_" (listOf (e/bvar 2)) (listOf (listOf (e/bvar 3))) :default)
        nilC (nilOf (listOf (e/bvar 2)))
        cnd (e/app* (e/const' (nmk "Nat.blt") []) (e/app* (e/const' (nmk "List.length") [z]) (e/bvar 7) (e/bvar 1)) (e/bvar 6))
        tcase (consOf (listOf (e/bvar 7)) (consOf (e/bvar 7) (e/bvar 4) (e/bvar 1)) (e/bvar 0))
        ecase (consOf (listOf (e/bvar 7)) (consOf (e/bvar 7) (e/bvar 4) (nilOf (e/bvar 7)))
                      (consOf (listOf (e/bvar 7)) (e/bvar 1) (e/bvar 0)))
        conssub (e/lam "blk" (listOf (e/bvar 5))
                  (e/lam "rest" (listOf (listOf (e/bvar 6)))
                    (e/app* (e/const' (nmk "cond") [L1]) (listOf (listOf (e/bvar 7))) cnd tcase ecase) :default) :default)
        nilsub (consOf (listOf (e/bvar 5)) (consOf (e/bvar 5) (e/bvar 2) (nilOf (e/bvar 5))) (nilOf (listOf (e/bvar 5))))
        coMot (e/lam "_" (listOf (listOf (e/bvar 5))) (listOf (listOf (e/bvar 6))) :default)
        ihCases (e/app* (e/const' (nmk "List.casesOn") [L1 z]) (listOf (e/bvar 5)) coMot (e/bvar 0) nilsub conssub)
        consC (e/lam "x" (e/bvar 2)
                (e/lam "xs" (listOf (e/bvar 3))
                  (e/lam "ih" (listOf (listOf (e/bvar 4))) ihCases :default) :default) :default)
        body (e/app* (e/const' (nmk "List.rec") [L1 z]) (e/bvar 2) motive nilC consC (e/bvar 0))
        chunk-term (e/lam "a" type0 (e/lam "B" natT (e/lam "l" (listOf (e/bvar 1)) body :default) :default) :default)]
    (env/mk-def (nmk "List.chunk") [] chunk-type chunk-term :hints {:regular 1})))

;; ── List.casesOn_nil / casesOn_cons : iota rfl-lemmas (motive M Type-valued) ──
;; casesOn A M nil fn fc = fn  ;  casesOn A M (a::as) fn fc = fc a as
(defn- casesOn-nil-ci []
  (let [Mty (e/forall' "_" (listOf (e/bvar 0)) type0 :default)
        fnty (e/app* (e/bvar 0) (nilOf (e/bvar 1)))
        fcty (e/forall' "a" (e/bvar 2) (e/forall' "as" (listOf (e/bvar 3))
               (e/app* (e/bvar 3) (consOf (e/bvar 4) (e/bvar 1) (e/bvar 0))) :default) :default)
        co (fn [A M t fn fc] (e/app* (e/const' (nmk "List.casesOn") [L1 z]) A M t fn fc))
        concl (eqOf (e/app* (e/bvar 2) (nilOf (e/bvar 3)))
                    (co (e/bvar 3) (e/bvar 2) (nilOf (e/bvar 3)) (e/bvar 1) (e/bvar 0)) (e/bvar 1))
        ty (e/forall' "A" type0 (e/forall' "M" Mty (e/forall' "fn" fnty (e/forall' "fc" fcty concl :default) :default) :default) :default)
        pf (e/lam "A" type0 (e/lam "M" Mty (e/lam "fn" fnty (e/lam "fc" fcty
             (refl (e/app* (e/bvar 2) (nilOf (e/bvar 3))) (e/bvar 1)) :default) :default) :default) :default)]
    (env/mk-thm (nmk "List.casesOn_nil") [] ty pf)))

(defn- casesOn-cons-ci []
  (let [Mty (e/forall' "_" (listOf (e/bvar 0)) type0 :default)
        aty (e/bvar 1) asty (listOf (e/bvar 2)) fnty (e/app* (e/bvar 2) (nilOf (e/bvar 3)))
        fcty (e/forall' "x" (e/bvar 4) (e/forall' "xs" (listOf (e/bvar 5))
               (e/app* (e/bvar 5) (consOf (e/bvar 6) (e/bvar 1) (e/bvar 0))) :default) :default)
        co (fn [A M t fn fc] (e/app* (e/const' (nmk "List.casesOn") [L1 z]) A M t fn fc))
        concl (eqOf (e/app* (e/bvar 4) (consOf (e/bvar 5) (e/bvar 3) (e/bvar 2)))
                    (co (e/bvar 5) (e/bvar 4) (consOf (e/bvar 5) (e/bvar 3) (e/bvar 2)) (e/bvar 1) (e/bvar 0))
                    (e/app* (e/bvar 0) (e/bvar 3) (e/bvar 2)))
        ty (e/forall' "A" type0 (e/forall' "M" Mty (e/forall' "a" aty (e/forall' "as" asty (e/forall' "fn" fnty (e/forall' "fc" fcty concl :default) :default) :default) :default) :default) :default)
        pf (e/lam "A" type0 (e/lam "M" Mty (e/lam "a" aty (e/lam "as" asty (e/lam "fn" fnty (e/lam "fc" fcty
             (refl (e/app* (e/bvar 4) (consOf (e/bvar 5) (e/bvar 3) (e/bvar 2))) (e/app* (e/bvar 0) (e/bvar 3) (e/bvar 2))) :default) :default) :default) :default) :default) :default)]
    (env/mk-thm (nmk "List.casesOn_cons") [] ty pf)))

;; ── List.chunk_cons / chunk_nil : structural equations (def-eq, proved by Eq.refl) ──
(defn- chunk-cons-ci []
  (let [A (e/fvar 1) B (e/fvar 2) x (e/fvar 3) xs (e/fvar 4)
        LA (listOf A) LLA (listOf LA)
        chunkOf (fn [c] (e/app* (e/const' (nmk "List.chunk") []) A B c))
        lhs (chunkOf (consOf A x xs)) cval (chunkOf xs)
        coMot (e/lam "_" LLA LLA :default)
        nilsub (consOf LA (consOf A x (nilOf A)) (nilOf LA))
        cnd (e/app* (e/const' (nmk "Nat.blt") []) (e/app* (e/const' (nmk "List.length") [z]) A (e/bvar 1)) B)
        tcase (consOf LA (consOf A x (e/bvar 1)) (e/bvar 0))
        ecase (consOf LA (consOf A x (nilOf A)) (consOf LA (e/bvar 1) (e/bvar 0)))
        conssub (e/lam "blk" LA (e/lam "rest" LLA (e/app* (e/const' (nmk "cond") [L1]) LLA cnd tcase ecase) :default) :default)
        rhs (e/app* (e/const' (nmk "List.casesOn") [L1 z]) LA coMot cval nilsub conssub)
        goal (-> (eqOf LLA lhs rhs)
                 (#(e/forall' "xs" LA (e/abstract1 % 4) :default)) (#(e/forall' "x" A (e/abstract1 % 3) :default))
                 (#(e/forall' "B" natT (e/abstract1 % 2) :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        pf (-> (refl LLA lhs)
               (#(e/lam "xs" LA (e/abstract1 % 4) :default)) (#(e/lam "x" A (e/abstract1 % 3) :default))
               (#(e/lam "B" natT (e/abstract1 % 2) :default)) (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    (env/mk-thm (nmk "List.chunk_cons") [] goal pf)))

(defn- chunk-nil-ci []
  (let [A (e/fvar 1) B (e/fvar 2) LA (listOf A) LLA (listOf LA)
        lhs (e/app* (e/const' (nmk "List.chunk") []) A B (nilOf A))
        goal (-> (eqOf LLA lhs (nilOf LA))
                 (#(e/forall' "B" natT (e/abstract1 % 2) :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        pf (-> (refl LLA lhs)
               (#(e/lam "B" natT (e/abstract1 % 2) :default)) (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]
    (env/mk-thm (nmk "List.chunk_nil") [] goal pf)))

(defn- thm! [s builder]
  (when-not (has? s)
    (let [[g p] (builder)]
      (when (and g p) (admit! (env/mk-thm (nmk s) [] g p))))))

(defn- install-blockfold!
  "Stage 2 — the block-partition spill algebra `Map.foldl_join_blockfold` and its Perm-cluster
   dependencies, on top of the clean foundation (Map.join, Map.bucket_content). Each builder is
   the verified hand-built proof (kernel `check-constant` strict). NO Fubini reformulation yet —
   this is the drop-in port that retires the OLD relational.clj as the grace-hash provider."
  []
  ;; Map.join's defining equation (`Map.join.eq_unfold`) — the filter-form Perm proofs simp with it.
  ;; Clean foundation provides Map.join but not its unfold lemma; admit it here (as old relational did).
  (when-not (has? "Map.join.eq_unfold")
    (try (admit! ((requiring-resolve 'wandler.clean.optimize/unfold-eqn-ci) (a/env) "Map.join"))
         (catch Throwable _ nil)))
  ;; §2 List.Perm helpers
  (thm! "List.flatMap_const_nil"           rp/prove-flatMap-const-nil)
  (thm! "List.flatMap_congr_perm"          rp/prove-flatMap-congr-perm)
  (thm! "List.flatMap_append_distrib_perm" rp/prove-flatMap-append-distrib)
  (thm! "List.flatMap_cons_distrib_perm"   rp/prove-flatMap-cons-distrib)
  (thm! "List.flatMap_map_comm"            rp/prove-flatMap-map-comm)
  (thm! "List.foldl_cons_perm"             rp/prove-foldflip-perm)
  ;; §5 grace-hash: build-side distributes over append (filter form) → process in blocks; a
  ;; left-commutative aggregate is invariant under the block partition's permutation.
  (thm! "Map.join_filter_append_perm"      rp/prove-join-filter-append-perm)
  (thm! "List.foldl_perm_lcomm"            rp/prove-foldl-perm-lcomm)
  (thm! "Map.join_filter_form_perm"        rp/prove-join-filter-form-perm)
  (thm! "Map.join_append_perm"             rp/prove-join-append-perm)
  (thm! "Map.join_nil_right"               rp/prove-join-nil-right)
  (thm! "Map.join_blockfold_perm"          rp/prove-join-blockfold-perm)
  (thm! "Map.foldl_join_blockfold"         rp/prove-foldl-join-blockfold))

(defn install!
  "Install the grace-hash spill laws (idempotent). Returns :installed.
   Stage 1: List.chunk + support lemmas + the THIN List.flatten_chunk.
   Stage 2: Map.foldl_join_blockfold + its Perm-cluster deps (on the clean foundation)."
  []
  (when-not (has? "List.chunk") (admit! (chunk-def-ci)))
  (when-not (has? "List.casesOn_nil") (admit! (casesOn-nil-ci)))
  (when-not (has? "List.casesOn_cons") (admit! (casesOn-cons-ci)))
  (when-not (has? "List.chunk_cons") (admit! (chunk-cons-ci)))
  (when-not (has? "List.chunk_nil") (admit! (chunk-nil-ci)))
  ;; List.flatten_cond : flatten (bif b X Y) = bif b (flatten X) (flatten Y) — by `cases b`.
  (when-not (has? "List.flatten_cond")
    (try
      (eval '(ansatz.core/theorem List.flatten_cond
               [A :- Type, b :- Bool, X :- (List (List A)), Y :- (List (List A))]
               (= (List A) (List.flatten A (bif b X Y)) (bif b (List.flatten A X) (List.flatten A Y)))
               (cases b) (all_goals (rfl))))
      (catch Throwable _ nil)))
  ;; List.flatten_chunk : flatten (chunk B l) = l — THE grace-hash certificate. THIN: structural
  ;; induction, then case-split the chunk recursion (the #149 nested-scrutinee machinery).
  (when-not (has? "List.flatten_chunk")
    (try
      (eval '(ansatz.core/theorem List.flatten_chunk [A :- Type, B :- Nat, l :- (List A)]
               (= (List A) (List.flatten A (List.chunk A B l)) l)
               (induction l)
               (all_goals (try (rw [List.chunk_cons])))
               (all_goals (try (generalize c hc (List.chunk A B tail))))
               (all_goals (try (intro c))) (all_goals (try (intro hc)))
               (all_goals (try (cases c)))
               (all_goals (try (simp_all [List.casesOn_nil List.casesOn_cons List.flatten_cond Bool.cond_self
                                          List.chunk_nil List.flatten_nil List.flatten_cons List.cons_append List.nil_append])))
               (all_goals (try (subst_vars)))
               (all_goals (try (simp_all [List.casesOn_nil List.casesOn_cons List.flatten_cond Bool.cond_self
                                          List.chunk_nil List.flatten_nil List.flatten_cons List.cons_append List.nil_append])))))
      (catch Throwable _ nil)))
  (install-blockfold!)
  :installed)
