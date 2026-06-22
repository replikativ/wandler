(ns wandler.clean.optimize.filter-elim
  "Step 3c — certified REFINEMENT FILTER-ELIMINATION as a Subsystem-A cascade strategy.

   Finds a bvar-free `List.filter α p xs` whose predicate `p` is provably CONSTANT-TRUE over its
   element type `α` (via the certified refine engine `prove-const` — the same one Subsystem B used),
   and rewrites it to `xs` with a kernel proof. The subterm equation `filter α p xs = xs` comes from
   `List.filter_eq_self.mpr` applied to `prove-const`'s pointwise `∀x:α, p x = true`; it is lifted to
   a whole-term proof `orig = orig[filter := xs]` by `congrArg` over a depth-aware motive (a fresh
   fvar + `abstract1`, so it works at any nesting depth). The whole proof is then re-checked by the
   strict `verified-rewrite?` gate, exactly like every other cascade strategy.

   Always-TRUE drops the filter (→ xs); always-FALSE empties it (→ [], via `List.filter_eq_nil_iff`
   and `Bool.not_eq_true`). This folds the filter-elimination capability that previously lived ONLY on
   the separate `wandler.verified` / `reducers.plan` surface into the one optimizer cascade — so an
   `a/defn` over a malli-refined element now drops its redundant (or empties its contradictory) filters
   automatically, certified, both directions."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [wandler.clean.surface.refine :as refine]
            [wandler.clean.optimize.certify :as cert])
  (:import [ansatz.kernel Env]))

(defn- C [s ls] (e/const' (name/from-string s) ls))
(defn- cname [x] (when (e/const? x) (name/->string (e/const-name x))))

(defn- replace-closed
  "Replace every occurrence of the closed subterm `s` with `r` in `t` (app/lam/forall/structural)."
  [t s r]
  (cond (.equals ^Object t s) r
        (e/app? t)    (e/app (replace-closed (e/app-fn t) s r) (replace-closed (e/app-arg t) s r))
        (e/lam? t)    (e/lam (e/lam-name t) (replace-closed (e/lam-type t) s r)
                             (replace-closed (e/lam-body t) s r) (e/lam-info t))
        (e/forall? t) (e/forall' (e/forall-name t) (replace-closed (e/forall-type t) s r)
                                 (replace-closed (e/forall-body t) s r) (e/forall-info t))
        :else t))

(defn- all-filters
  "Every bvar-free (closed) `List.filter α p xs` application subterm, preorder."
  [t]
  (let [acc (volatile! [])]
    (letfn [(go [t]
              (when (e/app? t)
                (let [[h args] (e/get-app-fn-args t)]
                  (when (and (= "List.filter" (cname h)) (= 3 (count args)) (zero? (e/bvar-range t)))
                    (vswap! acc conj t))))
              (cond (e/app? t)    (do (go (e/app-fn t)) (go (e/app-arg t)))
                    (e/lam? t)    (do (go (e/lam-type t)) (go (e/lam-body t)))
                    (e/forall? t) (do (go (e/forall-type t)) (go (e/forall-body t)))))]
      (go t))
    @acc))

(defn- filter-eq-self-eq
  "`filter α p xs = xs` from the pointwise `h : ∀x:α, p x = true` (List.filter_eq_self.mpr)."
  [u alpha p xs h]
  (let [u1 (lvl/succ u)
        listA (e/app (C "List" [u]) alpha)
        flt (e/app* (C "List.filter" [u]) alpha p xs)
        A (e/app* (C "Eq" [u1]) listA flt xs)
        inst (e/app (C "List.instMembership" [u]) alpha)
        mem (fn [a] (e/app* (C "Membership.mem" [u u]) alpha listA inst xs a))
        eqt (fn [a] (e/app* (C "Eq" [(lvl/succ lvl/zero)]) (C "Bool" []) (e/app p a) (C "Bool.true" [])))
        B (e/forall' "a" alpha (e/forall' "_m" (mem (e/bvar 0)) (eqt (e/bvar 1)) :default) :default)
        hb (e/lam "a" alpha (e/lam "_m" (mem (e/bvar 0)) (e/app h (e/bvar 1)) :default) :default)]
    (e/app* (C "Iff.mpr" []) A B (e/app* (C "List.filter_eq_self" [u]) alpha p xs) hb)))

(defn- filter-eq-nil-eq
  "`filter α p xs = []` from the pointwise `h : ∀x:α, p x = false` (List.filter_eq_nil_iff.mpr,
   with `Bool.not_eq_true` turning `p a = false` into the required `¬(p a = true)`)."
  [u alpha p xs h]
  (let [u1 (lvl/succ u)
        bl1 (lvl/succ lvl/zero)                                   ; Bool lives at Sort 1, always
        listA (e/app (C "List" [u]) alpha)
        flt (e/app* (C "List.filter" [u]) alpha p xs)
        nilA (e/app (C "List.nil" [u]) alpha)
        A (e/app* (C "Eq" [u1]) listA flt nilA)
        Bool (C "Bool" [])
        inst (e/app (C "List.instMembership" [u]) alpha)
        mem (fn [a] (e/app* (C "Membership.mem" [u u]) alpha listA inst xs a))
        pa-true (fn [a] (e/app* (C "Eq" [bl1]) Bool (e/app p a) (C "Bool.true" [])))
        pa-false (fn [a] (e/app* (C "Eq" [bl1]) Bool (e/app p a) (C "Bool.false" [])))
        notp (fn [a] (e/app (C "Not" []) (pa-true a)))
        ;; ¬(p a = true)  via  Eq.mpr (Bool.not_eq_true (p a) : ¬(p a=true) = (p a=false)) (h a)
        npf (fn [a] (e/app* (C "Eq.mpr" [lvl/zero]) (notp a) (pa-false a)
                            (e/app (C "Bool.not_eq_true" []) (e/app p a)) (e/app h a)))
        B (e/forall' "a" alpha (e/forall' "_m" (mem (e/bvar 0)) (notp (e/bvar 1)) :default) :default)
        hb (e/lam "a" alpha (e/lam "_m" (mem (e/bvar 0)) (npf (e/bvar 1)) :default) :default)]
    (e/app* (C "Iff.mpr" []) A B (e/app* (C "List.filter_eq_nil_iff" [u]) alpha p xs) hb)))

(defn- congr-whole
  "Lift subterm eq `flt = repl` (kernel proof `eq`) to a whole-term proof `orig = orig[flt:=repl]`
   via `congrArg` over the depth-aware motive `λ hole, orig[flt:=hole]`. `u` = element universe."
  [^Env env lctx orig flt repl eq u]
  (let [st (cert/mk-st env lctx)
        listA (tc/infer-type st flt)                              ; = List α
        T (tc/infer-type st orig)                                 ; orig : T
        v (let [s (#'tc/cached-whnf st (tc/infer-type st T))]     ; T : Sort v
            (if (e/sort? s) (e/sort-level s) lvl/zero))
        hfid -777001                                              ; fresh fvar id (no clash with lctx)
        M (e/lam "hole" listA (e/abstract1 (replace-closed orig flt (e/fvar hfid)) hfid) :default)]
    (e/app* (C "congrArg" [(lvl/succ u) v]) listA T flt repl M eq)))

(defn try-filter-elim
  "If `term` contains a closed `List.filter α p xs` whose `p` is provably const-true over `α`, return
   `{:term :proof :verified? true :rewrites [:filter-elim]}` rewriting that filter to `xs`; else nil.
   Sound by construction (every result is re-checked by `verified-rewrite?`)."
  [^Env env term & {:keys [lctx]}]
  (some (fn [flt]
          (try
            (let [[_ args] (e/get-app-fn-args flt)
                  alpha (nth args 0) p (nth args 1) xs (nth args 2)
                  pc (refine/prove-const env p alpha)]
              (when (and pc (boolean? (:value pc)))
                (let [u (or (first (e/const-levels (first (e/get-app-fn-args flt)))) lvl/zero)
                      always-true? (true? (:value pc))
                      repl (if always-true? xs (e/app (C "List.nil" [u]) alpha))
                      eq (if always-true?
                           (filter-eq-self-eq u alpha p xs (:proof pc))   ; filter = xs
                           (filter-eq-nil-eq  u alpha p xs (:proof pc)))  ; filter = []
                      result (replace-closed term flt repl)
                      proof (congr-whole env (or lctx {}) term flt repl eq u)
                      rw (if always-true? :filter-elim :filter-elim-empty)
                      ;; `:rw` (singular) is the cascade's composition key (faq.clj reorder branch);
                      ;; `:rewrites` is for direct callers/tests.
                      res {:term result :proof proof :rw rw :rewrites [rw]}]
                  (when (cert/verified-rewrite? env term res :lctx lctx)
                    (assoc res :verified? true)))))
            (catch Throwable _ nil)))
        (all-filters term)))


;; ── Step 4: certified DISTINCT-removal (uniqueness-licensed) ─────────────────────────────────────
(defn- all-eraseDups
  "Every bvar-free `List.eraseDups α inst xs` application subterm, preorder."
  [t]
  (let [acc (volatile! [])]
    (letfn [(go [t]
              (when (e/app? t)
                (let [[h args] (e/get-app-fn-args t)]
                  (when (and (= "List.eraseDups" (cname h)) (= 3 (count args)) (zero? (e/bvar-range t)))
                    (vswap! acc conj t))))
              (cond (e/app? t)    (do (go (e/app-fn t)) (go (e/app-arg t)))
                    (e/lam? t)    (do (go (e/lam-type t)) (go (e/lam-body t)))
                    (e/forall? t) (do (go (e/forall-type t)) (go (e/forall-body t)))))]
      (go t))
    @acc))

(defn- nodup-property
  "If `xs` is `Subtype.val.{u} (List α) P s`, return `Subtype.property.{u} (List α) P s : P (val s)`
   (= `P xs`; when `P` is `Nodup`, that is `Nodup xs`). Else nil. We do NOT verify P is literally
   Nodup here — a non-Nodup P makes the `nodup_eraseDups` citation ill-typed, so verified-rewrite?
   rejects it. The Nodup proof carried by a declared-`:set` refinement IS exactly this property."
  [xs]
  (let [[h args] (e/get-app-fn-args xs)]
    (when (and (= "Subtype.val" (cname h)) (= 3 (count args)))
      (let [u (or (first (e/const-levels h)) lvl/zero)]
        (e/app* (C "Subtype.property" [u]) (nth args 0) (nth args 1) (nth args 2))))))

(defn- synth-lawful-beq
  "Synthesize `LawfulBEq.{0} α inst` (the law's monomorphic Type-0 instance), or nil."
  [^Env env alpha inst]
  (let [goal (e/app* (C "LawfulBEq" [lvl/zero]) alpha inst)]
    (try ((requiring-resolve 'ansatz.tactic.instance/synthesize)
          env ((requiring-resolve 'ansatz.core/instance-index)) goal)
         (catch Throwable _ nil))))

(defn try-distinct-elim
  "If `term` contains a closed `List.eraseDups α inst xs` whose `xs` is a `Subtype.val` carrying a
   `Nodup` refinement (a declared-uniqueness `:set`), rewrite the dedup AWAY (→ xs) with a kernel
   proof: `nodup_eraseDups α inst (synth LawfulBEq) xs (Subtype.property …)` lifted whole-term by
   congrArg, re-checked by verified-rewrite?. The DISTINCT-removal capability — sound ONLY given the
   declared key (a stats planner can't do it). Requires `nodup_eraseDups` installed
   (wandler.clean.laws.uniqueness/install!)."
  [^Env env term & {:keys [lctx]}]
  (some (fn [ed]
          (try
            (let [[_ args] (e/get-app-fn-args ed)
                  alpha (nth args 0) inst (nth args 1) xs (nth args 2)
                  prop (nodup-property xs)
                  linst (when prop (synth-lawful-beq env alpha inst))]
              (when linst
                (let [eq (e/app* (C "nodup_eraseDups" []) alpha inst linst xs prop)
                      result (replace-closed term ed xs)
                      proof (congr-whole env (or lctx {}) term ed xs eq lvl/zero)
                      res {:term result :proof proof :rw :distinct-elim :rewrites [:distinct-elim]}]
                  (when (cert/verified-rewrite? env term res :lctx lctx)
                    (assoc res :verified? true)))))
            (catch Throwable _ nil)))
        (all-eraseDups term)))


;; ── Path 2a: certified KEYED DISTINCT-removal (relational FD, key-licensed) ──────────────────────
(defn- all-eraseDupsBy
  "Every bvar-free `List.eraseDupsBy X R xs` application subterm (3 args), preorder."
  [t]
  (let [acc (volatile! [])]
    (letfn [(go [t]
              (when (e/app? t)
                (let [[h args] (e/get-app-fn-args t)]
                  (when (and (= "List.eraseDupsBy" (cname h)) (= 3 (count args)) (zero? (e/bvar-range t)))
                    (vswap! acc conj t))))
              (cond (e/app? t)    (do (go (e/app-fn t)) (go (e/app-arg t)))
                    (e/lam? t)    (do (go (e/lam-type t)) (go (e/lam-body t)))
                    (e/forall? t) (do (go (e/forall-type t)) (go (e/forall-body t)))))]
      (go t))
    @acc))

(defn- key-comparator
  "Recognize a key-equality comparator `λ x y. BEq.beq K inst (kf x) (kf y)` (the shape `distinct-by`
   lowers to and `nodup_map_eraseDupsBy` is keyed on). Returns {:K :inst :kf} with `kf` the CLOSED
   key function, or nil. The two `kf`-applications must share one closed `kf` over the two binders."
  [R]
  (when (and (e/lam? R) (e/lam? (e/lam-body R)))
    (let [body (e/lam-body (e/lam-body R))
          [h args] (e/get-app-fn-args body)]
      (when (and (= "BEq.beq" (cname h)) (= 4 (count args)))
        (let [K (nth args 0) inst (nth args 1) ax (nth args 2) ay (nth args 3)]
          (when (and (e/app? ax) (e/app? ay)
                     (= (e/bvar 1) (e/app-arg ax)) (= (e/bvar 0) (e/app-arg ay))
                     (.equals ^Object (e/app-fn ax) (e/app-fn ay))
                     (zero? (e/bvar-range (e/app-fn ax))))
            {:K K :inst inst :kf (e/app-fn ax)}))))))

(defn try-keyed-distinct-elim
  "If `term` contains a closed `List.eraseDupsBy X (λx y. kf x == kf y) xs` whose `xs` is a
   `Subtype.val` carrying a `Nodup (map kf ·)` refinement (a declared UNIQUE KEY), rewrite the
   keyed dedup AWAY (→ xs) with a kernel proof `nodup_map_eraseDupsBy K X inst (synth LawfulBEq)
   kf xs (Subtype.property …)`, lifted whole-term by congrArg and re-checked by verified-rewrite?.
   The relational FUNCTIONAL-DEPENDENCY sibling of `try-distinct-elim`: sound ONLY given the
   declared key (a stats planner cannot). Requires `nodup_map_eraseDupsBy` installed."
  [^Env env term & {:keys [lctx]}]
  (some (fn [ed]
          (try
            (let [[_ args] (e/get-app-fn-args ed)
                  X (nth args 0) R (nth args 1) xs (nth args 2)
                  cmp (key-comparator R)
                  prop (when cmp (nodup-property xs))                ; : Nodup K (map kf xs)
                  linst (when prop (synth-lawful-beq env (:K cmp) (:inst cmp)))]
              (when linst
                (let [{:keys [K inst kf]} cmp
                      eq (e/app* (C "nodup_map_eraseDupsBy" []) K X inst linst kf xs prop)
                      result (replace-closed term ed xs)
                      proof (congr-whole env (or lctx {}) term ed xs eq lvl/zero)
                      res {:term result :proof proof
                           :rw :keyed-distinct-elim :rewrites [:keyed-distinct-elim]}]
                  (when (cert/verified-rewrite? env term res :lctx lctx)
                    (assoc res :verified? true)))))
            (catch Throwable _ nil)))
        (all-eraseDupsBy term)))


;; ── Path 2b: certified GROUP-BY ELIMINATION (relational FD, key-licensed) ─────────────────────────
(defn- groupby-self-shape
  "Recognize a denormalize-each-row-with-its-group map:
     List.map X (List X) (λr. Option.getD (Map.lookup K (List X) dec (kf r) (Map.group_by K X dec kf xs)) [])
                xs
   i.e. for each row look up its OWN group_by bucket. Returns {:K :X :dec :kf :xs} or nil. `xs` and `kf`
   must be CLOSED and the group_by must key on the same `kf`/`xs` (so `Map.groupby_self_elim` applies)."
  [t]
  (let [[h args] (e/get-app-fn-args t)]
    (when (and (= "List.map" (cname h)) (= 4 (count args)))
      (let [X (nth args 0) pred (nth args 2) xs (nth args 3)]
        (when (and (e/lam? pred) (zero? (e/bvar-range xs)))
          (let [[gh gargs] (e/get-app-fn-args (e/lam-body pred))]
            (when (and (= "Option.getD" (cname gh)) (= 3 (count gargs)))
              (let [[lh largs] (e/get-app-fn-args (nth gargs 1))]
                (when (and (= "Map.lookup" (cname lh)) (= 5 (count largs)))
                  (let [K (nth largs 0) dec (nth largs 2) keyterm (nth largs 3)
                        [gbh gbargs] (e/get-app-fn-args (nth largs 4))]
                    (when (and (e/app? keyterm)
                               (= (e/bvar 0) (e/app-arg keyterm))
                               (zero? (e/bvar-range (e/app-fn keyterm)))
                               (= "Map.group_by" (cname gbh)) (= 5 (count gbargs)))
                      (let [kf (e/app-fn keyterm)]
                        (when (and (.equals ^Object kf (nth gbargs 3))
                                   (.equals ^Object xs (nth gbargs 4)))
                          {:K K :X X :dec dec :kf kf :xs xs})))))))))))))

(defn- all-groupby-self-maps
  "Every closed group-by-self-lookup `List.map` subterm (preorder)."
  [t]
  (let [acc (volatile! [])]
    (letfn [(go [t]
              (when (and (e/app? t) (zero? (e/bvar-range t)) (groupby-self-shape t))
                (vswap! acc conj t))
              (cond (e/app? t)    (do (go (e/app-fn t)) (go (e/app-arg t)))
                    (e/lam? t)    (do (go (e/lam-type t)) (go (e/lam-body t)))
                    (e/forall? t) (do (go (e/forall-type t)) (go (e/forall-body t)))))]
      (go t))
    @acc))

(defn try-groupby-elim
  "If `term` contains a closed `map (λr. getD (lookup (kf r) (group_by kf xs)) []) xs` over a relation
   `xs` carrying a `Nodup (map kf ·)` refinement (declared UNIQUE KEY), rewrite the group-by + per-row
   lookups AWAY to `map (λr. [r]) xs` with a kernel proof `Map.groupby_self_elim … (Subtype.property …)`,
   lifted whole-term by congrArg and re-checked by verified-rewrite?. GROUP-BY ELIMINATION — sound ONLY
   given the declared key. Requires `Map.groupby_self_elim` installed (wandler.clean.laws.groupby)."
  [^Env env term & {:keys [lctx]}]
  (some (fn [mp]
          (try
            (let [{:keys [K X dec kf xs]} (groupby-self-shape mp)
                  u lvl/zero
                  prop (nodup-property xs)                       ; : Nodup K (map kf xs)
                  beq (e/app* (C "instBEqOfDecidableEq" [u]) K dec)
                  linst (when prop (synth-lawful-beq env K beq))]
              (when linst
                (let [eq (e/app* (C "Map.groupby_self_elim" []) K X dec linst kf xs prop)
                      listX (e/app (C "List" [u]) X)
                      repl (e/app* (C "List.map" [u u]) X listX
                                   (e/lam "r" X (e/app* (C "List.cons" [u]) X (e/bvar 0) (e/app (C "List.nil" [u]) X)) :default)
                                   xs)
                      result (replace-closed term mp repl)
                      proof (congr-whole env (or lctx {}) term mp repl eq u)
                      res {:term result :proof proof :rw :groupby-elim :rewrites [:groupby-elim]}]
                  (when (cert/verified-rewrite? env term res :lctx lctx)
                    (assoc res :verified? true)))))
            (catch Throwable _ nil)))
        (all-groupby-self-maps term)))
