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
                      res {:term result :proof proof
                           :rewrites [(if always-true? :filter-elim :filter-elim-empty)]}]
                  (when (cert/verified-rewrite? env term res :lctx lctx)
                    (assoc res :verified? true)))))
            (catch Throwable _ nil)))
        (all-filters term)))
