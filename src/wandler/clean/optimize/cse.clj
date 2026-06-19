(ns wandler.clean.optimize.cse
  "SHARED-SUBTREE PLANNING (common-subexpression elimination) for the certified optimizer.

   A dataflow TREE (e.g. two aggregations over the same `(filter p xs)`) recomputes the shared
   subexpression once per occurrence. CSE hoists it into a `let` so it runs ONCE:
       (f S S)   ⟶   (let s := S in f s s)
   The soundness is FREE: `let` is ZETA-reducible, so `(f S S)` and `(let s := S in f s s)` are
   DEFINITIONALLY equal — the certificate is `Eq.refl` (no law, no e-matching, no search). The
   kernel gate (`cert/verified-rewrite?`) accepts it because the two sides are defeq; ansatz.codegen
   already lowers `:let` to a Clojure `let`, so the runtime sharing is real.

   SCOPE: we only hoist subterms that are CLOSED under the enclosing binders (no loose de Bruijn
   index). A closed subterm looks structurally identical at every occurrence (its indices don't
   depend on local depth), so it can be lifted above all binders and matched by canonical string.
   A subterm that references a local lambda's parameter is left in place (can't escape the binder)."
  (:require [wandler.clean.optimize.certify :as cert]
            [wandler.clean.optimize.cost :as cost]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.level :as lvl])
  (:import [ansatz.kernel Env]))

(def ^:private barrier-heads
  "Subterms worth SHARING are BARRIERS — non-streaming ops fusion CANNOT inline away, expensive
   enough that recomputing per consumer hurts: joins, group-by, sort, dedup, and the materialized
   relational maps. Streaming map/filter/foldl are deliberately EXCLUDED — fusion deforests those, so
   sharing a `(filter p xs)` is worse than fusing it into each consumer (and simp's zeta would inline
   the let anyway). CSE complements fusion at exactly the points fusion stops."
  #{"Map.join" "Map.group_by" "List.mergeSort" "List.eraseDups" "Map.lookup" "Map.insert"})

(defn- barrier-bearing?
  "Worth hoisting only if the subterm computes a shareable BARRIER (see `barrier-heads`)."
  [e]
  (some #(cost/mentions-const? e %) barrier-heads))

(defn- closed?
  "True if `e` has no LOOSE de Bruijn index — every bvar is bound within `e`. Such a subterm is
   identical at every occurrence and can be lifted above all enclosing binders."
  [e]
  (letfn [(go [e d]
            (cond
              (e/bvar? e)   (< (e/bvar-idx e) d)
              (e/app? e)    (and (go (e/app-fn e) d) (go (e/app-arg e) d))
              (e/lam? e)    (and (go (e/lam-type e) d) (go (e/lam-body e) (inc d)))
              (e/forall? e) (and (go (e/forall-type e) d) (go (e/forall-body e) (inc d)))
              (e/let? e)    (and (go (e/let-type e) d) (go (e/let-value e) d) (go (e/let-body e) (inc d)))
              (e/proj? e)   (go (e/proj-struct e) d)
              (e/mdata? e)  (go (e/mdata-expr e) d)
              :else true))]
    (go e 0)))

(defn- count-subterms
  "Map canonical-string → {:expr e :count n} over CLOSED, SOAC-bearing subterms of `term`."
  [term]
  (let [acc (atom {})]
    (letfn [(visit [e]
              (when (and (e/app? e) (closed? e) (barrier-bearing? e))
                (let [k (e/->string e)]
                  (swap! acc update k (fn [v] (if v (update v :count inc) {:expr e :count 1})))))
              (cond
                (e/app? e)    (do (visit (e/app-fn e)) (visit (e/app-arg e)))
                (e/lam? e)    (do (visit (e/lam-type e)) (visit (e/lam-body e)))
                (e/forall? e) (do (visit (e/forall-type e)) (visit (e/forall-body e)))
                (e/let? e)    (do (visit (e/let-type e)) (visit (e/let-value e)) (visit (e/let-body e)))
                (e/proj? e)   (visit (e/proj-struct e))
                (e/mdata? e)  (visit (e/mdata-expr e))
                :else nil))]
      (visit term))
    @acc))

(defn- ranked-shares
  "Shared subterms (occur ≥2×, not the whole term), largest-first — the most work hoisted wins. Each
   is a candidate Expr; `try-cse` further requires a VALUE (non-function) type so we never hoist an
   under-applied SOAC prefix (e.g. `List.foldl Nat Nat`) into a let, which would codegen malformed."
  [term]
  (->> (count-subterms term)
       (filter (fn [[k v]] (and (>= (:count v) 2) (not= k (e/->string term)))))
       (sort-by (fn [[k _]] (- (count k))))
       (map (fn [[_ v]] (:expr v)))))

(defn- value-typed?
  "True if `s` has a concrete VALUE type (a List/Map/Nat/…), not a function type. A function-typed
   subterm is a partial application — hoisting it produces an under-applied head codegen can't lower."
  [st s]
  (try (let [T (#'tc/cached-whnf st (tc/infer-type st s))] (not (e/forall? T)))
       (catch Throwable _ false)))

(defn- abstract-subterm
  "Replace every occurrence of subterm `s` (by canonical string `sk`) in `term` with a bvar pointing
   at a `let` binder placed at the TOP. At an occurrence under `d` local binders the let-bound var is
   `bvar d`. `s` is closed, so it matches identically regardless of depth."
  [term s sk]
  (letfn [(go [e d]
            (if (and (e/app? e) (= (e/->string e) sk))
              (e/bvar d)
              (cond
                (e/app? e)    (e/app (go (e/app-fn e) d) (go (e/app-arg e) d))
                (e/lam? e)    (e/lam (e/lam-name e) (go (e/lam-type e) d) (go (e/lam-body e) (inc d)) (e/lam-info e))
                (e/forall? e) (e/forall' (e/forall-name e) (go (e/forall-type e) d) (go (e/forall-body e) (inc d)) (e/forall-info e))
                (e/let? e)    (e/let' (e/let-name e) (go (e/let-type e) d) (go (e/let-value e) d) (go (e/let-body e) (inc d)))
                :else e)))]
    (go term 0)))

(defn- carrier-u [st T]
  (let [s (#'tc/cached-whnf st (tc/infer-type st T))]
    (if (e/sort? s) (e/sort-level s) lvl/zero)))

(defn try-cse
  "Hoist the most valuable shared, closed, SOAC-bearing subterm of `term` into a `let`. Certificate
   is `Eq.refl` (zeta defeq). Returns {:term :proof :verified? :changed? :rw} or nil. Re-runnable to a
   fixpoint by the caller (each call hoists one share). Adopts only if the kernel certifies it (always
   should — it's rfl) AND it does not raise the cardinality cost."
  [^Env env term & {:keys [lctx selectivity sizes]}]
  (let [st (cert/mk-st env lctx)]
    (some
     (fn [s]
       (when (value-typed? st s)
         (let [Ts (try (tc/infer-type st s) (catch Throwable _ nil))
               Tt (try (tc/infer-type st term) (catch Throwable _ nil))]
           (when (and Ts Tt)
             (let [u      (carrier-u st Tt)
                   body'  (abstract-subterm term s (e/->string s))
                   result (e/let' "cse" Ts s body')
                   proof  (e/app* (e/const' (name/from-string "Eq.refl") [u]) Tt term)
                   res    {:term result :proof proof :changed? true :rw :cse}]
               ;; COST gate (now meaningful — the model is tree/let-aware, so the `let` pays the
               ;; shared subterm ONCE while the dup form pays it per occurrence): adopt iff the
               ;; shared plan is not more expensive. Soundness is the rfl certificate (verified-rewrite?).
               (when (and (<= (cost/pipeline-cost result {:selectivity selectivity :sizes sizes})
                              (cost/pipeline-cost term {:selectivity selectivity :sizes sizes}))
                          (cert/verified-rewrite? env term res :lctx lctx))
                 (assoc res :verified? true)))))))
     (ranked-shares term))))
