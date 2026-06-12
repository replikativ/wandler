(ns wandler.bridge.datahike
  "OPTIONAL datahike adapter for ansatz.bridge. PURE DATA transformation — it maps datahike's
   logical query IR (the LScan/LFilter/LEntityJoin subset of datahike.query.ir) to/from Ansatz
   KERNEL TERMS, so it has NO hard datahike dependency (datahike is only needed at RUNTIME to execute
   the γ-lowered plan; :detect? probes for it). Registering is a side-effect of loading this ns —
   wandler.bridge/load-optional-engines! requires it inside a try, so a classpath without this ns (or
   without datahike) simply skips it.

   THE α SPEC (the trusted boundary axioms, written as the :lift mapping):
     LScan [?e :attr ?v]          ↦ a relation SOURCE  (List Row) — opaque to the kernel, datahike's
                                     contract: it yields the datoms for :attr. Schema lives in the
                                     ROW TYPE so a pushdown only type-checks against present attrs.
     LFilter p (q)                ↦ List.filter p (⟦q⟧)
     LEntityJoin on (l) (r)       ↦ Map.join kf lf ⟦l⟧ ⟦r⟧           (the equi-join on a shared var)
   Boundary pushdown — push a Clojure filter INTO datahike so its index does the work — is the law
     q(where φ∧ψ) db = filter (sat ψ) (q(where φ) db)
   admitted as a datahike API AXIOM (a small trusted base beyond the kernel; property-test it against
   real datahike via the malli bridge). NOT yet wired here — this first cut does the STRUCTURAL
   optimization (filter→join pushdown, semijoin, count/sum factorization) over datahike-shaped terms
   using the already-proven relational laws, with scans as opaque sources.

   THE CORRELATED-SUBQUERY case (a transducer whose fn invokes datahike's q) DECORRELATES at α:
     mapcat (λrow. q[where attr = (sel row)] db) rows   (N per-row datahike queries)
       ↦  Map.join sel scan-attr rows (scan db attr)    (ONE join — the verified planner then does
                                                          join-order DP + aggregation-through-join,
                                                          with datahike's :estimate as the oracle for
                                                          its side's cardinality / index availability)
   See `decorrelate` + the worked example in the test / [[architecture-and-lift-plan]]."
  (:require [ansatz.core :as a]
            [wandler.bridge :as bridge]
            [wandler.plan :as plan]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(def ^:private L1 (lvl/succ z))
(def ^:private type0 (e/sort' L1))
(def ^:private boolT (e/const' (name/from-string "Bool") []))
(def ^:private natT (e/const' (name/from-string "Nat") []))
(defn- nm [s] (name/from-string s))

;; ══ THE DATAHIKE BOUNDARY SPEC — q TYPED DEPENDENTLY ON THE :find CLAUSE ══════════════════════════
;; datahike's q is heavily polymorphic in its RETURN shape, set by the :find spec (datalog-parser's
;; FindScalar/FindColl/FindTuple/FindRel): `:find ?a .` → a SCALAR, `:find [?a ...]` → a COLLECTION,
;; `:find [?a ?b]` → a TUPLE, `:find ?a ?b` → a RELATION. So a single `q : DB → … → List Row` axiom
;; is FALSE. Instead we model the :find spec as a kernel VALUE (Datahike.FindSpec) and COMPUTE q's
;; return type from it with a TYPE-LEVEL function Datahike.Result : FindSpec → Type. Then
;;     Datahike.q : DB → (f : FindSpec) → Result f
;; is precise: q db (fscalar tint) : Nat, q db (fcoll tint) : List Nat, q db (frel tint tbool) :
;; List (Nat × Bool), q db (ftuple tint tbool) : Nat × Bool. Schema value-types are a closed universe
;; of CODES (Datahike.TyCode) + Decode : TyCode → Type — so FindSpec stays a SMALL inductive and the
;; type computation is a large elimination (always sound for a Type-0 inductive). Admitted as
;; axioms/defs (the TCB beyond the kernel — datahike's API contract), OPT-IN; property-test vs real
;; datahike via the malli bridge. (The filter→q pushdown over the List-returning shapes is a separate
;; law, a follow-up.)
(def ^:private L2 (lvl/succ L1))
(defn- c' [s & ls] (e/const' (nm s) (vec ls)))
(defn- listOf [a] (e/app (c' "List" z) a))
(defn- prodOf [a b] (e/app* (c' "Prod" z z) a b))

(defn- build-decode []
  ;; Datahike.Decode : TyCode → Type  — tint↦Nat, tbool↦Bool (extend per the datahike schema types)
  (e/app* (c' "Datahike.TyCode.rec" L2) (e/lam "c" (c' "Datahike.TyCode") type0 :default) natT boolT))

(defn- build-result [Decode]
  ;; Datahike.Result : FindSpec → Type  — the per-find-spec return type, via a large elimination.
  (let [TyC (c' "Datahike.TyCode") FS (c' "Datahike.FindSpec") dec (fn [t] (e/app Decode t))]
    (e/app* (c' "Datahike.FindSpec.rec" L2) (e/lam "f" FS type0 :default)
            (e/lam "c" TyC (dec (e/bvar 0)) :default)                                                ; fscalar c → Decode c
            (e/lam "c" TyC (listOf (dec (e/bvar 0))) :default)                                       ; fcoll c → List(Decode c)
            (e/lam "a" TyC (e/lam "b" TyC (listOf (prodOf (dec (e/bvar 1)) (dec (e/bvar 0)))) :default) :default) ; frel a b → List(A×B)
            (e/lam "a" TyC (e/lam "b" TyC (prodOf (dec (e/bvar 1)) (dec (e/bvar 0))) :default) :default))))      ; ftuple a b → A×B

(defn install-axioms!
  "OPT-IN: admit the datahike boundary spec — q typed DEPENDENTLY on the :find clause (see above).
   EXPANDS THE TRUSTED BASE beyond the kernel (datahike's API contract) — a deliberate trust
   decision, NOT on load. q itself is polymorphic; its return type is COMPUTED from a FindSpec value
   via Result. Idempotent."
  []
  (when-not (kenv/lookup (a/env) (nm "Datahike.q"))
    (binding [a/*verbose* false]
      ;; the :find-spec value universe — small inductives carrying schema-type CODES
      (eval '(ansatz.core/inductive Datahike.TyCode [] (tint) (tbool)))
      (eval '(ansatz.core/inductive Datahike.FindSpec []
               (fscalar [c Datahike.TyCode]) (fcoll [c Datahike.TyCode])
               (frel [a Datahike.TyCode] [b Datahike.TyCode]) (ftuple [a Datahike.TyCode] [b Datahike.TyCode]))))
    (let [Decode (build-decode) Result (build-result Decode)
          TyC (c' "Datahike.TyCode") FS (c' "Datahike.FindSpec") DB (c' "Datahike.DB")
          admit (fn [ci] (swap! a/ansatz-env kenv/check-constant ci))]
      (admit (kenv/mk-def (nm "Datahike.Decode") [] (e/forall' "_" TyC type0 :default) Decode :hints :opaque))
      (admit (kenv/mk-def (nm "Datahike.Result") [] (e/forall' "_" FS type0 :default) Result :hints :opaque))
      (admit (kenv/mk-axiom (nm "Datahike.DB") [] type0))
      ;; THE DEPENDENT q : DB → (f : FindSpec) → Result f
      (admit (kenv/mk-axiom (nm "Datahike.q") []
                            (e/forall' "db" DB (e/forall' "f" FS (e/app (c' "Datahike.Result") (e/bvar 0)) :default) :default)))
      ;; a :where DATA PATTERN [?e :attr ?v] as a relation: Datahike.scan (V:Type) db attr :
      ;; List (Entity × V), Entity = Nat. The :where lift joins these on shared variables.
      (admit (kenv/mk-axiom (nm "Datahike.scan") []
                            (let [V (e/fvar 1)]
                              (-> (listOf (prodOf natT V))
                                  (#(e/forall' "a" natT % :default)) (#(e/forall' "db" DB % :default))
                                  (#(e/forall' "V" type0 (e/abstract1 % 1) :default))))))))
  (a/env))

;; ── the :where → relational plan lift (joins on shared variables) ────────────
(defn- prod-fst [A B p] (e/app* (c' "Prod.fst" z z) A B p))
(defn- prod-snd [A B p] (e/app* (c' "Prod.snd" z z) A B p))

(defn where-entity-join
  "Lift two :where data-patterns that SHARE the entity ?e — `[?e a1 ?x]` and `[?e a2 ?y]` — into the
   relational plan `Map.join fst fst (scan X db a1) (scan Y db a2) : List ((Nat×X) × (Nat×Y))`, the
   join on the shared entity. `db` a kernel DB term; each pattern `{:attr <Nat term> :vtype <Type>}`.
   (The n-way / non-entity-join general case folds this; the find-spec then projects.) Requires
   install-axioms! + kmap."
  [db {ax :attr X :vtype} {ay :attr Y :vtype}]
  (let [scanX (e/app* (c' "Datahike.scan") X db ax)        ; List (Nat × X)
        scanY (e/app* (c' "Datahike.scan") Y db ay)        ; List (Nat × Y)
        NX (prodOf natT X) NY (prodOf natT Y)
        kf (e/lam "p" NX (prod-fst natT X (e/bvar 0)) :default)
        lf (e/lam "p" NY (prod-fst natT Y (e/bvar 0)) :default)]
    (e/app* (c' "Map.join") natT NX NY (c' "instDecidableEqNat") kf lf scanX scanY)))

(defn project-rel2
  "Project the two VALUE columns out of a `where-entity-join` of vtypes X, Y — i.e. the :find ?x ?y
   step. `join : List ((Nat×X) × (Nat×Y))` → `map (λp. (snd (fst p), snd (snd p))) join : List (X×Y)`,
   which is exactly `Result (frel <code-x> <code-y>)` — so the lifted query inhabits the dependent
   q's type. (Drops the entity column; n-ary projection generalizes this.)"
  [join X Y]
  (let [NX (prodOf natT X) NY (prodOf natT Y) PXY (prodOf NX NY) XY (prodOf X Y)
        proj (e/lam "p" PXY
                    (e/app* (c' "Prod.mk" z z) X Y
                            (prod-snd natT X (prod-fst NX NY (e/bvar 0)))
                            (prod-snd natT Y (prod-snd NX NY (e/bvar 0)))) :default)]
    (e/app* (c' "List.map" z z) PXY XY proj join)))

(defn rel2-plan
  "The full relational plan for a 2-pattern entity-join + 2-var projection, over GIVEN scan terms
   (each : List (Nat × V)) — Map.join on the entity (fst), then project the values → List (X × Y).
   `scanX`/`scanY` may be Datahike.scan terms (for optimization) OR fvars (for codegen/execution: run
   it with the real (entity,value) pairs datahike returns, and it equals the native :find ?x ?y)."
  [scanX scanY X Y]
  (let [NX (prodOf natT X) NY (prodOf natT Y)
        kf (e/lam "p" NX (prod-fst natT X (e/bvar 0)) :default)
        lf (e/lam "p" NY (prod-fst natT Y (e/bvar 0)) :default)]
    (project-rel2 (e/app* (c' "Map.join") natT NX NY (c' "instDecidableEqNat") kf lf scanX scanY) X Y)))

;; ── the :find-clause → FindSpec lift (α for the dependent typing) ─────────────
(def ^:private tycode-of
  "datahike schema :db/valueType → a Datahike.TyCode constructor name. Extend as TyCode grows."
  {:db.type/long "tint" :db.type/boolean "tbool"
   :long "tint" :boolean "tbool" :int "tint" :bool "tbool"})   ; tolerant aliases

(defn find->findspec
  "Map a NORMALIZED :find spec → a Datahike.FindSpec kernel value (so `Datahike.q db (find->findspec
   spec)` is precisely typed). `spec` = {:kind :scalar|:coll|:tuple|:rel, :types [valueType …]} —
   `:kind` from the parser's FindScalar/FindColl/FindTuple/FindRel, `:types` from each find-var's
   schema :db/valueType. (Currently scalar/coll take 1 type, tuple/rel 2 — n-ary is a follow-up.)
   Requires install-axioms!."
  [{:keys [kind types]}]
  (let [tc   (fn [vt] (e/const' (nm (str "Datahike.TyCode." (or (tycode-of vt)
                                                                (throw (ex-info "unknown :db/valueType" {:vt vt}))))) []))
        ctor (fn [c & args] (apply e/app* (e/const' (nm (str "Datahike.FindSpec." c)) []) args))]
    (case kind
      :scalar (ctor "fscalar" (tc (first types)))
      :coll   (ctor "fcoll"   (tc (first types)))
      :tuple  (ctor "ftuple"  (tc (first types)) (tc (second types)))
      :rel    (ctor "frel"    (tc (first types)) (tc (second types))))))

;; ── α : datahike logical IR (as plain data) → Ansatz kernel term ─────────────
;; A normalized datahike query node (the relevant subset):
;;   {:op :scan   :src <fvar> }                       — LScan, the relation source (List Row)
;;   {:op :filter :pred <kernel-pred-term> :in <q> }  — LFilter
;;   {:op :join   :kf <term> :lf <term> :row <Type> :left <q> :right <q>} — LEntityJoin (equi-join)
(defn elem-type
  "The ELEMENT type of the rows a (sub)query yields: a scan/filter yields `row-type`; an equi-join
   yields a PAIR `Prod row row` (so a filter ABOVE a join must use the pair type, not the row type)."
  [{:keys [op] :as q} row-type]
  (case op
    :scan   row-type
    :filter (elem-type (:in q) row-type)
    :join   (e/app* (e/const' (nm "Prod") [z z]) (:row q) (:row q))))

(defn lift
  "α: a normalized datahike query (data) → an Ansatz kernel term. `row-type` is a scan row's type
   (carries the schema). Element types are computed bottom-up (see `elem-type`) so a filter over a
   join is typed at the PAIR type and the result type-checks. Scans must already be kernel terms."
  [{:keys [op] :as q} row-type]
  (case op
    :scan   (:src q)
    :filter (e/app* (e/const' (nm "List.filter") [z]) (elem-type (:in q) row-type)
                    (:pred q) (lift (:in q) row-type))
    :join   (e/app* (e/const' (nm "Map.join") [])
                    (:key-type q) (:row q) (:row q) (:deceq q) (:kf q) (:lf q)
                    (lift (:left q) (:row q)) (lift (:right q) (:row q)))))

;; ── γ : Ansatz plan → datahike logical IR (data) ─────────────────────────────
(defn- lower-source
  "A plan :source leaf → datahike IR. A `Datahike.q db f` term → a query node carrying the find-spec
   value `f`; anything else → an opaque scan over the raw term. (The filter→q pushdown over the
   List-returning find-specs — q_pred / :q-where — is a separate law, a follow-up.)"
  [term]
  (let [[h args] (e/get-app-fn-args term)
        hn (when (e/const? h) (name/->string (e/const-name h)))]
    (case hn
      "Datahike.q" {:op :q :db (nth args 0) :find (nth args 1)}
      {:op :scan :src term})))

(defn lower
  "γ: an Ansatz plan node (from term->plan, after optimization) → datahike logical IR data. A
   :join → :entity-join, :filter → :filter (placed wherever the optimizer moved it — e.g. pushed
   into a join input), :source → a scan (or a FILTERED scan if the filter was pushed into q)."
  [pl]
  (case (:op pl)
    :source (lower-source (:term pl))
    :filter {:op :filter :pred (:pred pl) :in (lower (:input pl))}
    :map    {:op :project :fn (:fn pl) :in (lower (:input pl))}
    :join   {:op :entity-join :kf (:kf pl) :lf (:lf pl)
             :left (lower (:left pl)) :right (lower (:right pl))}
    {:op (:op pl) :raw pl}))

;; ── decorrelation: a correlated subquery in a transducer IS a join ───────────
(defn decorrelate
  "Recognize the CORRELATED-SUBQUERY shape and rewrite it to a join (the α move that turns N per-row
   datahike queries into ONE join the verified planner can then optimize). Given the components of
     mapcat (λrow. map proj (filter (λo. eq (lf o) (kf row)) scan)) rows
   build the equivalent kernel term  map (proj∘snd) (Map.join kf lf rows scan)  — Map.join already IS
   the flatMap-of-filter form (bucket_content), so this is sound by that definition."
  [{:keys [row-type key-type deceq kf lf rows scan]}]
  (e/app* (e/const' (nm "Map.join") [])
          key-type row-type row-type deceq kf lf rows scan))

;; ── register (side-effect of load) ───────────────────────────────────────────
(defn datahike-present? []
  (boolean (try (require 'datahike.api) true (catch Throwable _ false))))

(bridge/register-engine!
 :datahike
 {:detect?  datahike-present?
  ;; :lift here takes [normalized-query row-type]; bridge/optimize-plan calls (lift ir), so callers
  ;; partial-apply the row-type, or use lift/lower directly. Exposed for direct use + tests.
  :lift     (fn [[q row-type]] (lift q row-type))
  :lower    lower})
