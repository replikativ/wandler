(ns wandler.refine-test
  "Dependent-type filter elimination: a filter whose predicate is provably constant
   over the element type is removed (always-true) or empties the pipeline
   (always-false), kernel-proven. Gated on an Init env."
  (:require [wandler.surface.refine :as refine]
            [wandler.reducers.plan :as pl]
            [wandler.reducers :as r]
            [wandler.test-env :as test-env]
            [wandler.surface.malli :as malli]
            [ansatz.core :as a]
            [wandler.surface.records :as rec]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private Nat (e/const' (nm "Nat") []))

(defn- malli-available?
  "metosin/malli is an OPTIONAL dep (:malli alias); the contract-boundary test
   uses it at runtime (rec/validate / rec/conform) and skips when it's absent so
   `clj -M:test` and `clj -M:test:malli` never diverge into errors."
  []
  (try (require 'malli.core) true (catch Throwable _ false)))

;; (>= n 0) over Nat  →  λn. Nat.ble 0 n   (always true)
(defn- nonneg-cfn []
  (r/certified-fn {:name 'nonneg
                   :kernel-term (e/lam "n" Nat
                                       (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 0) (e/bvar 0))
                                       :default)
                   :runtime (fn [n] (<= 0 n))}))

;; (< n 0) over Nat  →  λn. Nat.blt n 0   (always false)
(defn- neg-cfn []
  (r/certified-fn {:name 'neg
                   :kernel-term (e/lam "n" Nat
                                       (e/app* (e/const' (nm "Nat.blt") []) (e/bvar 0) (e/lit-nat 0))
                                       :default)
                   :runtime (fn [n] (< n 0))}))

;; (= n 5) over Nat  →  λn. Nat.beq n 5   (NOT constant)
(defn- eq5-cfn []
  (r/certified-fn {:name 'eq5
                   :kernel-term (e/lam "n" Nat
                                       (e/app* (e/const' (nm "Nat.beq") []) (e/bvar 0) (e/lit-nat 5))
                                       :default)
                   :runtime (fn [n] (= n 5))}))

(def ^:private add-cfn
  (delay (r/certified-fn {:name 'Nat.add :kernel-term (e/const' (nm "Nat.add") []) :runtime +})))

(defn- sum-plan [filter-cfn]
  (pl/plan (pl/producer Nat) [{:op :filter :fn filter-cfn}] (pl/fold-consumer @add-cfn 0)))

(deftest prove-const-direct
  (if-let [kenv @test-env/init-full-env]
    (do
      ;; the prover proves the always-true and always-false predicates, rejects the rest
      (is (= true (:value (refine/prove-const kenv (:kernel-term (r/certification (nonneg-cfn))) Nat))))
      (is (= false (:value (refine/prove-const kenv (:kernel-term (r/certification (neg-cfn))) Nat))))
      (is (nil? (refine/prove-const kenv (:kernel-term (r/certification (eq5-cfn))) Nat))))
    (do (println "SKIP prove-const-direct: no Init env") (is true))))

(deftest always-true-filter-eliminated
  (if-let [kenv @test-env/init-full-env]
    (let [res (pl/eliminate-filters kenv (sum-plan (nonneg-cfn)))
          xs [1 2 3 4 5]]
      ;; the filter is gone, with a kernel-checked proof
      (is (= [] (mapv :op (:transforms res))))
      (is (false? (:empty? res)))
      (is (= :filter-elim-always-true (:rule (last (:proofs res)))))
      (is (re-find #"Eq\." (e/->string (:theorem-type (last (:proofs res))))))
      ;; result matches the un-eliminated pipeline (the filter passed everything anyway)
      (is (= (reduce + 0 (clojure.core/filter #(<= 0 %) xs)) (pl/run res xs))))
    (do (println "SKIP always-true-filter-eliminated: no Init env") (is true))))

(deftest always-false-filter-empties-pipeline
  (if-let [kenv @test-env/init-full-env]
    (let [res (pl/eliminate-filters kenv (sum-plan (neg-cfn)))]
      (is (true? (:empty? res)))
      (is (= :filter-elim-always-false (:rule (last (:proofs res)))))
      ;; the pipeline yields the fold seed — nothing passes
      (is (= 0 (pl/run res [1 2 3 4 5]))))
    (is true)))

(deftest tier3-subtype-refinement-eliminates-filter
  ;; Element type is a refinement {v : Nat // 18 <= v}. The filter (>= v 18) is NOT
  ;; definitionally true (Tier 1 / rfl fails), but the Subtype's carried .property
  ;; discharges it (Tier 3). This is the dependent-type payoff.
  (if-let [kenv @test-env/init-full-env]
    (let [u0 lvl/zero u1 (lvl/succ lvl/zero)
          Nat (e/const' (nm "Nat") [])
          lit18 (e/lit-nat 18)
          ;; P = fun v:Nat => 18 <= v
          P (e/lam "v" Nat (e/app* (e/const' (nm "LE.le") [u0]) Nat (e/const' (nm "instLENat") [])
                                   lit18 (e/bvar 0)) :default)
          T (e/app* (e/const' (nm "Subtype") [u1]) Nat P)
          valx (e/app* (e/const' (nm "Subtype.val") [u1]) Nat P (e/bvar 0))
          ;; predicate λx:T. Nat.ble 18 (val x)   = (>= (val x) 18)
          p (e/lam "x" T (e/app* (e/const' (nm "Nat.ble") []) lit18 valx) :default)
          res (refine/prove-const kenv p T)]
      (is (some? res))
      (is (= true (:value res)))
      ;; the proof used the refinement's property bridge, not rfl
      (is (re-find #"Nat.ble_eq_true_of_le" (e/->string (:proof res)))))
    (do (println "SKIP tier3-subtype-refinement-eliminates-filter: no Init env") (is true))))

(deftest tier3-string-length-refinement-eliminates-filter
  ;; STRINGS (#44 step 3): {s : String // 1 <= s.length} (malli [:string {:min 1}], non-empty).
  ;; The length filter (1 <= s.length) is redundant — the carried .property discharges it
  ;; DIRECTLY via Nat.ble_eq_true_of_le. The predicate reads the val THROUGH String.length, so
  ;; the bridge uses find-subtype-val to reach the val while leaving `m = length (val x)` OPAQUE.
  ;; Before the sharing-aware lift/instantiate1 fix (#46) this HUNG (omega/simp on the expanded
  ;; String.length term blew up); now it's a cheap syntactic discharge.
  (if-let [kenv @test-env/init-full-env]
    (let [u0 lvl/zero u1 (lvl/succ lvl/zero)
          Str (e/const' (nm "String") [])
          len (fn [s] (e/app (e/const' (nm "String.length") []) s))
          P (e/lam "s" Str (e/app* (e/const' (nm "LE.le") [u0]) Nat (e/const' (nm "instLENat") [])
                                   (e/lit-nat 1) (len (e/bvar 0))) :default)
          T (e/app* (e/const' (nm "Subtype") [u1]) Str P)
          valx (e/app* (e/const' (nm "Subtype.val") [u1]) Str P (e/bvar 0))
          ;; predicate λx:T. Nat.ble 1 (s.length)  =  (1 <= s.length)
          p (e/lam "x" T (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 1) (len valx)) :default)
          t0 (System/currentTimeMillis)
          res (refine/prove-const kenv p T)
          ms (- (System/currentTimeMillis) t0)]
      (is (< ms 30000) (str "must not blow up (was 25-min hang before #46); took " ms "ms"))
      (is (some? res) "string length refinement discharges the filter")
      (is (= true (:value res)) "non-empty {s // 1<=length} eliminates filter (1 <= length)")
      (is (re-find #"Nat.ble_eq_true_of_le" (e/->string (:proof res))) "direct property bridge"))
    (do (println "SKIP tier3-string-length-refinement-eliminates-filter: no Init env") (is true))))

(deftest omega-discharges-implication-and-upper-bound
  ;; The systematic omega path: filters that don't directly MATCH the refinement
  ;; but are IMPLIED by it (weaker lower bound), and UPPER-bound refinements, are
  ;; discharged via omega — cases the direct .property bridge can't reach.
  (if-let [kenv @test-env/init-full-env]
    (let [u0 lvl/zero u1 (lvl/succ lvl/zero)
          Nat (e/const' (nm "Nat") [])
          sub (fn [P] (e/app* (e/const' (nm "Subtype") [u1]) Nat P))
          valx (fn [P] (e/app* (e/const' (nm "Subtype.val") [u1]) Nat P (e/bvar 0)))
          ;; {v // 18 <= v}, filter (>= v 10)  → TRUE by implication (18<=v ⟹ 10<=v)
          Plo (e/lam "v" Nat (e/app* (e/const' (nm "LE.le") [u0]) Nat (e/const' (nm "instLENat") [])
                                     (e/lit-nat 18) (e/bvar 0)) :default)
          imp (e/lam "x" (sub Plo) (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 10) (valx Plo)) :default)
          ;; {v // v < 18}, filter (< v 18)  → TRUE (upper bound, via Nat.blt)
          Pup (e/lam "v" Nat (e/app* (e/const' (nm "LT.lt") [u0]) Nat (e/const' (nm "instLTNat") [])
                                     (e/bvar 0) (e/lit-nat 18)) :default)
          upper (e/lam "x" (sub Pup) (e/app* (e/const' (nm "Nat.blt") []) (valx Pup) (e/lit-nat 18)) :default)]
      (is (= true (:value (refine/prove-const kenv imp (sub Plo)))))     ; implication
      (is (= true (:value (refine/prove-const kenv upper (sub Pup))))))  ; upper bound
    (do (println "SKIP omega-discharges-implication-and-upper-bound: no Init env") (is true))))

(deftest update-on-refined-field-discharges-monotone
  ;; (update p :age inc) over a {age // 18 <= age} field: the result must be PROVEN
  ;; to still satisfy the refinement (18 <= succ age) — the omega-write. A monotone
  ;; fn is accepted (wrapped in Subtype.mk with the proof); a decreasing one is
  ;; rejected.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record URPerson
                 [:map [:age [:and :int [:>= 18]]] [:score [:and :int [:>= 0]]]]))
        (eval '(ansatz.core/defn ur-bump [p :- URPerson] URPerson (update p :age Nat.succ))))
      (let [ci (env/lookup (a/env) (name/from-string "ur-bump"))
            tc (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 50000000))]
        (is (true? (.isDefEq tc (.inferType tc (.value ci)) (.type ci))))
        ;; the update wrapped the result in Subtype.mk with the monotone proof
        (is (re-find #"Subtype.mk" (e/->string (.value ci))))))
    (do (println "SKIP update-on-refined-field-discharges-monotone: no Init env") (is true))))

(deftest refinement-always-false-and-bound-emission
  ;; Always-FALSE: a filter that contradicts the refinement (< k over >= k). And the
  ;; malli boundary emits upper bounds [:< k] and ranges [:>= a][:< b] as Subtypes.
  (if-let [kenv @test-env/init-full-env]
    (let [u0 lvl/zero u1 (lvl/succ lvl/zero)
          Nat (e/const' (nm "Nat") [])
          P (e/lam "v" Nat (e/app* (e/const' (nm "LE.le") [u0]) Nat (e/const' (nm "instLENat") [])
                                   (e/lit-nat 18) (e/bvar 0)) :default)
          T (e/app* (e/const' (nm "Subtype") [u1]) Nat P)
          valx (e/app* (e/const' (nm "Subtype.val") [u1]) Nat P (e/bvar 0))
          ;; filter (< v 18) over {v // 18 <= v} → always FALSE (contradiction)
          p (e/lam "x" T (e/app* (e/const' (nm "Nat.blt") []) valx (e/lit-nat 18)) :default)]
      (is (= false (:value (refine/prove-const kenv p T))))
      (is (re-find #"Subtype" (e/->string (malli/malli->type-expr [:and :int [:< 100]]))))
      (is (re-find #"And" (e/->string (malli/malli->type-expr [:and :int [:>= 18] [:< 65]])))))
    (do (println "SKIP refinement-always-false-and-bound-emission: no Init env") (is true))))

(deftest boundary-refinement-eliminates-filter-end-to-end
  ;; D→C→A: a Malli refinement schema becomes a Subtype element type at the boundary,
  ;; and a downstream filter matching the refinement is eliminated (Tier 3). The
  ;; "validate once at the edge, drop every downstream check" story.
  (if-let [kenv @test-env/init-full-env]
    (let [elem (malli/malli->type-expr [:and :int [:>= 18]])    ; D: → {v:Nat // 18≤v}
          [h args] (e/get-app-fn-args elem)
          Nat (e/const' (nm "Nat") [])
          P (second args)
          u1 (lvl/succ lvl/zero)
          valx (e/app* (e/const' (nm "Subtype.val") [u1]) Nat P (e/bvar 0))
          ;; filter (>= v 18) over a refined element: λx. Nat.ble 18 (val x)
          p (e/lam "x" elem (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 18) valx) :default)
          res (refine/prove-const kenv p elem)]
      (is (= "Subtype" (name/->string (e/const-name h))))        ; refinement → Subtype
      (is (= true (:value res)))                                 ; filter eliminated
      (is (re-find #"Nat.ble_eq_true_of_le" (e/->string (:proof res)))))
    (do (println "SKIP boundary-refinement-eliminates-filter-end-to-end: no Init env") (is true))))

(deftest refined-record-field-filter-eliminated
  ;; The keystone: a user-written refined record (age must be >= 18), a filter on
  ;; the refined field reads ergonomically (.val), compiles, verifies, and is
  ;; eliminated via the field's carried refinement. No axioms.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RPerson
                 [:map [:age [:and :int [:>= 18]]] [:score [:and :int [:>= 0]]]]))
        (eval '(ansatz.core/defn r-adult? [p :- RPerson] Bool (>= (:age p) 18))))
      (let [ci (env/lookup (a/env) (name/from-string "r-adult?"))
            body (e/->string (.value ci))
            res (refine/prove-const (a/env) (.value ci) (e/const' (name/from-string "RPerson") []))]
        ;; the refined field read unwrapped to its underlying value
        (is (re-find #"Subtype.val" body))
        ;; the filter is proven always-true via the field's refinement (Tier 3)
        (is (= true (:value res)))
        (is (re-find #"ble_eq_true_of_le" (e/->string (:proof res))))))
    (do (println "SKIP refined-record-field-filter-eliminated: no Init env") (is true))))

(deftest refined-field-write-discharges-or-rejects
  ;; Writing a refined field discharges its predicate: an in-range literal is
  ;; accepted (proof by rfl), an out-of-range literal is REJECTED at verification
  ;; (you genuinely can't put 5 in a >= 18 field). The gradual-typing write discipline.
  (if-let [kenv @test-env/init-full-env]
    (letfn [(defok? [form] (binding [a/*verbose* false]
                             (try (do (eval form) true) (catch Throwable _ false))))]
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record WPerson
                 [:map [:age [:and :int [:>= 18]]] [:score [:and :int [:>= 0]]]])))
      (is (true? (defok? '(ansatz.core/defn w-ok [p :- WPerson] WPerson (assoc p :age 30)))))
      (is (false? (defok? '(ansatz.core/defn w-bad [p :- WPerson] WPerson (assoc p :age 5)))))
      (is (true? (defok? '(ansatz.core/defn w-score [p :- WPerson] WPerson (assoc p :score 7)))))
      ;; the accepted write wraps the value in Subtype.mk
      (is (re-find #"Subtype.mk" (e/->string (.value (env/lookup (a/env) (name/from-string "w-ok")))))))
    (do (println "SKIP refined-field-write-discharges-or-rejects: no Init env") (is true))))

(deftest contract-boundary-validates-refinements
  ;; Slice 4: Malli validation is the contract boundary. Data that fails a
  ;; refinement is rejected at the edge; conformed data may be assumed by the
  ;; verified interior (the trusted gradual-typing seam).
  (if (and @test-env/init-full-env (malli-available?))
    (let [kenv @test-env/init-full-env]
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record CPerson
                 [:map [:age [:and :int [:>= 18]]] [:score [:and :int [:>= 0]]]])))
      (is (true? (rec/validate 'CPerson {:age 30 :score 5})))
      (is (false? (rec/validate 'CPerson {:age 5 :score 5})))         ; age < 18 fails
      (is (= {:age 25 :score 0} (rec/conform 'CPerson {:age 25 :score 0})))
      (is (thrown? Throwable (rec/conform 'CPerson {:age 5 :score 0}))))
    (do (println "SKIP contract-boundary-validates-refinements: no Init env or malli absent") (is true))))

(deftest non-constant-filter-kept
  (if-let [kenv @test-env/init-full-env]
    (let [res (pl/eliminate-filters kenv (sum-plan (eq5-cfn)))]
      ;; can't prove constant → filter stays, runs natively
      (is (= [:filter] (mapv :op (:transforms res))))
      (is (false? (:empty? res)))
      (is (= 5 (pl/run res [1 2 3 4 5 6 7]))))
    (is true)))
