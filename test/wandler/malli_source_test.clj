(ns wandler.malli-source-test
  "Step 1 of the cross-engine plan: SOURCES declared by MALLI SCHEMAS. The Clojurian writes the malli
   schemas they already write; the planner derives the record model from them and the FAQ factorization
   runs — fields accessed BY KEY, not column index.

   What the schema buys (the payoff): a malli REFINEMENT becomes a kernel DEPENDENT TYPE, erased at runtime
   but exploited at plan time. `[:int {:min 0}]` → `Nat` (a refinement of Int); `[:int {:min k}]` →
   `Subtype Nat (k ≤ v)`. Here the `{:min 0}` on :amount is what makes the sum a COMMUTATIVE Nat monoid —
   which is exactly what licenses the aggregation-through-join factorization. The Clojurian never writes a
   Π or Σ; they write `[:int {:min 0}]` and the kernel reads a dependent type."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [wandler.core :as wc] [wandler.kmap :as km] [wandler.laws.faq :as rl]
            [wandler.optimize :as opt] [wandler.optimize.cost :as cost]
            [wandler.surface.malli :as am]
            [wandler.reducers.record :as rec]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as name] [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(defn- tn [t] (when (e/const? t) (name/->string (e/const-name t))))
(defn- setup [f]
  (when-let [k @test-env/init-full-env] (reset! a/ansatz-env k) (wc/install!) (km/install!) (rl/install!))
  (f))
(use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; the Clojurian's schemas — ordinary malli, with {:min 0} where the domain is non-negative
(def Customer [:map [:cid [:int {:min 0}]] [:region [:int {:min 0}]]])
(def Order    [:map [:oid [:int {:min 0}]] [:cid [:int {:min 0}]] [:amount [:int {:min 0}]]])

(deftest malli-schema-communicates-dependent-types
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [cust (am/malli-record Customer)
          ord  (am/malli-record Order)]
      (testing "the malli REFINEMENT is read as a kernel DEPENDENT TYPE"
        ;; `[:int {:min 0}]` → Nat (a refinement of Int); a bare `:int` would be Int.
        (is (= "Nat" (tn (am/malli->type-expr [:int {:min 0}]))) "{:min 0} ⇒ Nat (non-negativity in the type)")
        (is (= "Int" (tn (am/malli->type-expr :int))) "bare :int ⇒ Int (no refinement)")
        (is (every? #(= "Nat" (tn %)) (:field-types ord)) "every Order field is the dependent type Nat"))
      (testing "the schema gives the record model — fields by KEY, no hand-built kernel types"
        (is (= [:cid :region] (:keys cust)))
        (is (= {:oid 0 :cid 1 :amount 2} (:index ord)) "key → column index, straight from the schema")))))

(deftest faq-over-malli-declared-sources
  (if-not (ready?)
    (is true "skipped — no full kernel env")
    (let [cust (am/malli-record Customer)  ord (am/malli-record Order)
          custRec (:rec-type cust) ordRec (:rec-type ord)
          custFt (:field-types cust) ordFt (:field-types ord)
          listOf (fn [t] (e/app (e/const' (nm "List") [z]) t))
          dec (e/const' (nm "instDecidableEqNat") [])
          key (fn [m k] (get (:index m) k))   ; resolve a key → column index from the schema
          ;; the query, written against schema KEYS (:cid, :amount) — the planner builds the projections
          kf (e/lam "c" custRec (rec/rget custFt (key cust :cid) (e/bvar 0)) :default)
          lf (e/lam "o" ordRec  (rec/rget ordFt  (key ord  :cid) (e/bvar 0)) :default)
          join (e/app* (e/const' (nm "Map.join") []) (e/const' (nm "Nat") []) custRec ordRec dec kf lf
                       (e/fvar 7001) (e/fvar 7002))
          pairT (e/app* (e/const' (nm "Prod") [z z]) custRec ordRec)
          amount (e/lam "p" pairT (rec/rget ordFt (key ord :amount)
                            (e/app* (e/const' (nm "Prod.snd") [z z]) custRec ordRec (e/bvar 0))) :default)
          amts (e/app* (e/const' (nm "List.map") [z z]) pairT (e/const' (nm "Nat") []) amount join)
          sum (e/app* (e/const' (nm "List.foldl") [z z]) (e/const' (nm "Nat") []) (e/const' (nm "Nat") [])
                      (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) amts)
          lctx {7001 {:name "custs" :type (listOf custRec)} 7002 {:name "ords" :type (listOf ordRec)}}
          r (opt/optimize-cost (a/env) sum :lctx lctx :sizes {7001 1000 7002 1000})
          compile (fn [t] (let [t1 (e/abstract1 t 7002) l2 (e/lam "ords" (listOf ordRec) t1 :default)
                                t2 (e/abstract1 l2 7001) l1 (e/lam "custs" (listOf custRec) t2 :default)]
                            (eval (a/ansatz->clj (a/env) l1 []))))
          CU [[1 100] [2 200]] OR [[10 [1 50]] [11 [1 70]] [12 [2 30]]]
          run (fn [t] (long (((compile t) CU) OR)))]
      (testing "a query written from malli schemas factorizes (the {:min 0} ⇒ Nat licenses it) + executes"
        (is (:verified? r) "certified ≡ naive")
        (is (contains? (set (:rewrites r)) :fold-factor) "FAQ factorization fired over the malli-derived records")
        (is (= 150 (run sum)) "naive Σ :amount over customers⋈orders")
        (is (= 150 (run (:term r))) "factored Σ = same answer")))))
