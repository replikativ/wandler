(ns wandler.physical-test
  "Physical backend selection below the mode lattice (wandler.exec.physical): the batch route picks a
   physical REALIZATION over the plan lens. :eager (unboxed amapl) is the unchanged default; :transduce
   emits a native Clojure transducer pipeline — opt-in via execute's :physical until boundedness
   automates the choice. Both run the SAME verified pipeline (the fusion proofs are the certificate)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [wandler.exec.mode :as m]
            [wandler.exec.physical :as phys]
            [wandler.optimize.plan :as plan]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(defn- ready? [] (some? @test-env/init-full-env))

(deftest physical-route-tag
  ;; structural: a linear map/filter pipeline is transducible (→ :transduce when requested); a foldl /
  ;; bare source is not (→ :eager).
  (let [src {:op :source :term nil}]
    (is (= :transduce (phys/physical-route {:op :map :input src} :requested :transduce)))
    (is (= :eager     (phys/physical-route {:op :map :input src})))                 ; default unchanged
    (is (= :eager     (phys/physical-route {:op :foldl :input src} :requested :transduce))) ; foldl → eager
    (is (= :eager     (phys/physical-route src :requested :transduce)))))           ; bare source → eager

(deftest chunkability-classifier
  ;; the chunked-array model (docs/PHYSICAL_PLANNER.md): map/filter/fold chains are chunkable (bounded
  ;; per-chunk passes + monoid merge); join/group_by are cross-chunk (→ stratum/grace-hash); bare
  ;; source has nothing to chunk.
  (let [src   {:op :source :term nil}
        mff   {:op :filter :input {:op :map :input {:op :foldl :input src}}}  ; filter∘map∘foldl
        joinp {:op :map :input {:op :join :left src :right src}}
        grp   {:op :group-by :input src}]
    (is (phys/chunkable? mff)        "map/filter/fold chain is chunkable")
    (is (not (phys/chunkable? joinp)) "a join in the chain is cross-chunk → not chunkable")
    (is (not (phys/chunkable? grp))   "group_by is cross-chunk → not chunkable")
    (is (not (phys/chunkable? src))   "bare source has nothing to chunk")
    (is (= [:source :reduce :per-chunk :per-chunk] (:classes (phys/classify mff))) "per-op chunk classes (innermost-first)")
    (is (true? (:chunkable? (phys/classify mff))))
    (is (= :cross-chunk (first (:classes (phys/classify grp)))) "group_by classed cross-chunk")))

(deftest transducer-backend-matches-eager
  (when (ready?)
    (reset! a/ansatz-env @test-env/init-full-env)
    ((requiring-resolve 'wandler.kmap/install!))
    ((requiring-resolve 'wandler.clean.laws.faq/install!))
    ((requiring-resolve 'wandler.clean.surface.collections/install!))
    (let [natT    (e/const' (nm "Nat") [])
          listNat (e/app (e/const' (nm "List") [z]) natT)
          xs      (e/fvar 1)
          sq      (e/lam "x" natT (e/app* (e/const' (nm "Nat.mul") []) (e/bvar 0) (e/bvar 0)) :default)
          ;; (List.map (λx. x*x) xs) — a producing pipeline (transducible)
          term    (e/app* (e/const' (nm "List.map") [z z]) natT natT sq xs)
          elab    {:term term :lctx {1 {:name "xs" :type listNat}}}
          tr      (m/execute (a/env) elab :physical :transduce)
          eg      (m/execute (a/env) elab)]
      (is (= :transduce (:physical tr)) "explicit :physical :transduce picks the transducer backend")
      (is (= :eager     (:physical eg)) "default is the unchanged eager backend")
      ;; both realizations compute the same verified pipeline
      (is (= [1 4 9] (vec ((:run tr) [1 2 3]))) "transducer backend runs correctly")
      (is (= [1 4 9] (vec ((:run eg) [1 2 3]))) "eager backend runs correctly (unchanged)"))))

(deftest array-backend-seam
  ;; :array routes to a registered chunked-array backend (raster/stratum plug in here); with none, it
  ;; falls back to the eager/apfoldl realization — result-equal. (Toy backend reuses the transducer
  ;; emission as a stand-in to exercise the seam.)
  (when (ready?)
    (reset! a/ansatz-env @test-env/init-full-env)
    ((requiring-resolve 'wandler.kmap/install!))
    ((requiring-resolve 'wandler.clean.laws.faq/install!))
    ((requiring-resolve 'wandler.clean.surface.collections/install!))
    (let [natT    (e/const' (nm "Nat") [])
          listNat (e/app (e/const' (nm "List") [z]) natT)
          xs      (e/fvar 1)
          sq      (e/lam "x" natT (e/app* (e/const' (nm "Nat.mul") []) (e/bvar 0) (e/bvar 0)) :default)
          term    (e/app* (e/const' (nm "List.map") [z z]) natT natT sq xs)
          elab    {:term term :lctx {1 {:name "xs" :type listNat}}}]
      (phys/clear-array-backends!)
      (let [r (m/execute (a/env) elab :physical :array)]
        (is (= :eager (:physical r)) "no array backend registered → eager fallback (result-equal)")
        (is (= [1 4 9] (vec ((:run r) [1 2 3])))))
      (phys/register-array-backend! (fn [env plan names] (phys/plan->transducer env plan names)))
      (let [r (m/execute (a/env) elab :physical :array)]
        (is (= :array (:physical r)) "a registered array backend serves the :array tag")
        (is (= [1 4 9] (vec ((:run r) [1 2 3])))))
      (phys/clear-array-backends!))))

(deftest cost-backend-push-down-is-cost-based
  ;; B2: the executor consults choose-cost-form — a COST-backend serves the :array tag only when its
  ;; advertised cost beats the eager Clojure cost; otherwise it declines and the eager realization runs.
  ;; (Fake backend reuses the transducer emission as a result-equal stand-in — no raster dep.)
  (when (ready?)
    (reset! a/ansatz-env @test-env/init-full-env)
    ((requiring-resolve 'wandler.kmap/install!))
    ((requiring-resolve 'wandler.clean.laws.faq/install!))
    ((requiring-resolve 'wandler.clean.surface.collections/install!))
    (let [natT    (e/const' (nm "Nat") [])
          listNat (e/app (e/const' (nm "List") [z]) natT)
          xs      (e/fvar 1)
          sq      (e/lam "x" natT (e/app* (e/const' (nm "Nat.mul") []) (e/bvar 0) (e/bvar 0)) :default)
          term    (e/app* (e/const' (nm "List.map") [z z]) natT natT sq xs)
          elab    {:term term :lctx {1 {:name "xs" :type listNat}}}
          lower   (fn [env plan names] (phys/plan->transducer env plan names))]
      (phys/clear-array-backends!) (phys/clear-cost-backends!)
      ;; CHEAP engine (cost = eager/2) → chosen
      (phys/register-cost-backend! {:name :fake :lower lower :cost (fn [_plan eager] (* 0.5 eager))})
      (let [r (m/execute (a/env) elab :physical :array)]
        (is (= :array (:physical r)) "a cost-backend cheaper than eager serves the :array tag")
        (is (= [1 4 9] (vec ((:run r) [1 2 3])))))
      ;; EXPENSIVE engine (cost = eager*2) → declines, eager runs (result-equal)
      (phys/clear-cost-backends!)
      (phys/register-cost-backend! {:name :fake :lower lower :cost (fn [_plan eager] (* 2.0 eager))})
      (let [r (m/execute (a/env) elab :physical :array)]
        (is (= :eager (:physical r)) "a cost-backend MORE expensive than eager is declined → eager")
        (is (= [1 4 9] (vec ((:run r) [1 2 3])))))
      (phys/clear-cost-backends!))))
