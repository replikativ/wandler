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

(deftest transducer-backend-matches-eager
  (when (ready?)
    (reset! a/ansatz-env @test-env/init-full-env)
    ((requiring-resolve 'wandler.kmap/install!))
    ((requiring-resolve 'wandler.laws.relational/install!))
    ((requiring-resolve 'wandler.surface.collections/install!))
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
