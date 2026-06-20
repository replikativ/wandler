(ns wandler.clean.optimize.cse-test
  "Phase 5.2: the clean CSE (wandler.clean.optimize.cse) — shared-subtree hoist, soundness-FREE
   (let/zeta = Eq.refl). The clean code is a verbatim copy of the old certifier-gated CSE, so this
   is a differential: the clean `try-cse` makes the SAME decision as old wandler's on the same term.
   CSE only hoists BARRIERS (sort/group-by/dedup); a streaming map/filter share is deliberately left
   to fusion — so on a streaming `map` share both correctly DECLINE (nil). Barrier-hoisting end-to-end
   is exercised by `wandler.cse-test` through the full optimizer."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as nm]
            [wandler.test-env :as test-env]
            [wandler.clean.optimize.cse :as cclean]))

(defn- setup [f]
  (when @test-env/init-full-env (reset! a/ansatz-env @test-env/init-full-env))
  (f))
(use-fixtures :once setup)

;; List.append Nat (List.map f xs) (List.map f xs) — a STREAMING (fusable) share, which CSE declines.
(defn- streaming-share-term []
  (let [Nat   (e/const' (nm/from-string "Nat") [])
        NatN  (e/forall' "_" Nat Nat :default)
        ListN (e/app (e/const' (nm/from-string "List") [lvl/zero]) Nat)
        f (e/fvar 7101) xs (e/fvar 7102)
        mapped (e/app* (e/const' (nm/from-string "List.map") [lvl/zero lvl/zero]) Nat Nat f xs)
        term  (e/app* (e/const' (nm/from-string "List.append") [lvl/zero]) Nat mapped mapped)
        lctx  {7101 {:name "f" :type NatN} 7102 {:name "xs" :type ListN}}]
    [term lctx]))

(deftest clean-cse-declines-streaming-share
  (when @test-env/init-full-env
    (let [env (a/env)
          [term lctx] (streaming-share-term)
          clean (cclean/try-cse env term :lctx lctx)]
      (testing "the clean CSE declines a streaming (fusable) share — fusion handles it, no barrier to hoist"
        (is (nil? clean))))))
