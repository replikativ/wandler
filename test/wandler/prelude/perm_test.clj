(ns wandler.prelude.perm-test
  "Validates wandler.prelude.perm: every Tier-1 List.Perm combinator proves and kernel-checks
   (authoritative check-constant), and install! registers all six. Mirrors Lean's
   Init/Data/List/Perm.lean as an owned Batteries-tier prelude. Requires the full Init store."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [wandler.prelude.perm :as perm]
            [wandler.test-env :as test-env]))

(defn- nm [s] (name/from-string s))
(defn- checks? [g p]
  (and (some? p)
       (try (kenv/check-constant (a/env) (kenv/mk-thm (nm "__chk__") [] g p)) true
            (catch Throwable _ false))))

(deftest perm-prelude-kernel-checks
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      ;; Each Tier-1 combinator proves + kernel-checks. flatMap_map_comm depends on
      ;; flatMap_cons_distrib_perm being registered, so prove them in install! order.
      (let [[g p] (perm/prove-flatMap-const-nil)]
        (is (checks? g p) "flatMap_const_nil (thin)"))
      (let [[g p] (perm/prove-flatMap-congr-perm)]
        (is (checks? g p) "flatMap_congr_perm (thin, flagship — no Lean counterpart)"))
      (let [[g p] (perm/prove-flatMap-append-distrib)]
        (is (checks? g p) "flatMap_append_distrib_perm"))
      (let [[g p] (perm/prove-flatMap-cons-distrib)]
        (is (checks? g p) "flatMap_cons_distrib_perm")
        (reset! a/ansatz-env (kenv/add-constant (a/env) (kenv/mk-thm (nm "List.flatMap_cons_distrib_perm") [] g p))))
      (let [[g p] (perm/prove-flatMap-map-comm)]
        (is (checks? g p) "flatMap_map_comm (Fubini / product transpose)"))
      (let [[g p] (perm/prove-foldflip-perm)]
        (is (checks? g p) "foldl_cons_perm")))
    (is true "SKIP perm-prelude: no Init env")))

(deftest perm-prelude-install
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (perm/install!)
      (is (every? #(some? (kenv/lookup (a/env) (nm %)))
                  ["List.flatMap_const_nil" "List.flatMap_congr_perm"
                   "List.flatMap_append_distrib_perm" "List.flatMap_cons_distrib_perm"
                   "List.flatMap_map_comm" "List.foldl_cons_perm"])
          "install! registers all six Tier-1 List.Perm combinators"))
    (is true "SKIP perm-prelude-install: no Init env")))
