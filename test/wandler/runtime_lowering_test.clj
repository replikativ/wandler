(ns wandler.runtime-lowering-test
  "Arch #4: the runtime lowering table is a SINGLE extensible map (built-ins + register-lowering!),
   not a case + parallel head-list. register-lowering! is the open extension point — Lean's
   @[implemented_by] for a compiled op — letting a vocabulary register a lowering without editing
   builtin-lowerings, and the head auto-installs into ansatz's codegen-registry."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.surface.ingest :as ingest]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [wandler.runtime :as rt]))

(deftest lowering-table-is-the-single-source
  ;; install! registers exactly the table's keys (no separate head-list to drift from it).
  (let [heads (set (keys @rt/lowering-table))]
    (is (contains? heads "Map.join") "built-in vocabulary is in the table")
    (is (contains? heads "List.foldl"))
    (is (every? #(contains? @ingest/codegen-registry %) heads)
        "install! pointed codegen-registry at lower for every table head")))

(deftest register-lowering-extends-the-table
  ;; A fresh head registered through the open API lowers via codegen — without touching builtins.
  (rt/register-lowering! "Demo.twice" (fn [_env ca _args _names]
                                        (list 'clojure.core/* 2 (nth ca 0))))
  (is (contains? @rt/lowering-table "Demo.twice") "registered into the single table")
  (is (contains? @ingest/codegen-registry "Demo.twice")
      "and auto-installed into ansatz's codegen-registry")
  ;; ansatz codegen now lowers (Demo.twice n) via the registered fn
  (a/load-init!)
  (let [term (e/app (e/const' (name/from-string "Demo.twice") []) (e/lit-nat 21))
        code (cg/ansatz->clj (a/env) term [])]
    (is (= '(clojure.core/* 2 21) code) "the registered lowering drives codegen")))
