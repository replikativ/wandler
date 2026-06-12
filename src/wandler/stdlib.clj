(ns wandler.stdlib
  "One-stop install! for the full Ansatz surface stdlib. Require this single namespace and the
   whole verified-body surface vocabulary is registered:
     - wandler.surface.collections : map/filter/reduce/count, take/drop/take-while/first/last/rest,
                            mapcat/map-indexed, transducer ingestion, ->/->> threading, list/[]
     - wandler.surface.records     : assoc/update/get-in/select-keys over def-record'd records
     - wandler.surface.relational  : join/group-by/->map
     - wandler.kmap        : the verified finite Map
   This replaces the scattered per-namespace install! calls and removes the load-order coupling
   they invited (e.g. ->/->> silently degrading to the type-arrow if a sub-namespace was missed).
   Each install! is idempotent."
  (:require [wandler.core]
            [wandler.surface.collections :as coll]
            [wandler.surface.records :as rec]
            [wandler.surface.relational :as rel]
            [wandler.kmap :as kmap]))

(defn install!
  "Install the full wandler surface + runtime (delegates to wandler.core/install!,
   which fills all three ansatz seams)."
  []
  ((requiring-resolve 'wandler.core/install!)))
