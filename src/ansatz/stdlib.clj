(ns ansatz.stdlib
  "One-stop install! for the full Ansatz surface stdlib. Require this single namespace and the
   whole verified-body surface vocabulary is registered:
     - ansatz.collections : map/filter/reduce/count, take/drop/take-while/first/last/rest,
                            mapcat/map-indexed, transducer ingestion, ->/->> threading, list/[]
     - ansatz.records     : assoc/update/get-in/select-keys over def-record'd records
     - ansatz.relational  : join/group-by/->map
     - ansatz.kmap        : the verified finite Map
   This replaces the scattered per-namespace install! calls and removes the load-order coupling
   they invited (e.g. ->/->> silently degrading to the type-arrow if a sub-namespace was missed).
   Each install! is idempotent."
  (:require [ansatz.collections :as coll]
            [ansatz.records :as rec]
            [ansatz.relational :as rel]
            [ansatz.kmap :as kmap]))

(defn install!
  "Register the entire Ansatz surface stdlib (idempotent). Call AFTER the kernel env is set
   (some sub-installs consult it), e.g. (a/init! …) / (reset! a/ansatz-env …) then
   (stdlib/install!)."
  []
  (kmap/install!)
  (coll/install!)
  (rel/install!)
  (rec/install!))
