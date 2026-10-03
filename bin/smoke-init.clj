;; Public store/bootstrap smoke check, separate from the low-level test fixtures.
;; clojure -J-Xmx8g -M bin/smoke-init.clj <current-format-store> [branch]
(require '[ansatz.core :as a]
         '[wandler.core :as w])

(let [[store-path branch] *command-line-args*]
  (when-not store-path
    (throw (ex-info "Pass a current-format Init store path and optional branch" {})))
  (binding [a/*verbose* false]
    (a/init! store-path (or branch "init"))
    (w/install!)
    (w/install-streaming!)
    (w/install-laws!)
    (a/defn smoke-big-squares [xs :- (List Nat)] Nat
      (reduce + 0 (map (fn [x] (* x x)) (filter (fn [x] (< 10 x)) xs))))))

(when-not (= 544 (smoke-big-squares [3 5 12 7 20 1]))
  (throw (ex-info "Quickstart pipeline returned a wrong result" {})))
(when-not (:verified? (w/explain 'smoke-big-squares))
  (throw (ex-info "Quickstart pipeline did not certify" (w/explain 'smoke-big-squares))))
(println "Public current-format Init initialization and quickstart pipeline passed")
(shutdown-agents)
