(ns ansatz.alist-test
  "EXTRINSIC association-list map: AList K V = List(K×V), NO NodupKeys proof. Its operations
   (AList.empty/get/put) are plain List-op COMPOSITIONS, so they compose FREELY and the
   composition kernel-verifies with no per-op preservation proof — the contrast with the
   intrinsic Subtype-Map (Map.insert carries an insert_nodupkeys proof). Runtime is a Clojure
   hash-map (empty→{}, get→get, put→assoc). The map invariant is a SEPARATE proposition,
   established only at a boundary that consumes it as a verified Map. See
   [[pipelines-system-design]]."
  (:require [ansatz.core :as a]
            [ansatz.collections :as coll]
            [ansatz.relational :as rel]
            [ansatz.kmap :as kmap]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- kernel-checks? [nm]
  (when-let [ci (kenv/lookup (a/env) (name/from-string nm))]
    (try (kenv/check-constant (a/env)
           (kenv/mk-def (name/from-string (str "__chk_" nm))
                        (kenv/ci-level-params ci) (kenv/ci-type ci) (kenv/ci-value ci)) 50000000)
         true (catch Throwable _ false))))

(deftest extrinsic-alist-composes-and-verifies
  (if-let [kenv* @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv*)
      (kmap/install!) (coll/install!) (rel/install!)
      ;; AList.empty/get/put kernel-verified on install (plain List compositions, no proof)
      (is (some? (kenv/lookup (a/env) (name/from-string "AList.put"))) "AList.put defined")
      (binding [a/*verbose* false]
        ;; build {1→10, 2→20} by composing puts, then look up — composes freely
        (eval '(ansatz.core/defn al-map [k :- Nat] Nat
                 (aget (aput (aput (aempty Nat Nat) 1 10) 2 20) k 0))))
      ;; (1) the COMPOSITION kernel-verifies — no proof threaded
      (is (true? (kernel-checks? "al-map")) "composed alist function passes check-constant")
      ;; (2) runs correctly via the hash-map runtime
      (is (= 10 ((resolve 'al-map) 1))  "get existing key 1")
      (is (= 20 ((resolve 'al-map) 2))  "put overwrites/inserts, get key 2")
      (is (= 0  ((resolve 'al-map) 99)) "get missing key → default")
      ;; frequencies = a foldl over the extrinsic map (put-bump) — also verifies, no tax
      (binding [a/*verbose* false]
        (eval '(ansatz.core/defn al-freq [xs :- (List Nat)] (List (Prod Nat Nat)) (frequencies xs))))
      (is (true? (kernel-checks? "al-freq")) "frequencies (foldl AList.put-bump) passes check-constant")
      (is (= {1 2, 2 1, 3 3} ((resolve 'al-freq) [1 1 2 3 3 3])) "frequencies counts via hash-map runtime")
      (is (= {} ((resolve 'al-freq) [])) "frequencies of empty"))
    (do (println "SKIP extrinsic-alist-composes-and-verifies: no Init env") (is true))))
