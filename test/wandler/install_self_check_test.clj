(ns wandler.install-self-check-test
  "Phase 3.3 / strangler-retirement Phase A — the STRICT install self-check. `install-laws!` admits the
   proven law DAG; this test re-checks EVERY law it admits with the AUTHORITATIVE kernel `verifies?`
   (check-constant), so a law that is present-but-lenient-masked, or silently dropped, fails LOUDLY
   instead of quietly disabling an optimization. This is the safety rail under the clean-tree cutover:
   if a later rename/port breaks a proof, this goes red."
  (:require [wandler.core :as w]
            [wandler.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is testing]]))

(defn- const-names [e] (into #{} (map (comp str env/ci-name)) (env/all-constants e)))

(deftest install-laws-strict-self-check
  (if-let [ke @test-env/init-full-env]
    (do (reset! a/ansatz-env ke)
        (w/install!)
        (let [before (const-names (a/env))]
          (is (= :installed (w/install-laws!)) "install-laws! completes without throwing")
          (let [added (->> (env/all-constants (a/env))
                           (remove #(before (str (env/ci-name %))))
                           (filter env/thm?))               ; LAWS only — not the supporting defs/inductives
                bad   (remove (fn [ci] (env/verifies? (a/env) (env/ci-type ci) (env/ci-value ci)))
                              added)]
            (testing "install-laws! admitted a non-trivial law DAG"
              (is (pos? (count added)) "laws (theorems) were admitted"))
            (testing "EVERY admitted law kernel-verifies (no lenient-masked / swallowed proof)"
              (is (empty? bad)
                  (str "laws that do NOT pass check-constant: "
                       (mapv (comp str env/ci-name) bad)))))))
    (println "SKIP install-laws-strict-self-check: no Init env (storeless run)")))
