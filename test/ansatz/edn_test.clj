(ns ansatz.edn-test
  (:require [ansatz.edn :as edn]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(def ^:private init-full-env test-env/init-full-env)

(defn- kernel-verifies? [env nm]
  (let [tc (doto (ansatz.kernel.TypeChecker. env) (.setFuel 80000000))
        ci (env/lookup env (name/from-string nm))]
    (and ci (.isDefEq tc (.inferType tc (.value ci)) (.type ci)))))

(deftest edn-core-installs-and-verifies
  ;; Integration: the EDN value universe + core ops + the get-after-assoc law
  ;; install on a real Init env, and every declaration kernel-verifies. Skips
  ;; when init.ndjson is absent.
  (if-let [kenv @init-full-env]
    (let [saved @a/ansatz-env]
      (try
        (reset! a/ansatz-env kenv)
        (let [env (edn/install-core!)]
          ;; type + auto structural-recursion machinery
          (is (some? (env/lookup env (name/from-string "Value.rec"))))
          (is (some? (env/lookup env (name/from-string "Value.below"))))
          (is (some? (env/lookup env (name/from-string "Value.brecOn"))))
          ;; ops kernel-verify (value : type)
          (is (kernel-verifies? env "vassoc"))
          (is (kernel-verifies? env "vget1"))
          (is (kernel-verifies? env "vcount"))   ;; recursive op via auto-sizeOf
          ;; the get-after-assoc law was admitted (proof checked at definition)
          (is (some? (env/lookup env (name/from-string "vget-vassoc")))))
        (finally (reset! a/ansatz-env saved))))
    (do
      (println "SKIP edn-core-installs-and-verifies: test-data/init.ndjson absent")
      (is true))))
