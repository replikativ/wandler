(ns wandler.kmap-test
  "The verified Map: keys/NodupKeys/Map defined, the insert-preserves-NodupKeys
   theorem and the generic ops (empty/insert/lookup over any [DecidableEq K])
   kernel-check, and maps over Nat AND String keys verify and run."
  (:require [ansatz.core :as a]
            [wandler.kmap :as kmap]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- recheck [nm]
  ;; Re-infer the stored proof/def type and confirm it defeq the declared type.
  (when-let [ci (env/lookup (a/env) (name/from-string nm))]
    (let [tc (doto (TypeChecker. (a/env)) (.setFuel 50000000))]
      (.isDefEq tc (.inferType tc (.value ci)) (.type ci)))))

(deftest map-installs-and-verifies
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (doseq [n ["Map.keys" "Map.NodupKeys" "Map"]]
        (is (some? (env/lookup (a/env) (name/from-string n)))))
      ;; the preservation theorem, every op, and the refinement laws type-check
      (doseq [n ["Map.insert_nodupkeys" "Map.empty" "Map.insert" "Map.lookup"
                 "Map.lookup_empty_eq" "Map.lookup_insert_head"
                 ;; LawfulBEq-from-DecidableEq instance — fills the Init gap so the
                 ;; Map lookup laws can use beq_iff_eq / beq_eq_false_iff_ne
                 "instLawfulBEqOfDecidableEq"]]
        (is (true? (recheck n)))))
    (do (println "SKIP map-installs-and-verifies: no Init env") (is true))))

;; helpers to build kernel terms for a concrete key/value type
(let [con  (fn [s] (e/const' (name/from-string s) []))]
  (defn- mk-empty [K V] (e/app* (con "Map.empty") K V))
  (defn- mk-insert [K V deceq k v m] (e/app* (con "Map.insert") K V deceq k v m))
  (defn- mk-lookup [K V deceq k m] (e/app* (con "Map.lookup") K V deceq k m)))

(deftest map-ops-run-nat-keys
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (let [con  #(e/const' (name/from-string %) [])
            nat  (con "Nat") deceq (con "instDecidableEqNat")
            ins  (fn [k v m] (mk-insert nat nat deceq (e/lit-nat k) (e/lit-nat v) m))
            look (fn [k m] (a/ansatz->clj (a/env) (mk-lookup nat nat deceq (e/lit-nat k) m) []))
            m    (ins 2 20 (ins 1 10 (mk-empty nat nat)))
            m2   (ins 1 99 m)]
        (is (= 20  (eval (look 2 m))))
        (is (= nil (eval (look 9 m))))
        (is (= 99  (eval (look 1 m2))))))
    (do (println "SKIP map-ops-run-nat-keys: no Init env") (is true))))

(deftest map-ops-run-string-keys
  ;; Beyond Nat: String keys (instDecidableEqString) → Nat values, verified + run.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (kmap/install!)
      (let [con  #(e/const' (name/from-string %) [])
            strT (con "String") nat (con "Nat") deceq (con "instDecidableEqString")
            ins  (fn [k v m] (mk-insert strT nat deceq (e/lit-str k) (e/lit-nat v) m))
            look (fn [k m] (a/ansatz->clj (a/env) (mk-lookup strT nat deceq (e/lit-str k) m) []))
            tc   (doto (TypeChecker. (a/env)) (.setFuel 50000000))
            m    (ins "b" 2 (ins "a" 1 (mk-empty strT nat)))]
        ;; the constructed map term type-checks to Map String Nat (proof carried)
        (is (some? (.inferType tc m)))
        ;; and runs
        (is (= 1   (eval (look "a" m))))
        (is (= 2   (eval (look "b" m))))
        (is (= nil (eval (look "z" m))))))
    (do (println "SKIP map-ops-run-string-keys: no Init env") (is true))))
