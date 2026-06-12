(ns wandler.inference.wmc.logicng
  "OPTIONAL LogicNG WMC backend (pure-JVM knowledge compilation). Loading this ns requires LogicNG on the
   classpath (the :logicng alias) — wandler.inference.wmc/load-backends! requires it inside a try, so a classpath
   without LogicNG simply skips it (Ansatz stays standalone). Registers a `:logicng` backend that compiles
   the provenance DNF to a BDD and computes WMC by a weighted Shannon-expansion DP over the BDD:

       wmc(node) = p(var)·wmc(high) + (1−p(var))·wmc(low) ;  leaf $true ↦ 1, $false ↦ 0

   Skipped variables (BDD reduction) contribute factor 1 because per-fact weights normalize (p + (1−p) = 1).
   This is EXACT — it accounts for shared variables (correlation), unlike the naïve product. The BDD is linear
   to count once built, so this scales past the 2^n enumeration reference. See ansatz.wmc."
  (:require [wandler.inference.wmc :as wmc])
  (:import [org.logicng.formulas FormulaFactory Formula]
           [org.logicng.knowledgecompilation.bdds BDDFactory BDD]
           [org.logicng.knowledgecompilation.bdds.datastructures BDDNode]))

(defn logicng-wmc
  "Exact WMC of a provenance DNF via a LogicNG BDD + weighted DP."
  [probs dnf]
  (let [fs (vec (distinct (mapcat seq dnf)))]
    (cond
      (empty? dnf)            0.0                       ; ⋁ of nothing = false
      (some empty? dnf)       1.0                       ; a tautological (empty) conjunction
      :else
      (let [f (FormulaFactory.)
            names (zipmap fs (map #(str "v" %) (range)))
            var-of (into {} (map (fn [fc] [fc (.variable f (names fc))])) fs)
            name->p (into {} (map (fn [fc] [(names fc) (double (probs fc))])) fs)
            and* (fn [xs] (.and f (into-array Formula xs)))
            or*  (fn [xs] (.or  f (into-array Formula xs)))
            formula (or* (map (fn [conj] (and* (map var-of conj))) dnf))
            bdd  (BDDFactory/build ^Formula formula)
            root (.toLngBdd ^BDD bdd)
            memo (java.util.IdentityHashMap.)
            walk (fn walk [^BDDNode n]
                   (if (.isInnerNode n)
                     (if-let [v (.get memo n)] v
                       (let [p (double (name->p (str (.label n))))
                             v (+ (* p (walk (.high n))) (* (- 1.0 p) (walk (.low n))))]
                         (.put memo n v) v))
                     (if (= "$true" (str (.label n))) 1.0 0.0)))]
        (walk root)))))

(wmc/register-backend! :logicng {:detect? (constantly true) :wmc logicng-wmc})
