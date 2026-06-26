(ns wandler.bridge.stratum
  "OPTIONAL stratum adapter for ansatz.bridge. PURE DATA transformation — maps stratum's COLUMNAR
   logical IR (LScan[columns length] / LFilter[predicates input] / LJoin[join-type on-pairs left
   right], from stratum.query.ir) to/from Ansatz KERNEL TERMS, with NO hard stratum dependency
   (:detect? probes; stratum executes the γ-lowered columnar/SIMD plan at runtime).

   Unlike datahike (rows of datoms), stratum is COLUMNAR with STRUCTURED predicates `[col op arg]`,
   so this adapter COMPILES those predicates into kernel lambdas — real α work. A row is modelled
   logically as a tuple; for the (demo) 2-column case that's `Prod Nat Nat` with column 0 = Prod.fst,
   column 1 = Prod.snd. The optimizer's relational laws (filter→join pushdown, semijoin,
   aggregation-through-join factorization) then apply uniformly, certified, and γ-lower back to
   stratum's PSIMDFilter / PSortedMerge physical ops."
  (:require [wandler.bridge :as bridge]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(def ^:private z lvl/zero)
(defn- nm [s] (name/from-string s))
(def ^:private nat (e/const' (nm "Nat") []))

(defn- lit [n] (e/app* (e/const' (nm "OfNat.ofNat") [z]) nat (e/lit-nat n)
                       (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat n))))

(defn- col-proj
  "Project column `idx` out of a (demo 2-column Prod) row bound at de Bruijn 0."
  [idx]
  (e/app* (e/const' (nm (if (zero? idx) "Prod.fst" "Prod.snd")) [z z]) nat nat (e/bvar 0)))

(defn- compile-pred1
  "One stratum normalized predicate `[col-idx op arg]` → a Bool body over the row at de Bruijn 0.
   op ∈ #{:< :> :<= :>= :=} on Nat columns (Nat.blt / Nat.ble / Nat.beq)."
  [[col op arg]]
  (let [c (col-proj col) a (lit arg)]
    (case op
      :>  (e/app* (e/const' (nm "Nat.blt") []) a c)        ; arg < c
      :<  (e/app* (e/const' (nm "Nat.blt") []) c a)        ; c < arg
      :>= (e/app* (e/const' (nm "Nat.ble") []) a c)
      :<= (e/app* (e/const' (nm "Nat.ble") []) c a)
      :=  (e/app* (e/const' (nm "Nat.beq") []) c a))))

(defn- and-preds
  "AND-combine stratum predicates into one `λrow. p1 ∧ p2 ∧ …` (Bool)."
  [preds row-type]
  (e/lam "r" row-type
         (reduce (fn [acc p] (e/app* (e/const' (nm "Bool.and") []) acc (compile-pred1 p)))
                 (compile-pred1 (first preds)) (rest preds))
         :default))

(defn- key-fn
  "Key function `λrow. col-proj idx` for an equi-join on a single column."
  [idx row-type]
  (e/lam "r" row-type (col-proj idx) :default))

;; ── α : stratum logical IR (data) → kernel term ──────────────────────────────
;;   {:op :scan :src <fvar> :row <Type>}
;;   {:op :filter :predicates [[col op arg]…] :in <q>}
;;   {:op :join :on [[lcol rcol]] :row <Type> :key-type <Type> :deceq <inst> :left <q> :right <q>}
(defn lift [{:keys [op] :as q} row-type]
  (case op
    :scan   (:src q)
    :filter (e/app* (e/const' (nm "List.filter") [z]) row-type
                    (and-preds (:predicates q) row-type) (lift (:in q) row-type))
    :join   (let [[[lcol rcol]] (:on q)]
              (e/app* (e/const' (nm "Map.join") [])
                      (:key-type q) (:row q) (:row q) (:deceq q)
                      (key-fn lcol (:row q)) (key-fn rcol (:row q))
                      (lift (:left q) (:row q)) (lift (:right q) (:row q))))))

;; ── γ : kernel plan → stratum logical IR (data) ──────────────────────────────
(defn lower [pl]
  (case (:op pl)
    :source {:op :scan :src (:term pl)}
    :filter {:op :simd-filter :pred (:pred pl) :in (lower (:input pl))}   ; → PSIMDFilter
    :map    {:op :project :fn (:fn pl) :in (lower (:input pl))}
    :join   {:op :sorted-merge :kf (:kf pl) :lf (:lf pl)                  ; → PSortedMerge
             :left (lower (:left pl)) :right (lower (:right pl))}
    {:op (:op pl) :raw pl}))

(defn stratum-present? []
  (boolean (try (require 'stratum.query.ir) true (catch Throwable _ false))))

(bridge/register-engine!
 :stratum
 {:detect? stratum-present?
  :lift    (fn [[q row-type]] (lift q row-type))
  :lower   lower})
