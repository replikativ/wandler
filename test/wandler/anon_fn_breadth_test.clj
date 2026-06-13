(ns wandler.anon-fn-breadth-test
  "General anonymous-fn breadth: the release-audit battery as a differential regression.
   Every case is ordinary Clojure compiled + kernel-certified through a/defn, value-checked
   against clojure.core on the same input. Covers: arithmetic composition · let (incl.
   shadowing) · if/cond/case in element fns · and/or (macroexpansion path) · closures over
   params · nested pipelines with capture · #() shorthand · pair first/second AND [[a b]]
   destructuring over Prod · comp/partial as fn values · quot/max/mod parity.
   Documented gap (clean rejection): when/keep — nil-punning as Option producer."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(def ^:private xs10 '(1 2 3 4 5 6 7 8 9 10))
(def ^:private prs '([1 10] [2 20] [3 30]))

(def ^:private cases
  ;; [name sig ret body truth args]
  [['af-arith '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (+ (* 2 x) 3)) xs) #(mapv (fn [x] (+ (* 2 x) 3)) %) [xs10]]
   ['af-let '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (let [y (* x x)] (+ y 1))) xs) #(mapv (fn [x] (let [y (* x x)] (+ y 1))) %) [xs10]]
   ['af-if '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (if (< x 5) (* 10 x) x)) xs) #(mapv (fn [x] (if (< x 5) (* 10 x) x)) %) [xs10]]
   ['af-cond '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (cond (< x 3) 0 (< x 7) 1 :else 2)) xs)
    #(mapv (fn [x] (cond (< x 3) 0 (< x 7) 1 :else 2)) %) [xs10]]
   ['af-case '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (case x 1 100 2 200 0)) xs) #(mapv (fn [x] (case x 1 100 2 200 0)) %) ['(1 2 3)]]
   ['af-and '[xs :- (List Nat)] '(List Nat)
    '(filterv (fn [x] (and (< 2 x) (< x 8))) xs) #(filterv (fn [x] (and (< 2 x) (< x 8))) %) [xs10]]
   ['af-or '[xs :- (List Nat)] '(List Nat)
    '(filterv (fn [x] (or (< x 3) (< 8 x))) xs) #(filterv (fn [x] (or (< x 3) (< 8 x))) %) [xs10]]
   ['af-shadow '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (let [x (+ x 1)] (* x 2))) xs) #(mapv (fn [x] (let [x (+ x 1)] (* x 2))) %) [xs10]]
   ['af-shorthand '[xs :- (List Nat)] '(List Nat)
    '(mapv #(* % %) xs) #(mapv (fn [x] (* x x)) %) [xs10]]
   ['af-closure '[k :- Nat, xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (+ x k)) xs) (fn [k xs] (mapv (fn [x] (+ x k)) xs)) [100 xs10]]
   ['af-nested-capture '[xs :- (List Nat)] 'Nat
    '(reduce + 0 (mapv (fn [x] (reduce + 0 (mapv (fn [y] (* x y)) xs))) xs))
    #(reduce + 0 (mapv (fn [x] (reduce + 0 (mapv (fn [y] (* x y)) %))) %)) ['(1 2 3)]]
   ['af-pair-fs '[ps :- (List (Prod Nat Nat))] '(List Nat)
    '(mapv (fn [p] (+ (first p) (second p))) ps) #(mapv (fn [p] (+ (first p) (second p))) %) [prs]]
   ['af-destructure '[ps :- (List (Prod Nat Nat))] '(List Nat)
    '(mapv (fn [[a b]] (+ a b)) ps) #(mapv (fn [[a b]] (+ a b)) %) [prs]]
   ['af-comp '[xs :- (List Nat)] '(List Nat)
    '(mapv (comp inc inc) xs) #(mapv (comp inc inc) %) [xs10]]
   ['af-partial '[xs :- (List Nat)] '(List Nat)
    '(mapv (partial + 3) xs) #(mapv (partial + 3) %) [xs10]]
   ['af-quot '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (quot x 2)) xs) #(mapv (fn [x] (quot x 2)) %) [xs10]]
   ['af-max '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (max x 5)) xs) #(mapv (fn [x] (max x 5)) %) [xs10]]])

(defn- cmp [got want]
  (if (or (sequential? got) (sequential? want)) (= (seq got) (seq want)) (= got want)))

(deftest anon-fn-breadth-differential
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (w/install!)
      (doseq [[n sig ret body truth args] cases]
        (binding [a/*verbose* false]
          (eval (list 'ansatz.core/defn n sig ret body)))
        (let [f @(resolve n)
              got (apply f args)
              want (apply truth args)]
          (is (cmp got want)
              (str n ": " (pr-str got) " ≠ clojure.core " (pr-str want))))))
    (println "anon-fn-breadth: no Init env, skipping")))
