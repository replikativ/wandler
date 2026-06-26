(ns wandler.transducer-breadth-test
  "Transducer-surface BREADTH: the idiomatic-vocabulary battery from the public-release
   audit, kept as a differential regression. Every case is (1) an ordinary Clojure
   transducer spelling, (2) compiled + kernel-certified through a/defn, and (3) checked
   against clojure.core ground truth on the same input — so a desugaring or lowering
   regression shows up as a VALUE difference, not just a proof failure.

   Covers: into/transduce/sequence/eduction · map/filter/remove/mapcat/map-indexed/
   take/drop/take-while/dedupe/distinct/interpose · nested comp + comp ORDER semantics ·
   set-literal predicates · even? parity · vector literals in fn bodies.
   Documented gaps (clean rejections, not regressions): keep (Option-producing fns),
   partition-all (List.chunk surface verb), let-bound xforms (binding-time inlining)."
  (:require [ansatz.core :as a]
            [wandler.core :as w]                    ; full surface + lowering registry, as a user gets it
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(def ^:private xs10 '(1 2 3 4 5 6 7 8 9 10))
(def ^:private dup '(1 1 2 2 3 1 1 4))

(def ^:private cases
  ;; [name body-form ground-truth-fn input]
  [['tb-into-map '(into [] (map (fn [x] (* x x))) xs)
    #(into [] (map (fn [x] (* x x))) %) xs10]
   ['tb-comp-mf '(into [] (comp (map (fn [x] (* x x))) (filter (fn [x] (< 10 x)))) xs)
    #(into [] (comp (map (fn [x] (* x x))) (filter (fn [x] (< 10 x)))) %) xs10]
   ;; comp ORDER: filter sees raw elements, map sees survivors (left-to-right)
   ['tb-comp-fm '(into [] (comp (filter (fn [x] (< 3 x))) (map (fn [x] (+ x 1)))) xs)
    #(into [] (comp (filter (fn [x] (< 3 x))) (map (fn [x] (+ x 1)))) %) xs10]
   ['tb-transduce '(transduce (comp (filter (fn [x] (< 2 x))) (map (fn [x] (* x x)))) + 0 xs)
    #(transduce (comp (filter (fn [x] (< 2 x))) (map (fn [x] (* x x)))) + 0 %) xs10]
   ['tb-transduce-init '(transduce (map (fn [x] (* 2 x))) + 100 xs)
    #(transduce (map (fn [x] (* 2 x))) + 100 %) xs10]
   ['tb-sequence '(sequence (comp (map (fn [x] (+ x 1))) (filter (fn [x] (< 4 x)))) xs)
    #(doall (sequence (comp (map (fn [x] (+ x 1))) (filter (fn [x] (< 4 x)))) %)) xs10]
   ['tb-take '(into [] (comp (map (fn [x] (* x x))) (take 3)) xs)
    #(into [] (comp (map (fn [x] (* x x))) (take 3)) %) xs10]
   ['tb-drop '(into [] (comp (drop 2) (map (fn [x] (+ x 1)))) xs)
    #(into [] (comp (drop 2) (map (fn [x] (+ x 1)))) %) xs10]
   ['tb-take-while '(into [] (take-while (fn [x] (< x 5))) xs)
    #(into [] (take-while (fn [x] (< x 5))) %) xs10]
   ['tb-remove '(into [] (remove (fn [x] (< x 5))) xs)
    #(into [] (remove (fn [x] (< x 5))) %) xs10]
   ;; vector literal in the fn body ([x x] = List literal)
   ['tb-mapcat '(into [] (mapcat (fn [x] [x x])) xs)
    #(into [] (mapcat (fn [x] [x x])) %) '(1 2 3)]
   ['tb-dedupe '(into [] (dedupe) xs)
    #(into [] (dedupe) %) dup]
   ['tb-distinct '(into [] (distinct) xs)
    #(into [] (distinct) %) dup]
   ['tb-map-indexed '(into [] (map-indexed (fn [i x] (+ i x))) xs)
    #(into [] (map-indexed (fn [i x] (+ i x))) %) xs10]
   ['tb-interpose '(into [] (interpose 0) xs)
    #(into [] (interpose 0) %) '(1 2 3)]
   ['tb-nested-comp '(into [] (comp (comp (map (fn [x] (* x x))) (filter (fn [x] (< 5 x)))) (map (fn [x] (+ x 1)))) xs)
    #(into [] (comp (comp (map (fn [x] (* x x))) (filter (fn [x] (< 5 x)))) (map (fn [x] (+ x 1)))) %) xs10]
   ['tb-eduction '(reduce + 0 (eduction (map (fn [x] (* x x))) xs))
    #(reduce + 0 (eduction (map (fn [x] (* x x))) %)) xs10]
   ['tb-filter-set '(into [] (filter #{2 4 6}) xs)
    #(into [] (filter #{2 4 6}) %) xs10]
   ['tb-even '(into [] (filter even?) xs)
    #(into [] (filter even?) %) xs10]
   ;; standalone `remove` VERB (not inside a transducer stack): (remove p coll) ≡ filter (complement p).
   ;; inline predicate (body negated in place), named predicate verb (eta-expanded), and a fused
   ;; map+remove+sum (the optimizer collapses map∘remove to a single filterMap, then sums).
   ['tb-remove-verb '(remove (fn [x] (< x 5)) xs)
    #(remove (fn [x] (< x 5)) %) xs10]
   ['tb-remove-even '(remove even? xs)
    #(remove even? %) xs10]
   ['tb-remove-fused '(reduce + 0 (remove even? (map (fn [x] (* x x)) xs)))
    #(reduce + 0 (remove even? (map (fn [x] (* x x)) %))) xs10]
   ;; drop-last (List.dropLast — drops the final element)
   ['tb-drop-last '(drop-last xs) #(drop-last %) xs10]
   ['tb-drop-last-fused '(reduce + 0 (drop-last xs)) #(reduce + 0 (drop-last %)) xs10]
   ;; reduce with a bare non-+ binary verb (eta-expanded) + apply over a monoid
   ['tb-reduce-max '(reduce max 0 xs) #(reduce max 0 %) xs10]
   ['tb-reduce-min '(reduce min 999 xs) #(reduce min 999 %) xs10]
   ['tb-apply-max '(apply max xs) #(apply max %) xs10]
   ['tb-apply-plus '(apply + xs) #(apply + %) xs10]
   ['tb-apply-times '(apply * (take 4 xs)) #(apply * (take 4 %)) xs10]
   ;; for comprehensions (intercepted before Clojure's `for` macro; → map/mapcat/filter/let)
   ['tb-for '(for [x xs] (* x x)) #(vec (for [x %] (* x x))) xs10]
   ['tb-for-when '(for [x xs :when (< 5 x)] x) #(vec (for [x % :when (< 5 x)] x)) xs10]
   ['tb-for-let '(for [x xs :let [y (* x 2)]] (+ x y)) #(vec (for [x % :let [y (* x 2)]] (+ x y))) xs10]
   ['tb-for-cartesian '(reduce + 0 (for [x xs y xs] (* x y)))
    #(reduce + 0 (for [x % y %] (* x y))) '(1 2 3 4)]
   ['tb-for-when-sum '(reduce + 0 (for [x xs :when (odd? x)] x))
    #(reduce + 0 (for [x % :when (odd? x)] x)) xs10]
   ;; partition-all / partition (inlined verified foldl chunk; partition DROPS the short tail) + take-nth
   ['tb-partition-all '(partition-all 3 xs) #(partition-all 3 %) xs10]
   ['tb-partition '(partition 3 xs) #(partition 3 %) xs10]
   ['tb-partition-count '(count (partition 3 xs)) #(count (partition 3 %)) xs10]
   ['tb-take-nth '(take-nth 2 xs) #(take-nth 2 %) xs10]
   ['tb-take-nth-sum '(reduce + 0 (take-nth 3 xs)) #(reduce + 0 (take-nth 3 %)) xs10]
   ;; TUMBLING-WINDOW analytics: per-window aggregation over partition-all (map∘map fusion leaves
   ;; reverse/Nat.max point-free — exercises the eta-saturating codegen lowerings).
   ['tb-win-sum '(map (fn [w] (reduce + 0 w)) (partition-all 3 xs))
    #(mapv (fn [w] (reduce + 0 w)) (partition-all 3 %)) xs10]
   ['tb-win-max '(map (fn [w] (reduce max 0 w)) (partition-all 3 xs))
    #(mapv (fn [w] (reduce max 0 w)) (partition-all 3 %)) xs10]
   ['tb-peak-load '(reduce max 0 (map (fn [w] (reduce + 0 w)) (partition-all 3 xs)))
    #(reduce max 0 (map (fn [w] (reduce + 0 w)) (partition-all 3 %))) xs10]
   ;; downsample (take-nth) → window → per-window sum → peak (4-stage stream pipeline)
   ['tb-downsample-peak '(reduce max 0 (map (fn [w] (reduce + 0 w)) (partition-all 2 (take-nth 2 xs))))
    #(reduce max 0 (map (fn [w] (reduce + 0 w)) (partition-all 2 (take-nth 2 %)))) xs10]])

(defn- cmp [got want]
  (if (or (sequential? got) (sequential? want))
    (= (seq got) (seq want))
    (= got want)))

(deftest transducer-breadth-differential
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (w/install!)
      (doseq [[n body truth input] cases]
        (let [ret (cond
                    (#{'tb-transduce 'tb-transduce-init 'tb-eduction 'tb-remove-fused
                       'tb-drop-last-fused 'tb-reduce-max 'tb-reduce-min 'tb-apply-max
                       'tb-apply-plus 'tb-apply-times 'tb-for-cartesian 'tb-for-when-sum
                       'tb-partition-count 'tb-take-nth-sum 'tb-peak-load 'tb-downsample-peak} n) 'Nat
                    (#{'tb-partition-all 'tb-partition} n) '(List (List Nat))
                    :else '(List Nat))]
          (binding [a/*verbose* false]
            (eval (list 'ansatz.core/defn n '[xs :- (List Nat)] ret body)))
          (let [f @(resolve n)
                got (f input)
                want (truth input)]
            (is (cmp got want)
                (str n ": " (pr-str got) " ≠ clojure.core " (pr-str want)))))))
    (println "transducer-breadth: no Init env, skipping")))
