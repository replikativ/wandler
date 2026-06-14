(ns wandler.fusion-test
  "FUSION REGRESSION — the transducer/relational surface must DEFOREST multi-stage pipelines to a single
   pass, not merely compute the right value. The breadth corpus (transducer_breadth_test) checks values;
   this locks in that the certified optimizer actually FUSES. Each case is (1) ordinary Clojure through
   a/defn, (2) checked against clojure.core ground truth (value), AND (3) asserted to collapse to the
   expected minimal pass count via w/explain (so a fusion-law or codegen regression shows up here).

   Covers the deforestation algebra: map_map · filter_filter · map/filter→filterMap chains · the flatMap
   (mapcat) laws map_flatMap/flatMap_map/foldl_flatMap · foldl over map/filter · and the same over named
   def-record field projections (the malli-record surface). `mapcat∘filter` is the documented non-fusing
   case (pushing filter into a literal-list flatMap body unfolds List.filter's match auxiliary)."
  (:require [ansatz.core :as a]
            [wandler.core :as w]
            [wandler.surface.records :as wrec]
            [wandler.test-env :as test-env]
            [clojure.test :refer [deftest is]]))

(def ^:private xs '(1 2 3 4 5 6 7 8 9 10))

;; [name params ret body ground-truth-fn input expected-passes-after]
(def ^:private cases
  [['fz-mm '[xs :- (List Nat)] '(List Nat)
    '(into [] (comp (map (fn [x] (+ x 1))) (map (fn [x] (* x x)))) xs)
    #(into [] (comp (map (fn [x] (+ x 1))) (map (fn [x] (* x x)))) %) xs 1]
   ['fz-ff '[xs :- (List Nat)] '(List Nat)
    '(into [] (comp (filter (fn [x] (< 2 x))) (filter (fn [x] (< x 9)))) xs)
    #(into [] (comp (filter (fn [x] (< 2 x))) (filter (fn [x] (< x 9)))) %) xs 1]
   ['fz-mfm '[xs :- (List Nat)] '(List Nat)
    '(into [] (comp (map (fn [x] (+ x 1))) (filter (fn [x] (< 3 x))) (map (fn [x] (* x 2)))) xs)
    #(into [] (comp (map (fn [x] (+ x 1))) (filter (fn [x] (< 3 x))) (map (fn [x] (* x 2)))) %) xs 1]
   ['fz-four '[xs :- (List Nat)] '(List Nat)
    '(into [] (comp (map (fn [x] (+ x 1))) (filter (fn [x] (< 3 x))) (map (fn [x] (* x 2))) (filter (fn [x] (< x 20)))) xs)
    #(into [] (comp (map (fn [x] (+ x 1))) (filter (fn [x] (< 3 x))) (map (fn [x] (* x 2))) (filter (fn [x] (< x 20)))) %) xs 1]
   ['fz-mapcat-map '[xs :- (List Nat)] '(List Nat)
    '(into [] (comp (mapcat (fn [x] [x x])) (map (fn [y] (+ y 1)))) xs)
    #(into [] (comp (mapcat (fn [x] [x x])) (map (fn [y] (+ y 1)))) %) xs 1]
   ['fz-map-mapcat '[xs :- (List Nat)] '(List Nat)
    '(into [] (comp (map (fn [x] (+ x 1))) (mapcat (fn [x] [x x]))) xs)
    #(into [] (comp (map (fn [x] (+ x 1))) (mapcat (fn [x] [x x]))) %) xs 1]
   ['fz-reduce-mapcat '[xs :- (List Nat)] 'Nat
    '(reduce + 0 (mapcat (fn [x] [x x]) xs))
    #(reduce + 0 (mapcat (fn [x] [x x]) %)) xs 1]
   ['fz-transduce '[xs :- (List Nat)] 'Nat
    '(transduce (comp (filter (fn [x] (< 2 x))) (map (fn [x] (* x x)))) + 0 xs)
    #(transduce (comp (filter (fn [x] (< 2 x))) (map (fn [x] (* x x)))) + 0 %) xs 1]
   ['fz-mapv '[xs :- (List Nat)] '(List Nat)
    '(mapv (fn [x] (* x x)) (filterv (fn [x] (< 2 x)) xs))
    #(mapv (fn [x] (* x x)) (filterv (fn [x] (< 2 x)) %)) xs 1]])

;; record (malli def-record) pipelines — field projections must fuse like any other map/filter
(def ^:private ORD [{:cid 1 :amount 50 :tier 2} {:cid 2 :amount 70 :tier 1} {:cid 1 :amount 30 :tier 2}])
(def ^:private rec-cases
  [['fz-rec-mr '[os :- (List Order)] 'Nat
    '(reduce + 0 (map (fn [o] (:amount o)) os))
    #(reduce + 0 (map :amount %)) ORD 1]
   ['fz-rec-fmr '[os :- (List Order)] 'Nat
    '(reduce + 0 (map (fn [o] (:amount o)) (filter (fn [o] (< 40 (:amount o))) os)))
    #(reduce + 0 (map :amount (filter (fn [o] (< 40 (:amount o))) %))) ORD 1]
   ;; realistic 4-stage: enrich (assoc) → keep premium → project → sum, all over malli records → ONE pass
   ['fz-rec-enrich '[os :- (List Order)] 'Nat
    '(reduce + 0 (map (fn [o] (:amount o))
                   (filter (fn [o] (< 1 (:tier o)))
                     (map (fn [o] (assoc o :amount (+ 10 (:amount o)))) os))))
    #(reduce + 0 (map :amount (filter (fn [o] (< 1 (:tier o)))
                                (map (fn [o] (assoc o :amount (+ 10 (:amount o)))) %)))) ORD 1]])

(defn- cmp [got want] (if (or (sequential? got) (sequential? want)) (= (seq got) (seq want)) (= got want)))

(defn- run-case [n params ret body truth input max-pa]
  (binding [a/*verbose* false] (eval (list 'ansatz.core/defn n params ret body)))
  (let [ex (w/explain n) got ((deref (resolve n)) input) want (truth input)]
    (is (cmp got want) (str n " value: " (pr-str got) " ≠ clojure.core " (pr-str want)))
    (is (:verified? ex) (str n " optimizer rewrite not kernel-certified"))
    (is (and (:passes-after ex) (<= (long (:passes-after ex)) (long max-pa)))
        (str n " did not fuse: passes " (:passes-before ex) "→" (:passes-after ex) " (want ≤" max-pa ")"))))

(deftest transducer-pipelines-fuse-to-one-pass
  (if-let [kenv @test-env/init-full-env]
    (do (reset! a/ansatz-env kenv) (w/install!)
        (doseq [[n params ret body truth input max-pa] cases]
          (run-case n params ret body truth input max-pa)))
    (is true "skipped — no Init env")))

(deftest record-field-pipelines-fuse
  (if-let [kenv @test-env/init-full-env]
    (do (reset! a/ansatz-env kenv) (w/install!)
        (wrec/def-record Order [:map [:cid [:and :int [:>= 0]]] [:amount [:and :int [:>= 0]]] [:tier [:and :int [:>= 0]]]])
        (doseq [[n params ret body truth input max-pa] rec-cases]
          (run-case n params ret body truth input max-pa)))
    (is true "skipped — no Init env")))
