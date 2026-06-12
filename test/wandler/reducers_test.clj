(ns wandler.reducers-test
  (:require [wandler.reducers :as r]
            [ansatz.core :as ac]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

;; Shared, loaded-once Init envs. `init-medium` carries Nat/monoid laws; the full
;; `Init` carries the real `List.map_map`/`List.filter_filter` fusion theorems.
(def ^:private init-medium-env test-env/init-medium-env)
(def ^:private init-full-env test-env/init-full-env)

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "test-data/init-medium.ndjson not found" {}))))

(defn- add-test-law [kernel-env theorem type]
  (env/add-constant kernel-env
                    (env/mk-axiom (name/from-string theorem) [] type)))

(r/defpipeline odd-squares
  (map inc)
  (filter odd?)
  (map #(* % %)))

(deftest pipeline-compiles-to-transducer
  (let [pipeline (-> r/empty
                     (r/map inc)
                     (r/filter even?)
                     (r/flat-map (fn [x] [x (* 10 x)])))]
    (is (identical? (r/xform pipeline) (r/xform pipeline))
        "compiled xform is cached on the pipeline value")
    (is (= [2 20 4 40]
           (r/into [] pipeline [0 1 2 3])))
    (is (= 66
           (r/transduce pipeline + 0 [0 1 2 3])))
    (is (= [2 20 4 40]
           (vec (r/eduction pipeline [0 1 2 3]))))
    (is (= {:steps [{:op :map :fold-safe? true}
                    {:op :filter :fold-safe? true}
                    {:op :mapcat :fold-safe? true}]
            :optimized-steps [{:op :map :fold-safe? true}
                              {:op :filter :fold-safe? true}
                              {:op :mapcat :fold-safe? true}]
            :optimizations []
            :fold-safe? true}
           (r/explain pipeline)))))

(deftest optimizer-fuses-order-preserving-steps
  (let [pipeline (r/pipeline
                  (map inc)
                  (map #(* 2 %))
                  (filter even?)
                  (remove #(> % 6)))
        report (r/explain pipeline)]
    (is (= [2 4 6]
           (r/into [] pipeline [0 1 2 3 4 5])))
    (is (= [{:op :map :fold-safe? true}
            {:op :filter :fold-safe? true}]
           (:optimized-steps report)))
    (is (= [:map-map :remove->filter :filter-filter]
           (mapv :rule (:optimizations report))))
    (is (every? false? (mapv :kernel-checked? (:optimizations report))))))

(deftest optimizer-preserves-clojure-evaluation-order
  (let [events (atom [])
        pipeline (r/pipeline
                  (map #(do (swap! events conj [:f %])
                            (inc %)))
                  (map #(do (swap! events conj [:g %])
                            (* 2 %)))
                  (filter #(do (swap! events conj [:p %])
                               (pos? %)))
                  (filter #(do (swap! events conj [:q %])
                               (even? %))))]
    (is (= [2 4]
           (r/into [] pipeline [-1 0 1])))
    (is (= [[:f -1] [:g 0] [:p 0]
            [:f 0] [:g 1] [:p 2] [:q 2]
            [:f 1] [:g 2] [:p 4] [:q 4]]
           @events))))

(deftest reducer-law-spec-validates-kernel-theorem-type
  (let [law-type (e/sort' lvl/zero)
        kernel-env (add-test-law (env/empty-env) "Ansatz.Reducer.map_map" law-type)
        spec (r/reducer-law-spec {:rule :map-map
                                  :theorem "Ansatz.Reducer.map_map"
                                  :expected-type law-type})
        checked (r/validate-reducer-law-spec kernel-env spec)]
    (is (r/reducer-law-checked? checked))
    (is (= "Ansatz.Reducer.map_map"
           (get-in checked [:metadata :kernel :theorem])))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Reducer law type does not match"
         (r/validate-reducer-law-spec
          kernel-env
          (r/reducer-law-spec {:rule :map-map
                               :theorem "Ansatz.Reducer.map_map"
                               :expected-type (e/sort' (lvl/succ lvl/zero))}))))))

(deftest checked-pipeline-requires-checked-laws-and-functions
  (let [base-env (require-env)
        law-type (e/sort' lvl/zero)
        kernel-env (add-test-law base-env "Ansatz.Reducer.map_map" law-type)
        succ-ci (env/lookup kernel-env (name/from-string "Nat.succ"))
        unchecked-succ (r/certified-fn {:name 'Nat.succ
                                        :type (.type succ-ci)
                                        :runtime inc})
        checked-succ (r/validate-certified-fn kernel-env unchecked-succ)
        law (r/reducer-law-spec {:rule :map-map
                                 :theorem "Ansatz.Reducer.map_map"
                                 :expected-type law-type})
        checked-pipeline (r/check-pipeline kernel-env
                                           (r/pipeline
                                            (map checked-succ)
                                            (map checked-succ))
                                           [law])
        unchecked-pipeline (r/check-pipeline kernel-env
                                             (r/pipeline
                                              (map unchecked-succ)
                                              (map unchecked-succ))
                                             [law])
        checked-opt (first (:optimizations (r/explain checked-pipeline)))
        unchecked-opt (first (:optimizations (r/explain unchecked-pipeline)))]
    (is (= [3 4]
           (r/into [] checked-pipeline [1 2])))
    (is (true? (:rule-kernel-checked? checked-opt)))
    (is (true? (:functions-certified? checked-opt)))
    (is (true? (:kernel-checked? checked-opt)))
    (is (true? (:rule-kernel-checked? unchecked-opt)))
    (is (false? (:functions-certified? unchecked-opt)))
    (is (false? (:kernel-checked? unchecked-opt)))))

(deftest prove-pipeline-skips-uncertified-functions
  ;; Ordinary Clojure closures carry no kernel term, so no proof is emitted and
  ;; nothing is consulted in the kernel environment.
  (let [proved (r/prove-pipeline (env/empty-env)
                                 (r/pipeline (map inc) (map #(* 2 %))))]
    (is (= [] (r/reducer-proofs proved)))
    (is (= [] (:reducer-proofs (r/explain proved))))))

(deftest prove-pipeline-records-missing-law-without-throwing
  ;; A certified function whose law is absent from the environment must degrade
  ;; gracefully: the fusion is recorded as not kernel-checked, with an error,
  ;; rather than throwing.
  (let [succ (r/certified-fn {:name 'Nat.succ :runtime inc})
        proved (r/prove-pipeline (env/empty-env)
                                 (r/pipeline (map succ) (map succ)))
        [proof] (r/reducer-proofs proved)]
    (is (= 1 (count (r/reducer-proofs proved))))
    (is (= :map-fusion (:rule proof)))
    (is (false? (:kernel-checked? proof)))
    (is (string? (:error proof)))))

(deftest prove-pipeline-only-proves-across-adjacent-certified-steps
  ;; An uncertified step in the middle prevents fusing the certified maps around
  ;; it, so no proof can be emitted.
  (let [succ (r/certified-fn {:name 'Nat.succ :runtime inc})
        proved (r/prove-pipeline (env/empty-env)
                                 (r/pipeline (map succ) (map inc) (map succ)))]
    (is (= [] (r/reducer-proofs proved)))))

(deftest prove-pipeline-emits-kernel-checked-fusion-proofs
  ;; Integration: against the real Lean `Init` library the optimizer emits
  ;; actual proof terms (`List.map_map`, `List.filter_filter`) and the kernel
  ;; type-checks them.  No Mathlib is involved.  Skips when init.ndjson is absent.
  (if-let [kenv @init-full-env]
    (let [succ (r/certified-fn {:name 'Nat.succ :runtime inc})
          all (r/certified-fn {:kernel-term (e/lam "n"
                                                   (e/const' (name/from-string "Nat") [])
                                                   (e/const' (name/from-string "Bool.true") [])
                                                   :default)
                               :name 'all-true
                               :runtime (constantly true)})
          ;; map run fusion proof
          map-proved (r/prove-pipeline kenv (r/pipeline (map succ) (map succ)))
          [map-proof] (r/reducer-proofs map-proved)
          ;; filter run fusion proof
          filter-proved (r/prove-pipeline kenv (r/pipeline (filter all) (filter all)))
          [filter-proof] (r/reducer-proofs filter-proved)
          ;; chained maps: ONE end-to-end proof for the whole run
          chain-proved (r/prove-pipeline kenv (r/pipeline (map succ) (map succ) (map succ)))
          [chain-proof] (r/reducer-proofs chain-proved)
          ;; mixed pipeline: one proof per maximal run
          mixed-proved (r/prove-pipeline kenv (r/pipeline (map succ) (map succ)
                                                          (filter all) (filter all)))]
      (is (= :map-fusion (:rule map-proof)))
      (is (= "List.map_map" (:theorem map-proof)))
      (is (= 2 (:steps map-proof)))
      (is (true? (:kernel-checked? map-proof)))
      (is (re-find #"List\.map_map|Function\.comp"
                   (e/->string (:theorem-type map-proof))))
      (is (= :filter-fusion (:rule filter-proof)))
      (is (= "List.filter_filter" (:theorem filter-proof)))
      (is (true? (:kernel-checked? filter-proof)))
      ;; one proof certifying the entire 3-map run
      (is (= 1 (count (r/reducer-proofs chain-proved))))
      (is (= 3 (:steps chain-proof)))
      (is (true? (:kernel-checked? chain-proof)))
      ;; one proof per run (map run + filter run)
      (is (= [:map-fusion :filter-fusion]
             (mapv :rule (r/reducer-proofs mixed-proved))))
      (is (every? :kernel-checked? (r/reducer-proofs mixed-proved)))
      ;; The runtime transducer is unchanged by proof emission.
      (is (= [3 4 5] (r/into [] map-proved [1 2 3]))))
    (do
      (println "SKIP prove-pipeline-emits-kernel-checked-fusion-proofs: test-data/init.ndjson absent")
      (is true))))

(deftest prove-pipeline-auto-certifies-ansatz-defn
  ;; Integration: a function defined with `ansatz.core/defn` (idiomatic `+`,
  ;; `:-` types) tags itself with its kernel constant, so it can be used in a
  ;; pipeline directly — no `certified-fn` wrapper — and still proves end-to-end.
  (if-let [kenv @init-full-env]
    (let [saved @ac/ansatz-env]
      (try
        (reset! ac/ansatz-env kenv)
        (let [triple (ac/define-verified 'rt-triple '[n :- Nat] 'Nat '(+ n (+ n n)))]
          ;; self-certified purely from a/defn metadata
          (is (= 'rt-triple (:name (r/certification triple))))
          (let [proved (r/prove-pipeline @ac/ansatz-env
                                         (r/pipeline (map triple) (map triple)))
                [proof] (r/reducer-proofs proved)]
            (is (= :map-fusion (:rule proof)))
            (is (true? (:kernel-checked? proof)))
            ;; triple twice = ×9
            (is (= [9 18 27] (r/into [] proved [1 2 3])))))
        (finally (reset! ac/ansatz-env saved))))
    (do
      (println "SKIP prove-pipeline-auto-certifies-ansatz-defn: test-data/init.ndjson absent")
      (is true))))

(deftest compose-preserves-left-to-right-order
  (let [pipeline (r/compose (r/map inc)
                            (r/filter odd?)
                            (r/map #(* % %)))]
    (is (= [1 9 25]
           (r/into [] pipeline [0 1 2 3 4])))))

(deftest pipeline-macro-accepts-clojure-transducer-shape
  (let [pipeline (r/pipeline
                  (map inc)
                  (filter odd?)
                  (mapcat (fn [x] [x (- x)])))]
    (is (= [1 -1 3 -3 5 -5]
           (r/into [] pipeline [0 1 2 3 4]))))
  (is (= [1 9 25]
         (r/into [] odd-squares [0 1 2 3 4]))))

(deftest lawful-fold-map-matches-sequential-transduce
  (let [xs (vec (range 1000))
        pipeline (-> r/empty
                     (r/map inc)
                     (r/filter #(not (zero? (mod % 3)))))
        value-f #(* % %)
        expected (r/transduce pipeline
                              (fn
                                ([] 0)
                                ([x] x)
                                ([acc x] (+ acc (value-f x))))
                              xs)]
    (doseq [grain [1 2 17 512]]
      (is (= expected
             (r/fold-map pipeline r/nat-add value-f xs {:grain grain}))
          (str "grain=" grain)))))

(deftest convenience-terminals-map-to-lawful-folds
  (let [xs (vec (range 10))
        pipeline (r/pipeline (map inc) (filter odd?))]
    (is (= 25
           (r/sum pipeline r/nat-add xs {:grain 2})))
    (is (= 25
           (r/sum-seq pipeline r/nat-add xs)))
    (is (= 55
           (r/sum-by r/empty r/nat-add inc xs {:grain 2})))
    (is (= 55
           (r/sum-by-seq r/empty r/nat-add inc xs)))
    (is (= {0 5, 1 5}
           (r/frequencies r/empty r/nat-add #(mod % 2) xs {:grain 2})))
    (is (= {0 5, 1 5}
           (r/frequencies-seq r/empty r/nat-add #(mod % 2) xs)))))

(deftest group-by-uses-value-monoid
  (let [xs (vec (range 1 31))
        pipeline (r/filter #(<= % 20))
        actual (r/group-by pipeline r/nat-add #(mod % 4) (constantly 1) xs {:grain 3})]
    (is (= {0 5, 1 5, 2 5, 3 5} actual))))

(deftest unsafe-monoid-is-rejected-by-lawful-fold
  (let [bad-spec (r/monoid-spec
                  {:name :bad/add
                   :unit-fn (constantly 0)
                   :combine +
                   :laws {:assoc 'Nat.add_assoc}})]
    (is (false? (r/lawful? bad-spec)))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Parallel fold requires a lawful MonoidSpec"
         (r/fold-map r/empty bad-spec identity [1 2 3])))
    (is (= 6
           (r/unchecked-fold-map r/empty (constantly 0) + identity [1 2 3]
                                 {:grain 1})))))

(deftest kernel-validates-monoid-law-certificates
  (let [env (require-env)
        checked (r/checked env r/nat-add)]
    (is (r/lawful? checked))
    (is (r/kernel-lawful? checked))
    (is (= 10
           (r/fold-map-checked r/empty checked identity [1 2 3 4]
                               {:grain 1})))
    (is (= 10
           (r/sum-checked r/empty checked [1 2 3 4]
                          {:grain 1})))
    (is (= 10
           (r/sum-seq-checked r/empty checked [1 2 3 4])))
    (is (= {0 2, 1 2}
           (r/group-by-checked r/empty checked #(mod % 2) (constantly 1)
                               [1 2 3 4]
                               {:grain 1})))
    (is (= {0 2, 1 2}
           (r/group-by-seq-checked r/empty checked #(mod % 2) (constantly 1)
                                   [1 2 3 4])))
    (is (= {0 2, 1 2}
           (r/frequencies-checked r/empty checked #(mod % 2)
                                  [1 2 3 4]
                                  {:grain 1})))
    (is (= {0 2, 1 2}
           (r/frequencies-seq-checked r/empty checked #(mod % 2)
                                      [1 2 3 4])))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Kernel-checked fold requires validate-monoid-spec"
         (r/fold-map-checked r/empty r/nat-add identity [1 2 3])))))

(deftest kernel-validation-rejects-mismatched-law-type
  (let [env (require-env)
        bad-spec (r/monoid-spec
                  {:name :bad/nat-add
                   :unit-fn (:unit-fn r/nat-add)
                   :combine (:combine r/nat-add)
                   :laws (assoc (:laws r/nat-add)
                                :right-identity 'Nat.zero_add)
                   :metadata (:metadata r/nat-add)})]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Kernel law type does not match MonoidSpec"
         (r/validate-monoid-spec env bad-spec)))))
