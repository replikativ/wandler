(ns wandler.records-test
  "Standard Clojure record ops (assoc / keyword access) compile and kernel-verify
   inside verified functions. Gated on an Init env (structures need Prod/Eq)."
  (:require [ansatz.core :as a]
            [wandler.surface.records :as rec]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]])
  (:import [ansatz.kernel TypeChecker]))

(defn- verified? [type-name]
  (when-let [ci (env/lookup (a/env) (name/from-string type-name))]
    (let [tc (doto (TypeChecker. (a/env)) (.setFuel 50000000))]
      (.isDefEq tc (.inferType tc (.value ci)) (.type ci)))))

(deftest def-record-lifts-malli-schema
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestAcct
                 [:map [:owner :string]
                  [:balance [:and :int [:>= 0]]]
                  [:bonus [:and :int [:>= 0]]]])))
      (let [sreg (-> (requiring-resolve 'ansatz.core/structure-registry) deref deref)]
        ;; the Malli :map became an Ansatz structure with the schema's field order
        (is (= ["owner" "balance" "bonus"] (:fields (get sreg "RecTestAcct"))))))
    (do (println "SKIP def-record-lifts-malli-schema: no Init env") (is true))))

(deftest assoc-and-get-compile-and-verify
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestAcct2
                 [:map [:owner :string]
                  [:balance [:and :int [:>= 0]]]
                  [:bonus [:and :int [:>= 0]]]]))
        ;; idiomatic Clojure: standard assoc (NOT nat-assoc) and keyword access
        (eval '(ansatz.core/defn rec-set-bonus [a :- RecTestAcct2] RecTestAcct2
                 (assoc a :bonus 100)))
        (eval '(ansatz.core/defn rec-get-bal [a :- RecTestAcct2] Nat
                 (:balance a))))
      ;; the elaborated structure rebuild kernel-verifies
      (is (true? (verified? "rec-set-bonus")))
      (is (true? (verified? "rec-get-bal")))
      ;; assoc rebuilds via the constructor, touching the right field
      (let [body (e/->string (.value (env/lookup (a/env) (name/from-string "rec-set-bonus"))))]
        (is (re-find #"RecTestAcct2\.mk" body))
        (is (re-find #"100" body))))
    (do (println "SKIP assoc-and-get-compile-and-verify: no Init env") (is true))))

(deftest update-maps-field-through-fn
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestAcctU
                 [:map [:owner :string] [:balance [:and :int [:>= 0]]]]))
        ;; idiomatic (update r :k f): rebuild with the field mapped through f
        (eval '(ansatz.core/defn rec-bump [a :- RecTestAcctU] RecTestAcctU
                 (update a :balance Nat.succ))))
      (is (true? (verified? "rec-bump")))
      (let [body (e/->string (.value (env/lookup (a/env) (name/from-string "rec-bump"))))]
        ;; field 1 (balance) goes through Nat.succ of its own projection; field 0 copied
        (is (re-find #"Nat\.succ" body))
        (is (re-find #"RecTestAcctU\.mk" body))))
    (do (println "SKIP update-maps-field-through-fn: no Init env") (is true))))

(deftest threaded-pipeline-fuses-with-overwrite-elimination
  ;; The marquee case: an idiomatic threaded chain of standard record ops fuses to
  ;; ONE rebuild at compile time, and a write that is later overwritten is dropped
  ;; from the verified term — overwrite elimination, kernel-checked.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestRow
                 [:map [:a [:and :int [:>= 0]]] [:b [:and :int [:>= 0]]] [:c [:and :int [:>= 0]]]]))
        (eval '(ansatz.core/defn rec-pipe [r :- RecTestRow] RecTestRow
                 (-> r (assoc :a 1) (assoc :b 2) (update :c Nat.succ) (assoc :a 9)))))
      (is (true? (verified? "rec-pipe")))
      (let [body (e/->string (.value (env/lookup (a/env) (name/from-string "rec-pipe"))))]
        ;; one fused rebuild, the live :a write (9) survives, the dead one (1) is gone
        (is (= 1 (count (re-seq #"RecTestRow\.mk" body))))
        (is (re-find #"\b9\b" body))
        (is (re-find #"Nat\.succ" body))
        (is (not (re-find #"\b1\b" body)))))     ; dead `assoc :a 1` eliminated
    (do (println "SKIP threaded-pipeline-fuses-with-overwrite-elimination: no Init env")
        (is true))))

(deftest nested-get-assoc-update-in-verify
  ;; Nested records (a structure-typed field) with get-in/assoc-in/update-in,
  ;; built as direct kernel proj/rebuild terms and kernel-checked.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(ansatz.core/structure RecTestAddr [] (zip Nat) (num Nat)))
        (eval '(ansatz.core/structure RecTestCust [] (id Nat) (addr RecTestAddr)))
        (eval '(ansatz.core/defn rec-gz [c :- RecTestCust] Nat (get-in c [:addr :zip])))
        (eval '(ansatz.core/defn rec-az [c :- RecTestCust] RecTestCust (assoc-in c [:addr :zip] 5)))
        (eval '(ansatz.core/defn rec-uz [c :- RecTestCust] RecTestCust (update-in c [:addr :zip] Nat.succ))))
      (is (true? (verified? "rec-gz")))
      (is (true? (verified? "rec-az")))
      (is (true? (verified? "rec-uz")))
      ;; assoc-in rebuilds the OUTER record with the inner one rebuilt; sibling
      ;; fields (id, num) are copied through, only :addr/:zip changes
      (let [body (e/->string (.value (env/lookup (a/env) (name/from-string "rec-az"))))]
        (is (re-find #"RecTestCust\.mk" body))
        (is (re-find #"RecTestAddr\.mk" body))
        (is (re-find #"\b5\b" body))))
    (do (println "SKIP nested-get-assoc-update-in-verify: no Init env") (is true))))

(deftest select-keys-synthesizes-projection-record
  ;; (select-keys r ks) projects to a NEW auto-registered record `<T>__ks`. The
  ;; result type is synthesized (unnameable), so the function uses `_` return type
  ;; (inferred from the body). Column projection, kernel-checked.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestWide
                 [:map [:a [:and :int [:>= 0]]] [:b [:and :int [:>= 0]]] [:c [:and :int [:>= 0]]]]))
        (eval '(ansatz.core/defn rec-pick [r :- RecTestWide] _ (select-keys r [:a :c]))))
      (is (true? (verified? "rec-pick")))
      ;; the projection record was synthesized + registered with just the kept fields
      (let [sreg (-> (requiring-resolve 'ansatz.core/structure-registry) deref deref)]
        (is (= ["a" "c"] (:fields (get sreg "RecTestWide__a_c")))))
      ;; body builds the synth ctor from the kept-field projections; type is the synth record
      (let [ci (env/lookup (a/env) (name/from-string "rec-pick"))]
        (is (re-find #"RecTestWide__a_c\.mk" (e/->string (.value ci))))
        (is (re-find #"RecTestWide__a_c" (e/->string (.type ci))))))
    (do (println "SKIP select-keys-synthesizes-projection-record: no Init env") (is true))))

(deftest rec-defn-proves-fusion-equivalence
  ;; rec/defn compiles the fused pipeline AND admits a kernel theorem
  ;; `<name>.fusion_eq : naive = fused`, certifying the overwrite elimination sound.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestFuse
                 [:map [:a [:and :int [:>= 0]]] [:b [:and :int [:>= 0]]] [:c [:and :int [:>= 0]]]]))
        (eval '(wandler.surface.records/defn rec-fuse-pipe [r :- RecTestFuse] RecTestFuse
                 (-> r (assoc :a 1) (assoc :b 2) (assoc :a 9)))))
      ;; the fused body is verified, and the dead :a 1 write is gone
      (is (true? (verified? "rec-fuse-pipe")))
      (is (not (re-find #"\b1\b" (e/->string (.value (env/lookup (a/env) (name/from-string "rec-fuse-pipe")))))))
      ;; the equivalence theorem `naive = fused` was admitted to the env
      (let [eq (env/lookup (a/env) (name/from-string "rec-fuse-pipe.fusion_eq"))]
        (is (some? eq))
        (is (re-find #"Eq\." (e/->string (.type eq))))))
    (do (println "SKIP rec-defn-proves-fusion-equivalence: no Init env") (is true))))

(deftest nested-def-record-from-schema
  ;; A single Malli schema with a nested :map defines BOTH structures; the nested
  ;; ops then work over them, kernel-verified.
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestCustomer
                 [:map [:id [:and :int [:>= 0]]]
                  [:addr [:map [:zip [:and :int [:>= 0]]] [:num [:and :int [:>= 0]]]]]]))
        (eval '(ansatz.core/defn cust-zip [c :- RecTestCustomer] Nat (get-in c [:addr :zip])))
        (eval '(ansatz.core/defn cust-set-zip [c :- RecTestCustomer] RecTestCustomer
                 (assoc-in c [:addr :zip] 90210))))
      (let [sreg (-> (requiring-resolve 'ansatz.core/structure-registry) deref deref)]
        ;; both the nested and outer structures were defined from the one schema
        (is (= ["zip" "num"] (:fields (get sreg "RecTestCustomerAddr"))))
        (is (= ["id" "addr"] (:fields (get sreg "RecTestCustomer")))))
      (is (true? (verified? "cust-zip")))
      (is (true? (verified? "cust-set-zip"))))
    (do (println "SKIP nested-def-record-from-schema: no Init env") (is true))))

(deftest assoc-rejects-unknown-field
  (if-let [kenv @test-env/init-full-env]
    (do
      (reset! a/ansatz-env kenv)
      (rec/install!)
      (binding [a/*verbose* false]
        (eval '(wandler.surface.records/def-record RecTestAcct3
                 [:map [:balance [:and :int [:>= 0]]]])))
      (is (re-find #"unknown field"
                   (try (binding [a/*verbose* false]
                          (eval '(ansatz.core/defn rec-bad [a :- RecTestAcct3] RecTestAcct3
                                   (assoc a :nope 1))))
                        ""
                        (catch Throwable e
                          (or (some-> (.getCause e) .getMessage) (.getMessage e) ""))))))
    (is true)))

(deftest keyword-as-function-projects-like-the-explicit-lambda
  ;; Track 2 breadth: (map :k rs) — the ubiquitous keyword-as-function idiom — elaborates to the same
  ;; projection as (map (fn [x] (:k x)) rs), so it kernel-verifies and is DEFEQ to the explicit form.
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (rec/install!)
    (binding [a/*verbose* false]
      (eval '(wandler.surface.records/def-record KwTestRow [:map [:owner :string] [:balance :int]]))
      (eval '(ansatz.core/defn kw-explicit [rs :- (List KwTestRow)] (List Int) (map (fn [x] (:balance x)) rs)))
      (eval '(ansatz.core/defn kw-sugar    [rs :- (List KwTestRow)] (List Int) (map :balance rs))))
    (let [val (fn [n] (.value (env/lookup (a/env) (name/from-string n))))
          tc  (ansatz.kernel.TypeChecker. (a/env))]
      (is (some? (val "kw-sugar")) "(map :balance rs) compiles")
      (is (.isDefEq tc (val "kw-explicit") (val "kw-sugar"))
          "keyword-as-fn ≡ the explicit projection lambda"))))
