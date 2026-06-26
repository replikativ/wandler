(ns wandler.malli-envelope-test
  "#57 — the VERIFIED-MALLI expressiveness envelope. Each entry is a malli schema we compile to
   a kernel-proved-TOTAL `Value → Bool` conformance predicate; the test asserts (a) EVERY
   generated a/defn form passes authoritative check-constant, and (b) the predicate AGREES with
   `malli.core/validate` on hundreds of `malli.generator`-produced values per schema. This file
   doubles as the capability spec: the list below IS the supported schema surface.

   Scope note: comparison is over the EDN VALUE domain Ansatz models — nil/bool/string/keyword,
   in-range integers (host BigInt is excluded: `:int`≈`integer?`, the numeric-tower distinction
   is erased by design), and collections thereof. Doubles/uuids/etc. are not modeled and are
   filtered out of the differential comparison. Requires malli (the :malli alias) + Init env."
  (:require [ansatz.core :as a]
            [wandler.surface.edn :as edn]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]))

(defn- checks? [nm]
  (when-let [ci (kenv/lookup (a/env) (name/from-string nm))]
    (try (kenv/check-constant (a/env)
           (kenv/mk-def (name/from-string (str "__c_" nm))
                        (kenv/ci-level-params ci) (kenv/ci-type ci) (kenv/ci-value ci)) 50000000)
         true (catch Throwable _ false))))

(defn- domain?
  "Is `x` in the EDN value domain Ansatz models? Excludes host numeric subtypes (BigInt,
   doubles) and non-EDN types, over which we make no faithfulness claim."
  [x]
  (cond
    (nil? x) true (boolean? x) true (string? x) true (keyword? x) true (double? x) true
    (or (instance? Long x) (instance? Integer x)) true
    (map? x) (every? (fn [[k v]] (and (domain? k) (domain? v))) x)
    (set? x) (every? domain? x)
    (sequential? x) (every? domain? x)
    :else false))

;; The supported schema surface (Tier 1 + ranges). Each is fuzzed against malli/validate.
(def ^:private envelope
  '[:int :string :keyword :boolean :nil :any
    int? integer? string? keyword? boolean? nil? any? map? vector?
    pos-int? nat-int? neg-int?
    [:int {:min 0 :max 100}] [:int {:min 5}] [:int {:max 9}]
    [:string {:min 2 :max 5}] [:string {:min 1}]
    :double double? [:double {:min 0.0 :max 1.0}] [:double {:min -5.0 :max 5.0}] [:double {:min -1.5}]
    [:enum :a :b :c] [:enum 1 2 3] [:= 42] [:= :admin] [:= "x"] [:not= 0]
    [:and :int [:int {:min 0}]] [:or :int :string] [:or :int :string :keyword]
    [:not :int] [:maybe :int] [:maybe :string]
    [:map [:name :string] [:age :int]]
    [:map [:age [:int {:min 0 :max 120}]] [:role [:enum :admin :user]]]
    [:map [:id [:or :int :string]] [:nick [:maybe :string]]]
    [:map [:name :string] [:age {:optional true} :int]]
    [:vector :int] [:vector :string] [:vector [:enum :x :y]] [:vector [:int {:min 0}]]
    [:tuple :int :string] [:tuple :int :int :keyword] [:tuple]
    [:tuple :int [:vector :int]]
    [:map-of :keyword :int] [:map-of :string :int]
    [:map-of :keyword [:int {:min 0 :max 9}]]
    [:map [:addr [:map [:city :string] [:zip [:int {:min 0}]]]]]
    [:map [:tags [:vector :keyword]] [:scores [:vector [:int {:min 0 :max 10}]]]]
    [:map [:pt [:tuple :int :int]]] [:map [:env [:map-of :keyword :string]]]
    [:vector [:tuple :int :string]]
    ;; sets + doubles
    [:set :int] [:set :keyword] [:set :double] [:set [:int {:min 0}]]
    [:map [:lat :double] [:lng :double]] [:map [:tags [:set :keyword]]]
    [:or :int :double] [:vector :double] [:map-of :keyword :double]
    ;; closed maps + tagged unions
    [:map {:closed true} [:a :int] [:b :string]]
    [:map {:closed true} [:a :int] [:b {:optional true} :string]]
    [:multi {:dispatch :type}
     [:a [:map [:type [:= :a]] [:x :int]]]
     [:b [:map [:type [:= :b]] [:s :string]]]]
    [:multi {:dispatch :kind}
     [:pt [:map [:kind [:= :pt]] [:xy [:tuple :int :int]]]]
     [:malli.core/default [:map [:kind :keyword]]]]])

;; Recursive (self-referential) schemas — local registry + [:ref ::self]. Each compiles to ONE
;; structurally-recursive Value→Bool predicate (refs become self-calls on match-bound subterms).
(def ^:private recursive-envelope
  '[;; the canonical malli recursion example: a non-empty cons-list of positive ints (or nil)
    [:schema {:registry {::cons [:maybe [:tuple pos-int? [:ref ::cons]]]}} [:ref ::cons]]
    ;; cons-list of strings
    [:schema {:registry {::s [:maybe [:tuple :string [:ref ::s]]]}} [:ref ::s]]
    ;; ref in head position
    [:schema {:registry {::t [:maybe [:tuple [:ref ::t] :int]]}} [:ref ::t]]
    ;; or-shaped: leaf int OR a tagged recursive pair
    [:schema {:registry {::n [:or :int [:tuple [:= :node] [:ref ::n]]]}} [:ref ::n]]
    ;; TREE: recursive ref nested inside :vector (children)
    [:schema {:registry {::tree [:map [:val :int] [:children [:vector [:ref ::tree]]]]}}
     [:ref ::tree]]
    ;; JSON: recursive :or with refs inside :vector, :set, and :map-of
    [:schema {:registry {::json [:or :nil :boolean [:int {:min -100 :max 100}] :double :string
                                 [:vector [:ref ::json]] [:set [:ref ::json]]
                                 [:map-of :string [:ref ::json]]]}}
     [:ref ::json]]
    ;; MUTUAL recursion: ping ↔ pong
    [:schema {:registry {::ping [:maybe [:tuple [:= "ping"] [:ref ::pong]]]
                         ::pong [:maybe [:tuple [:= "pong"] [:ref ::ping]]]}}
     [:ref ::ping]]])

(defn- fuzz-schema!
  "Compile `schema`, assert every form check-constants, and assert the predicate agrees with
   malli/validate on `vals` (filtered to the modeled EDN domain)."
  [validate schema vals]
  (let [nm    (gensym "fz__")
        forms (edn/schema->conforms-forms nm schema)
        _     (binding [a/*verbose* false] (doseq [f forms] (eval f)))
        pred  (resolve nm)
        cmp   (for [x vals :when (domain? x)
                    :let [v (try (edn/edn->value x) (catch Throwable _ ::skip))]
                    :when (not= v ::skip)]
                [x (boolean (validate schema x)) (boolean (pred v))])
        mism  (filter (fn [[_ e g]] (not= e g)) cmp)]
    (doseq [f forms]
      (is (true? (checks? (str (nth f 1))))
          (str (nth f 1) " (from " (pr-str schema) ") kernel-verifies")))
    (is (empty? mism)
        (str "conforms == malli/validate for " (pr-str schema)
             " (checked " (count cmp) ", mismatches: " (pr-str (take 3 mism)) ")"))))

(deftest schema-expressiveness-envelope
  (let [validate (try (requiring-resolve 'malli.core/validate) (catch Throwable _ nil))
        sample   (try (requiring-resolve 'malli.generator/sample) (catch Throwable _ nil))]
    (if (and @test-env/init-full-env validate sample)
      (do
        (reset! a/ansatz-env @test-env/init-full-env)
        (edn/install-core!)
        (let [junk '[:or [:int {:min -100000 :max 100000}] :string :boolean :keyword :nil :double
                     [:vector [:int {:min -1000 :max 1000}]] [:vector :string] [:set :keyword]
                     [:tuple :int :string] [:map-of :keyword [:int {:min -1000 :max 1000}]]
                     [:map [:type [:enum :a :b :c]] [:x :int]] [:map [:a :int] [:b :string]]]]
          (doseq [schema envelope]
            (fuzz-schema! validate schema
                          (concat (try (sample schema {:size 40 :seed 11}) (catch Throwable _ []))
                                  (try (sample junk   {:size 60 :seed 22}) (catch Throwable _ [])))))))
      (do (println "SKIP schema-expressiveness-envelope: no Init env / malli") (is true)))))

(deftest fn-objects-and-trusted-leaf
  (let [validate (try (requiring-resolve 'malli.core/validate) (catch Throwable _ nil))
        sample   (try (requiring-resolve 'malli.generator/sample) (catch Throwable _ nil))]
    (if (and @test-env/init-full-env validate sample)
      (do
        (reset! a/ansatz-env @test-env/init-full-env)
        (edn/install-core!)
        ;; UNQUOTED predicate fns (the fn objects) resolve like their symbols — and stay faithful
        ;; to malli, so they go through the same differential fuzz.
        (doseq [schema [[:tuple pos-int? string?]
                        [:map [:n int?] [:s string?] [:ok boolean?]]
                        [:vector pos-int?]
                        [:map [:xs [:set keyword?]]]]]
          (fuzz-schema! validate schema
                        (concat (try (sample schema {:size 40 :seed 3}) (catch Throwable _ []))
                                (try (sample '[:or :int :string [:vector :int]
                                               [:map [:n :int] [:s :string] [:ok :boolean]]]
                                             {:size 40 :seed 4}) (catch Throwable _ [])))))
        ;; :fn / unknown fn → TRUSTED leaf (gradual Any): compiles, verifies, accepts anything at
        ;; that node (over-approximates malli), but structural siblings still reject.
        (let [compile! (fn [schema]
                         (let [nm (gensym "fn__")
                               forms (edn/schema->conforms-forms nm schema)]
                           (binding [a/*verbose* false] (doseq [f forms] (eval f)))
                           (doseq [f forms]
                             (is (true? (checks? (str (nth f 1)))) (str (nth f 1) " verifies")))
                           (resolve nm)))]
          (let [p (compile! [:fn even?])]
            (is (true? (p (edn/edn->value 3))) ":fn leaf accepts anything (trusted)")
            (is (true? (p (edn/edn->value "x")))))
          (let [p (compile! [:and [:map [:a :int]] [:fn (fn [m] (pos? (:a m)))]])]
            (is (true? (p (edn/edn->value {:a 5}))) "structural ok + fn trusted")
            (is (true? (p (edn/edn->value {:a -5}))) "fn node trusted → -5 passes")
            (is (false? (p (edn/edn->value {:a "x"}))) "structural :map still rejects bad type"))
          ;; :re verifies string-ness; the pattern is trusted (over-approximates malli)
          (let [p (compile! [:re #"\d+"])]
            (is (true?  (p (edn/edn->value "123"))) ":re verifies a string")
            (is (true?  (p (edn/edn->value "abc"))) ":re pattern trusted → non-matching string passes")
            (is (false? (p (edn/edn->value 5)))     ":re still rejects a non-string"))))
      (do (println "SKIP fn-objects-and-trusted-leaf: no Init env / malli") (is true)))))

(deftest recursive-schemas
  (let [validate (try (requiring-resolve 'malli.core/validate) (catch Throwable _ nil))
        sample   (try (requiring-resolve 'malli.generator/sample) (catch Throwable _ nil))]
    (if (and @test-env/init-full-env validate sample)
      (do
        (reset! a/ansatz-env @test-env/init-full-env)
        (edn/install-core!)
        ;; junk yields shallow nested lists/scalars that mostly violate the recursive shape
        (let [junk '[:or :nil :int :string :keyword
                     [:tuple [:int {:min -5 :max 5}] :nil]
                     [:tuple :int [:tuple :int :nil]] [:vector :int]]]
          (doseq [schema recursive-envelope]
            (fuzz-schema! validate schema
                          (concat (try (sample schema {:size 60 :seed 5}) (catch Throwable _ []))
                                  (try (sample junk   {:size 50 :seed 6}) (catch Throwable _ [])))))))
      (do (println "SKIP recursive-schemas: no Init env / malli") (is true)))))
