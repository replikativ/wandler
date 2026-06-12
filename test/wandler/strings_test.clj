(ns wandler.strings-test
  "Strings as a first-class data type in the verified optimizer.

   Two layers, both Init-only (no Mathlib): (1) string-ELEMENT pipelines (`map trim
   (map toUpper xs)`, filter by a string predicate) ride the ORDINARY collection fusion
   — `map_map`/`filter_filter` don't care that the element is a String, so string ETL
   fuses for free and is kernel-certified. (2) the string-SPECIFIC concat MONOID
   `(String, ++, \"\")` — `append_assoc`/`append_empty`/`empty_append`, with `length` a
   homomorphism to `(Nat,+,0)` via `length_append` — all present in Init; the two identity
   laws are in `opt/string-lemmas` (default fusion set), so redundant empty concats are
   eliminated automatically. This is the substrate for malli string-constraint refinements
   (`[:string {:min/:max/:re}]` → `Subtype`) which drive constraint-based replanning."
  (:require [ansatz.core :as a]
            [wandler.test-env :as test-env]
            [wandler.optimize :as opt]
            [wandler.malli :as malli]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.extract :as extract]
            [clojure.test :refer [deftest is]]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)
(def ^:private strT (e/const' (nm "String") []))
(def ^:private listStr (e/app (e/const' (nm "List") [z]) strT))
(defn- d [s] (e/const' (nm s) []))
(defn- mapS [f l] (e/app* (e/const' (nm "List.map") [z z]) strT strT f l))
(defn- happ [x y]
  (e/app* (e/const' (nm "HAppend.hAppend") [z z z]) strT strT strT
          (e/app* (e/const' (nm "instHAppendOfAppend") [z]) strT (d "instAppendString")) x y))

(defn- with-init [f]
  (if-let [kenv @test-env/init-full-env]
    (do (reset! a/ansatz-env kenv) (f))
    (is true "SKIP: no Init env")))

(deftest string-element-pipelines-fuse-for-free
  ;; A string ETL pass `map trim (map toUpper strs)` fuses to ONE pass via the ordinary
  ;; collection law map_map — strings need no special rule. Kernel-certified.
  (with-init
    (fn []
      (let [strs (e/fvar 6001)
            lctx {6001 {:name "strs" :type listStr}}
            term (mapS (d "String.trim") (mapS (d "String.toUpper") strs))
            r (opt/optimize-cost (a/env) term :lctx lctx)]
        (is (:changed? r) "string ETL map-map fused")
        (is (:verified? r) "the fusion is kernel-certified")
        (is (< (opt/pipeline-cost (:term r)) (opt/pipeline-cost term))
            "one pass instead of two (cost halved)")
        (is (clojure.string/includes? (e/->string (:term r)) "Function.comp")
            "result is a single map of the composed transform")))))

(deftest concat-monoid-eliminates-empty
  ;; The string concat monoid is default optimizer vocabulary (opt/string-lemmas): a
  ;; redundant empty concat `(s ++ \"\") ++ t` simplifies to `s ++ t`, kernel-certified,
  ;; with NO extra-lemmas passed (it rides the default fusion set).
  (with-init
    (fn []
      (let [s (e/fvar 7001) t (e/fvar 7002)
            lctx {7001 {:name "s" :type strT} 7002 {:name "t" :type strT}}
            term (happ (happ s (e/lit-str "")) t)
            r (opt/optimize (a/env) term :lctx lctx)]
        (is (:changed? r) "redundant empty concat removed")
        (is (:verified? r) "the simplification is kernel-certified")
        ;; the inner `s ++ \"\"` collapsed to `s`, so the result no longer mentions the literal
        (is (not (clojure.string/includes? (e/->string (:term r)) "\"\""))
            "no empty-string literal remains")))))

(deftest concat-monoid-and-length-homomorphism-are-init
  ;; The load-bearing string algebra is all in Init — no Mathlib needed for the string layer.
  (with-init
    (fn []
      (doseq [law ["String.append_assoc" "String.append_empty" "String.empty_append"
                   "String.length_append"]]
        (is (some? (kenv/lookup (a/env) (nm law)))
            (str law " present in Init (string monoid + length homomorphism)"))))))

;; ── malli string-constraint refinements (#44 step 2) ──────────────────────────
;; [:string {:min n :max m}] → {s : String // n ≤ s.length ∧ s.length ≤ m}. The
;; constraint is carried in the TYPE (a Subtype) and erased at runtime; it's the dependent
;; foundation for constraint-driven replanning.

(deftest malli-string-constraints-become-subtypes
  (with-init
    (fn []
      (let [st (tc/mk-tc-state (a/env))
            well-typed? (fn [schema]
                          (let [ty (malli/malli->type-expr schema)]
                            (e/sort? (tc/infer-type st ty))))]
        (is (= strT (malli/malli->type-expr :string)) "bare :string → String")
        (is (well-typed? [:string {:min 1}]) "[:string {:min 1}] → well-typed Subtype")
        (is (well-typed? [:string {:min 1 :max 10}]) "[:string {:min/:max}] → well-typed Subtype")
        (is (well-typed? [:string {:max 255}]) "[:string {:max 255}] → well-typed Subtype")
        ;; the refinement body mentions String.length (the carried invariant)
        (is (clojure.string/includes? (e/->string (malli/malli->type-expr [:string {:min 1}]))
                                      "String.length")
            "refinement predicate is over s.length")))))

(deftest string-length-refinement-discharges-checks
  ;; THE PAYOFF: a non-empty refinement `{s // 1 ≤ s.length}` lets omega discharge a
  ;; redundant emptiness check `0 < s.length` — kernel-certified. omega treats `s.length`
  ;; as a Nat atom, so the existing arithmetic discharge drives string constraint-elimination
  ;; with no new machinery. This is what makes constraint-driven replanning sound for strings.
  (with-init
    (fn []
      (let [Nat (e/const' (nm "Nat") [])
            lenS (fn [s] (e/app (d "String.length") s))
            le (fn [a b] (e/app* (e/const' (nm "LE.le") [z]) Nat (d "instLENat") a b))
            lt (fn [a b] (e/app* (e/const' (nm "LT.lt") [z]) Nat (d "instLTNat") a b))
            g (e/forall' "s" strT
                (e/forall' "h" (le (e/lit-nat 1) (lenS (e/bvar 0)))
                  (lt (e/lit-nat 0) (lenS (e/bvar 1))) :default) :default)
            [ps _] (proof/start-proof (a/env) g)
            ps (basic/intros ps ["s" "h"])
            ps (omega/omega ps)
            proof (when (proof/solved? ps) (extract/extract ps))]
        (is (proof/solved? ps) "omega discharges 0 < s.length from 1 ≤ s.length")
        (is (and proof (kenv/verifies? (a/env) g proof))
            "the discharge is kernel-certified (check-constant)")))))
