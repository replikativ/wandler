(ns wandler.regex-test
  "#63 — the self-contained verified regex matcher + parser, differentially validated against
   java.util.regex (the trust model: our Brzozowski `rmatch` is the kernel-verified SPEC, java is
   the fast executor; they must agree on the regular subset). See [[regex-planning-spike]]."
  (:require [ansatz.core :as a]
            [wandler.regex :as re]
            [wandler.surface.edn :as edn]
            [wandler.surface.collections :as coll]
            [wandler.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]])
  (:import [java.util.regex Pattern]))

(defn- checks? [nm]
  (when-let [ci (kenv/lookup (a/env) (name/from-string nm))]
    (try (kenv/check-constant (a/env)
           (kenv/mk-def (name/from-string (str "__c_" nm))
                        (kenv/ci-level-params ci) (kenv/ci-type ci) (kenv/ci-value ci)) 50000000)
         true (catch Throwable _ false))))

(defn- all-strings "All strings of length 0..maxlen over alphabet." [alphabet maxlen]
  (loop [n 0, acc [""]]
    (if (= n maxlen) acc
        (recur (inc n) (concat acc (for [s acc :when (= (count s) n), c alphabet] (str s c)))))))

(deftest matcher-verifies-and-agrees-with-java
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (re/install!)
      ;; (1) the verified matcher kernel-checks
      (is (true? (checks? "matchEps")) "matchEps verifies")
      (is (true? (checks? "deriv"))    "deriv verifies")
      (is (true? (checks? "rmatch"))   "rmatch verifies")
      ;; (2) specific known matches (parser + matcher)
      (let [abc (re/parse "a(b|c)*")]
        (is (true?  (re/rmatch* abc "abcb")))
        (is (true?  (re/rmatch* abc "a")))
        (is (false? (re/rmatch* abc "abx")))
        (is (false? (re/rmatch* abc "")))
        (is (false? (re/rmatch* abc "bc"))))
      ;; (3) EXHAUSTIVE differential test vs java — all short strings, several patterns.
      ;;     Our rmatch* (verified spec) must agree with java.util.regex on every input.
      (let [cases [["a(b|c)*"  "abc"]
                   ["(a|b)*"   "ab"]
                   ["ab?c"     "abc"]
                   ["a+b+"     "ab"]
                   ["[abc]+"   "abc"]
                   ["a.c"      "abc"]          ; . over printable ASCII
                   ["\\d+"     "012"]
                   ["[0-2]*"   "012"]
                   ["(ab|cd)+" "abcd"]
                   ["x?y?z?"   "xyz"]]
            disagreements
            (for [[pat alpha] cases
                  :let [re-term (re/parse pat)
                        p (Pattern/compile pat)]
                  s (all-strings alpha 4)
                  :when (not= (re/rmatch* re-term s) (re/re-java-matches? p s))]
              [pat s (re/rmatch* re-term s) (re/re-java-matches? p s)])]
        (is (empty? disagreements)
            (str "our rmatch must agree with java regex; disagreements: " (vec (take 8 disagreements))))
        ;; sanity: the test actually exercised many strings
        (is (> (reduce + (map (fn [[_ alpha]] (count (all-strings alpha 4))) cases)) 500))))
    (do (println "SKIP regex matcher test: no Init env") (is true))))

(deftest planning-maps-to-jvm-execution
  (if @test-env/init-full-env
    (do
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (re/install!)
      ;; (1) literal-set detection — a finite-language regex is really set membership
      (is (= #{"foo" "bar" "baz"} (re/literals (re/parse "foo|bar|baz"))) "literal alternation → set")
      (is (= #{"ab" "ac"}         (re/literals (re/parse "a(b|c)")))      "bounded concat → finite set")
      (is (nil? (re/literals (re/parse "[a-z]+")))                        "star → not a literal set")
      (is (nil? (re/literals (re/parse "a(b|c)*")))                       "star → not a literal set")
      ;; (2) exec strategy: the plan decides HashSet vs automaton
      (is (= :hashset   (:strategy (re/exec-strategy (re/parse "cat|dog|fish")))))
      (is (= :automaton (:strategy (re/exec-strategy (re/parse "[0-9]+")))))
      ;; (3) compile-matcher: both paths agree with java on every short string
      (doseq [[pat alpha] [["foo|bar|baz" "fobarz"]   ; → HashSet path
                           ["[a-z]+"      "abz"]       ; → java Pattern path
                           ["a(b|c)*d"    "abcd"]]]
        (let [re-term (re/parse pat)
              ours (re/compile-matcher re-term pat)
              p    (Pattern/compile pat)]
          (is (empty? (for [s (all-strings alpha 4) :when (not= (boolean (ours s)) (re/re-java-matches? p s))] s))
              (str "compile-matcher agrees with java for " pat))))
      ;; (3b) OR-fusion is now KERNEL-PROVEN (not just differential): the matcher is defined via the
      ;;      recursor (rfl constructor equations), so rmatch (rplus p q) x = rmatch p x ∨ rmatch q x
      (is (true? (checks? "matchEps_plus")) "matchEps (rplus a b) = matchEps a ∨ matchEps b (rfl)")
      (is (true? (checks? "deriv_plus"))    "deriv distributes over rplus (rfl)")
      (is (true? (checks? "fold_hom"))      "deriv distributes over the fold (induction)")
      (is (true? (checks? "rmatch_plus"))   "OR-fusion law kernel-certified")
      (is (true? (checks? "reMatchStr_plus")) "String-boundary OR-fusion: (reMatchStr p s)∨(reMatchStr q s) = reMatchStr (p+q) s")
      ;; (4) OR-fusion is sound: rmatch(fuse-or[p q]) = rmatch p ∨ rmatch q (one pass, not two)
      (doseq [[p1 p2 alpha] [["user_[0-9]" "admin_[0-9]" "user_admin0123"]
                             ["a+"         "b+"          "ab"]
                             ["foo"        "bar"         "fobar"]]]
        (let [r1 (re/parse p1) r2 (re/parse p2)
              fused (re/fuse-or [r1 r2])
              jp1 (Pattern/compile p1) jp2 (Pattern/compile p2)]
          (is (empty? (for [s (all-strings alpha 5)
                            :when (not= (re/rmatch* fused s)
                                        (or (re/rmatch* r1 s) (re/rmatch* r2 s)))] s))
              (str "fuse-or = OR of rmatches for " p1 " | " p2))
          ;; and the fused matcher agrees with (java p1 OR java p2)
          (is (empty? (for [s (all-strings alpha 5)
                            :when (not= (re/rmatch* fused s)
                                        (or (re/re-java-matches? jp1 s) (re/re-java-matches? jp2 s)))] s))
              "fused matcher agrees with the disjunction of java patterns"))))
    (do (println "SKIP regex planning test: no Init env") (is true))))

(deftest re-as-verified-field-refinement
  "#62/#63 composition: a `:re` malli field compiles to a PRECISE, kernel-verified conforms node
   (the Brzozowski matcher checks the pattern) once the matcher is installed — gradually sharpening
   from the trusted-string leaf. A regex is a verified field refinement on dynamic Value / records."
  (if @test-env/init-full-env
    (do
      ;; (a) WITHOUT the matcher installed → the trusted-string leaf (accepts ANY string)
      (reset! a/ansatz-env @test-env/init-full-env)
      (coll/install!)
      (edn/install-core!)
      (binding [a/*verbose* false] (doseq [f (edn/schema->conforms-forms 'rc-trusted [:re "u[0-9]+"])] (eval f)))
      (is (true?  ((resolve 'rc-trusted) (edn/edn->value "user"))) "trusted leaf accepts a non-matching string")
      (is (false? ((resolve 'rc-trusted) (edn/edn->value 42)))     "but still rejects non-strings")
      ;; (b) WITH the matcher installed → PRECISE (checks the pattern), kernel-verified
      (re/install!)
      (binding [a/*verbose* false] (doseq [f (edn/schema->conforms-forms 'rc-precise [:re "u[0-9]+"])] (eval f)))
      (is (true? (checks? "reMatchStr")) "the kernel String matcher verifies")
      (is (true? (checks? "rc-precise")) "the precise :re conforms node kernel-verifies")
      (is (true?  ((resolve 'rc-precise) (edn/edn->value "u42"))))
      (is (false? ((resolve 'rc-precise) (edn/edn->value "user"))) "precise: rejects a non-matching string")
      (is (false? ((resolve 'rc-precise) (edn/edn->value "u42x"))))
      (is (false? ((resolve 'rc-precise) (edn/edn->value 42)))     "and non-strings")
      ;; (c) a :re field inside a :map schema is checked field-wise
      (binding [a/*verbose* false]
        (doseq [f (edn/schema->conforms-forms 'rc-map [:map [:id [:re "u[0-9]+"]] [:age :int]])] (eval f)))
      (is (true? (checks? "rc-map")) "record conforms with a :re field verifies")
      (is (true?  ((resolve 'rc-map) (edn/edn->value {:id "u7"  :age 30}))))
      (is (false? ((resolve 'rc-map) (edn/edn->value {:id "bad" :age 30}))) ":re field rejects a non-matching id"))
    (do (println "SKIP regex conforms test: no Init env") (is true))))
