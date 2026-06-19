(ns wandler.regex
  "#63 — VERIFIED REGEX PLANNING, self-contained (no Mathlib).

   A regex is an algebraic term (a Kleene algebra) just like our pipeline terms, so it slots into
   the same plan-and-certify architecture. The PLAN layer is the `RegularExpression` (RE) kernel
   term + verified rewrites (OR-fusion = alternation, literal-set detection, simplification); the
   EXECUTION layer emits the JVM-optimal construct (java.util.regex.Pattern, or a HashSet for a
   literal set). Our Brzozowski `rmatch` is the verified SPEC/reference — it agrees with java regex
   by differential testing (the same trust model as malli conforms), and java executes ~11x faster.

   This file installs the matcher (`install!`), builds RE terms from a regex pattern string
   (`parse`), and runs the verified matcher (`rmatch*`). Optimizer wiring (OR-fusion, literal-set
   → index) builds on top. See [[regex-planning-spike]]."
  (:require [wandler.core]
            [ansatz.core :as a]
            [wandler.surface.collections :as coll]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name])
  (:import [java.util.regex Pattern]))

(declare re->surface parse re-conforms-leaf)

;; ── the verified matcher (Init-only) ─────────────────────────────────────────
;; RegularExpression over Nat char-codes. matchEps/deriv are STRUCTURAL recursions written via the
;; recursor IHs (`ih_<field>`) — NOT :termination-by/fuel — so they reduce DEFINITIONALLY on
;; constructors (matchEps (rplus a b) ≡ matchEps a ∨ matchEps b is rfl), which is what lets the
;; OR-fusion law be kernel-PROVEN (install-laws! below). rmatch folds the derivative over the chars.

(defn install!
  "Install the RE inductive + matchEps/deriv/rmatch + the proven algebra laws (idempotent)."
  []
  (when-not (kenv/lookup (a/env) (name/from-string "RE"))
    ;; *optimize* false: the matcher primitives are the verified base — they don't need pipeline
    ;; fusion, and fusing rmatch's `foldl (map Char.toNat …)` would compose Char.toNat into a form
    ;; the codegen table misses. reMatchStr is a boundary helper; correctness, not fusion, matters.
    (binding [a/*verbose* false wandler.core/*optimize* false]
      (eval '(ansatz.core/inductive RE []
               (rzero) (reps) (rchar [c Nat]) (rplus [a RE] [b RE]) (rcomp [a RE] [b RE]) (rstar [r RE])))
      ;; structural via IHs: ih_a/ih_b = the recursive results for the rplus/rcomp fields a,b;
      ;; ih_r = the result for the rstar field r (IH name follows the CONSTRUCTOR field name).
      (eval '(ansatz.core/defn matchEps [r :- RE] Bool
               (match r RE Bool
                 (rzero false) (reps true) (rchar [c] false)
                 (rplus [a b] (or ih_a ih_b))
                 (rcomp [a b] (and ih_a ih_b))
                 (rstar [s] true))))
      (eval '(ansatz.core/defn deriv [r :- RE, c :- Nat] RE
               (match r RE RE
                 (rzero (RE.rzero)) (reps (RE.rzero))
                 (rchar [d] (if (== c d) (RE.reps) (RE.rzero)))
                 (rplus [a b] (RE.rplus ih_a ih_b))
                 (rcomp [a b] (if (matchEps a)
                                (RE.rplus (RE.rcomp ih_a b) ih_b)
                                (RE.rcomp ih_a b)))
                 (rstar [s] (RE.rcomp ih_r (RE.rstar s))))))
      (eval '(ansatz.core/defn rmatch [r :- RE, xs :- (List Nat)] Bool
               (matchEps (List.foldl RE Nat deriv r xs))))
      ;; ── proven algebra laws (the kernel-certified fusion, no longer differential-only) ──
      ;; constructor equations — definitional, since matchEps/deriv are recursor-based
      (eval '(ansatz.core/theorem matchEps_plus [a :- RE, b :- RE]
               (= Bool (matchEps (RE.rplus a b)) (or (matchEps a) (matchEps b))) (rfl)))
      (eval '(ansatz.core/theorem deriv_plus [a :- RE, b :- RE, c :- Nat]
               (= RE (deriv (RE.rplus a b) c) (RE.rplus (deriv a c) (deriv b c))) (rfl)))
      ;; deriv distributes over the fold (list induction generalizing p,q)
      (eval '(ansatz.core/theorem fold_hom [xs :- (List Nat)]
               (forall [p :- RE, q :- RE]
                 (= RE (List.foldl RE Nat deriv (RE.rplus p q) xs)
                       (RE.rplus (List.foldl RE Nat deriv p xs) (List.foldl RE Nat deriv q xs))))
               (induction xs)
               (all_goals (try (intros p q)))
               (all_goals (try (simp List.foldl_cons List.foldl_nil deriv_plus)))
               (all_goals (try (apply ih_tail)))
               (all_goals (try (rfl)))))
      ;; OR-FUSION, kernel-certified: rmatch (rplus p q) xs = rmatch p xs ∨ rmatch q xs
      (eval '(ansatz.core/theorem rmatch_plus [p :- RE, q :- RE, xs :- (List Nat)]
               (= Bool (rmatch (RE.rplus p q) xs) (or (rmatch p xs) (rmatch q xs)))
               (simp rmatch fold_hom matchEps_plus)))
      ;; whole-string matcher over a kernel String — the leaf used by the `:re` conforms node
      (eval '(ansatz.core/defn reMatchStr [r :- RE, s :- String] Bool
               (rmatch r (mapv (fn [c] (Char.toNat c)) (String.toList s)))))
      ;; OR-FUSION at the String boundary — the optimizer fusion law (fusion-lemmas): two regex
      ;; filters on the same string collapse to ONE matcher over the alternation. LHS→RHS is the
      ;; fusion direction (2 reMatchStr calls → 1), confluent. From rmatch_plus.
      (eval '(ansatz.core/theorem reMatchStr_plus [p :- RE, q :- RE, s :- String]
               (= Bool (or (reMatchStr p s) (reMatchStr q s)) (reMatchStr (RE.rplus p q) s))
               (simp reMatchStr rmatch_plus))))))
;; Once `reMatchStr` is in the env, ansatz.surface.schema's `:re` conforms node becomes PRECISE automatically
;; (it env-gates on `reMatchStr` and resolves `re-conforms-leaf` below) — the #62/#63 composition:
;; a regex becomes a verified field refinement. No global hook; gated on env state (test-isolated).

;; ── RE builders (Clojure → the #59 tagged runtime rep) ────────────────────────
;; cidx: rzero=0 reps=1 rchar=2 rplus=3 rcomp=4 rstar=5  (constructor declaration order)
(def ^:const RZERO [0])
(def ^:const REPS  [1])
(defn rchar [c] [2 (int c)])
(defn rplus [a b] [3 a b])
(defn rcomp [a b] [4 a b])
(defn rstar [r] [5 r])

(defn alt*  "Alternation of a seq of REs (∅ if empty)." [res]
  (if (empty? res) RZERO (reduce rplus res)))
(defn cat*  "Concatenation of a seq of REs (ε if empty)." [res]
  (if (empty? res) REPS (reduce rcomp res)))
(defn ropt  "e? = e | ε" [r] (rplus r REPS))
(defn rplus1 "e+ = e·e*" [r] (rcomp r (rstar r)))
(defn lit   "An RE matching a literal string exactly." [s] (cat* (map rchar s)))
(defn char-range "RE matching any char in [lo..hi] inclusive." [lo hi]
  (alt* (map (comp rchar char) (range (int lo) (inc (int hi))))))

;; ── parser: regex pattern string → RE term ────────────────────────────────────
;; Supports the REGULAR subset: literals, concatenation, alternation |, postfix * + ?, groups (),
;; char classes [..] with ranges a-z, `.` (over printable ASCII), and \d \w \s escapes + \<meta>.
;; Not supported (non-regular / TODO): backrefs, lookaround, anchors ^$, {n,m}, lazy quantifiers.

(def ^:private printable-ascii (char-range \space \~))   ; . = any printable ASCII char
(def ^:private class-shorthand
  {\d [[\0 \9]]
   \w [[\a \z] [\A \Z] [\0 \9] [\_ \_]]
   \s [[\space \space] [\tab \tab] [\newline \newline] [\return \return]]})

(defn- ranges->re [ranges] (alt* (map (fn [[lo hi]] (char-range lo hi)) ranges)))

(declare parse-alt)

(defn- parse-class
  "Parse a [...] class starting after '['. Returns [re rest-idx]."
  [s i]
  (loop [i i, ranges []]
    (let [c (nth s i nil)]
      (cond
        (nil? c) (throw (ex-info "regex: unterminated [" {:s s}))
        (= c \]) [(ranges->re ranges) (inc i)]
        (and (= c \\) (class-shorthand (nth s (inc i) nil)))
        (recur (+ i 2) (into ranges (class-shorthand (nth s (inc i)))))
        (= c \\) (recur (+ i 2) (conj ranges [(nth s (inc i)) (nth s (inc i))]))
        ;; range  a-z
        (and (= (nth s (inc i) nil) \-) (not= (nth s (+ i 2) nil) \]) (nth s (+ i 2) nil))
        (recur (+ i 3) (conj ranges [c (nth s (+ i 2))]))
        :else (recur (inc i) (conj ranges [c c]))))))

(defn- parse-atom [s i]
  (let [c (nth s i nil)]
    (case c
      \( (let [[re j] (parse-alt s (inc i))]
           (when-not (= (nth s j nil) \)) (throw (ex-info "regex: unbalanced (" {:s s})))
           [re (inc j)])
      \[ (parse-class s (inc i))
      \. [printable-ascii (inc i)]
      \\ (let [d (nth s (inc i) nil)]
           (if-let [rngs (class-shorthand d)]
             [(ranges->re rngs) (+ i 2)]
             [(rchar d) (+ i 2)]))             ; \<meta> → literal
      [(rchar c) (inc i)])))

(defn- parse-postfix [s i]
  (let [[re j] (parse-atom s i)]
    (loop [re re, j j]
      (case (nth s j nil)
        \* (recur (rstar re) (inc j))
        \+ (recur (rplus1 re) (inc j))
        \? (recur (ropt re) (inc j))
        [re j]))))

(defn- parse-cat [s i]
  (loop [i i, factors []]
    (let [c (nth s i nil)]
      (if (or (nil? c) (#{\| \)} c))
        [(cat* factors) i]
        (let [[re j] (parse-postfix s i)] (recur j (conj factors re)))))))

(defn- parse-alt [s i]
  (loop [i i, branches []]
    (let [[re j] (parse-cat s i)]
      (if (= (nth s j nil) \|)
        (recur (inc j) (conj branches re))
        [(alt* (conj branches re)) j]))))

(defn parse
  "Parse a regex pattern string into an RE term (the runtime tagged rep). Regular subset only."
  [pattern]
  (let [[re i] (parse-alt pattern 0)]
    (when (not= i (count pattern)) (throw (ex-info "regex: trailing input" {:s pattern :at i})))
    re))

;; ── run the verified matcher / compare with java ─────────────────────────────
(defn rmatch*
  "Run the verified Brzozowski matcher: does `re` (a tagged RE term) match the whole string `s`?
   `install!` must have run. This is the SPEC — java (`re-java-matches?`) is the fast executor."
  [re s]
  (boolean ((resolve 'rmatch) re (mapv int s))))

(defn re-java-matches? "java.util.regex whole-string match (the fast executor)." [^Pattern p ^String s]
  (.matches (.matcher p s)))

;; ── PLANNING: analyze an RE, then map to the JVM-optimal executor ─────────────
;; The RE is the plan term; these decide how it runs on the JVM. Two structural facts pay off
;; hugely (measured in [[regex-planning-spike]]): a regex whose language is a FINITE SET of literals
;; runs as O(1) HashSet membership (~43x vs an automaton), and a disjunction of regex filters FUSES
;; to one alternation (~4x). Our verified `rmatch` is the spec these are validated against.

(def ^:private literal-set-cap 1024)   ; above this, the automaton/Pattern path wins anyway

(defn literals
  "If `re`'s language is a FINITE set of ≤ `literal-set-cap` strings, return that set; else nil.
   Such a regex is really set membership — compile it to a HashSet, not an automaton. (A bounded
   pattern like `a.c` or `foo|bar` is finite; anything under * is not.)"
  [re]
  (letfn [(go [re]
            (case (long (first re))
              0 #{}                                   ; ∅  — empty language
              1 #{""}                                 ; ε
              2 #{(str (char (second re)))}           ; char
              3 (let [a (go (nth re 1)) b (go (nth re 2))]   ; union
                  (when (and a b (<= (+ (count a) (count b)) literal-set-cap)) (into a b)))
              4 (let [a (go (nth re 1)) b (go (nth re 2))]   ; concat (cartesian)
                  (when (and a b (<= (* (count a) (count b)) literal-set-cap))
                    (set (for [x a y b] (str x y)))))
              5 nil))]                                 ; star — infinite
    (go re)))

(defn fuse-or
  "OR-fusion: combine regexes (RE terms) into ONE that matches iff ANY does — `rplus` = alternation.
   KERNEL-CERTIFIED by the theorem `rmatch_plus` (install!): rmatch (rplus p q) x = rmatch p x ∨
   rmatch q x. Replaces N matcher passes with one."
  [res]
  (alt* res))

(defn compile-matcher
  "Map a planned regex to the JVM-optimal whole-string predicate (String → boolean): a finite
   literal language → O(1) HashSet membership; otherwise a compiled java.util.regex.Pattern built
   from `pattern`. `re` is the verified plan term used only to DECIDE; java does the running."
  [re ^String pattern]
  (if-let [lits (literals re)]
    (fn [^String x] (contains? lits x))
    (let [p (Pattern/compile pattern)] (fn [^String x] (.matches (.matcher p x))))))

(defn exec-strategy
  "The execution strategy a planned regex maps to (for plan/explain + tests): :hashset (finite
   literal language, size) or :automaton (java Pattern)."
  [re]
  (if-let [lits (literals re)] {:strategy :hashset :size (count lits)} {:strategy :automaton}))

;; ── conforms integration: a `:re` field → the verified matcher as its refinement (#62/#63) ────
(defn re->surface
  "Convert an RE tagged term into the surface constructor form (RE.rcomp (RE.rchar 97) …) for
   embedding in a kernel-elaborated conforms predicate."
  [re]
  (case (long (first re))
    0 '(RE.rzero)
    1 '(RE.reps)
    2 (list 'RE.rchar (second re))
    3 (list 'RE.rplus (re->surface (nth re 1)) (re->surface (nth re 2)))
    4 (list 'RE.rcomp (re->surface (nth re 1)) (re->surface (nth re 2)))
    5 (list 'RE.rstar (re->surface (nth re 1)))))

(defn re-conforms-leaf
  "Build the conforms form for `[:re pattern]` over `target`: it's a string AND the string matches
   the (parsed) pattern under the verified matcher. Installed as edn/*re-leaf-fn* by install!."
  [pattern target]
  (list 'and (list 'vstr? target)
        (list 'reMatchStr (re->surface (parse (str pattern))) (list 'vstr-val target))))
