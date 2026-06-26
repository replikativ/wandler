(ns wandler.inference.dist
  "FinSet and FinDist — the MONAD view of `wandler.inference.semiring`'s `Rel A S` (a finite map outcome→weight).
   A branching computation is a finite weighted map; `return`/`bind` are the semiring's unit/sum-product:

     fin-return sr a   = {a 1̄}                                     -- Dirac point / singleton
     fin-bind  sr m f  = ⊕_a  m(a) ⊗ (f a)                          -- run each branch, ⊗-scale, ⊕-combine

   `⊗` scales a path; `⊕` combines branches that reach the SAME outcome (law of total probability / union).
   The monad needs only ⊗ (a monoid); the QUERY (marginal / expectation) needs ⊕ — and `wandler.inference.semiring/faq`
   is exactly 'do the ⊕-combines in a cost-chosen order', i.e. variable elimination = marginalisation.

   Instances (just pick the semiring):
     FinSet   = `existence`   (S=Bool, ⊗=∧, ⊕=∨)  — finite NONDETERMINISM (the powerset monad)
     FinDist  = `probability` (S=ℝ≥0, ⊗=×, ⊕=+)   — finite PROBABILITY  (the distribution monad)

   So this is the Kleisli view of the relational algebra, NOT a new engine. A probabilistic query's symbolic
   part is L0 (provenance / the proven semiring laws); its numbers are the trusted L2 evaluation (WMC). The
   continuous analogue (the Giry monad) is an L2 oracle boundary, not here. See programming-model-4-structures."
  (:require [wandler.inference.semiring :as sr]))

;; ── the weighted monad over ANY semiring ─────────────────────────────────────────────────────────
(defn fin-return
  "`return a` — the deterministic computation / Dirac point: weight 1̄ on `a`."
  [sr a] {a (:one sr)})

(defn fin-bind
  "`m >>= f` — for each branch `a` with weight `m(a)`, run `f`, ⊗-scale its weights by `m(a)`, and ⊕-combine
   branches that reach the same outcome. (Law of total probability / union of images / weighted sum-product.)"
  [{:keys [add mul zero]} m f]
  (persistent!
    (reduce-kv (fn [acc a w]
                 (reduce-kv (fn [acc b w2] (assoc! acc b (add (get acc b zero) (mul w w2))))
                            acc (f a)))
               (transient {}) m)))

(defn fin-map
  "`map g` over outcomes — relabel each outcome by `g`, ⊕-combining collisions."
  [{:keys [add zero]} g m]
  (persistent! (reduce-kv (fn [acc a w] (let [b (g a)] (assoc! acc b (add (get acc b zero) w)))) (transient {}) m)))

;; ── FinSet — finite nondeterminism (the existence semiring) ──────────────────────────────────────
(defn singleton "FinSet `{a}`." [a] (fin-return sr/existence a))
(defn fset-bind  [m f] (fin-bind sr/existence m f))
(defn to-set "the underlying finite set (outcomes with weight ⊤)." [m] (set (for [[a w] m :when (true? w)] a)))
(defn fset "a FinSet from a Clojure collection." [coll] (into {} (map (fn [a] [a true])) coll))

;; ── FinDist — finite probability (the probability semiring) ──────────────────────────────────────
(defn bernoulli "FinDist Bool: ⊤ with prob `p`." [p] {true p false (- 1.0 (double p))})
(defn uniform   "FinDist over `coll`: each outcome equiprobable." [coll]
  (let [v (vec coll) p (/ 1.0 (count v))] (persistent! (reduce (fn [a x] (assoc! a x (+ (get a x 0.0) p))) (transient {}) v))))
(defn dist-return [a] (fin-return sr/probability a))
(defn dist-bind   [m f] (fin-bind sr/probability m f))
(defn expectation "E[g] = Σ_a m(a)·g(a)." [m g] (reduce-kv (fn [acc a p] (+ acc (* (double p) (double (g a))))) 0.0 m))
(defn prob "P(pred) = Σ_{a : pred a} m(a)." [m pred] (expectation m (fn [a] (if (pred a) 1.0 0.0))))
(defn normalize "rescale weights to sum to 1 (condition / renormalise)." [m]
  (let [t (reduce + 0.0 (vals m))] (if (zero? t) m (persistent! (reduce-kv (fn [a k v] (assoc! a k (/ (double v) t))) (transient {}) m)))))
