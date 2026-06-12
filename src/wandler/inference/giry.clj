(ns wandler.inference.giry
  "(b) The GIRY monad — CONTINUOUS probability — as an L2 TRUSTED-ORACLE boundary. This is the one piece of
   the inference stack that genuinely leaves the Init-only kernel: a continuous measure (a Gaussian prior, a
   continuous latent) needs σ-algebras + integration, which is not L0. So we model it exactly as the type
   theory prescribes — a TYPED INTERFACE whose evaluation is a trusted oracle, the same shape as `Datahike.q`.

   A measure is represented as a SAMPLER `rng → A`; the trusted seam is

       expectation : Giry A → (A → ℝ) → ℝ              (E[g] = ∫ g dμ, estimated by Monte Carlo here)

   `expectation` is the ONLY trusted thing — in production it's a real integrator / a knowledge-compilation
   backend; here it's seeded Monte Carlo so it's runnable and reproducible. Everything that *consumes* the
   expectation — a planner's `argmin E[cost]`, a decision rule — is ordinary L0/L1 logic over the (trusted)
   numbers. The DISCRETE sub-case is `wandler.inference.dist`/`FinDist`, which is fully L0 (exact finite sums, monad law
   proven as `WList.left_unit`); Giry is its continuous completion, and they AGREE on a discrete measure.

   So the boundary is sharp and named: discrete probability = L0 (proven); continuous = L2 (this), behind the
   `expectation` seam. See docs/TYPE_THEORY.md (L2), [[finset-findist-monad]]."
  (:import [java.util Random]))

;; ── the Giry monad (a measure = a sampler rng→A) ─────────────────────────────────────────────────
(defn giry-return "δ_a — the point mass at a." [a] (fn [^Random _] a))
(defn giry-bind   "μ >>= κ — sample μ, then sample the kernel κ at that point (the mixture / disintegration)."
  [m k] (fn [^Random r] ((k (m r)) r)))
(defn giry-map    [g m] (fn [^Random r] (g (m r))))

;; ── continuous priors (the part that has no L0 representation) ────────────────────────────────────
(defn uniform-c "Uniform(lo,hi)." [lo hi] (fn [^Random r] (+ lo (* (- hi lo) (.nextDouble r)))))
(defn gaussian  "Normal(μ,σ)."     [mu sigma] (fn [^Random r] (+ mu (* sigma (.nextGaussian r)))))
(defn beta-ish  "a crude Beta(a,b) via the ratio of two Gamma-ish sums (demo prior; mean ≈ a/(a+b))."
  [a b] (fn [^Random r] (let [g (fn [k] (reduce + 0.0 (repeatedly k #(- (Math/log (max 1e-12 (.nextDouble r)))))))
                              x (g a) y (g b)] (/ x (+ x y)))))

;; ── the TRUSTED L2 SEAM: expectation / probability via Monte Carlo (seeded ⇒ reproducible) ─────────
(defn expectation
  "E[g] = ∫ g dμ — the trusted oracle. Monte-Carlo over `n` seeded samples. (Production: a real integrator.)"
  ([m g] (expectation m g 100000 42))
  ([m g n seed]
   (let [r (Random. seed)]
     (/ (reduce (fn [acc _] (+ acc (double (g (m r))))) 0.0 (range n)) (double n)))))

(defn prob "P(pred) = E[1_pred]." ([m pred] (prob m pred 100000 42)) ([m pred n seed] (expectation m (fn [a] (if (pred a) 1.0 0.0)) n seed)))

;; ── the L0/L2 bridge: a DISCRETE FinDist lifts to a Giry measure (and the expectations agree) ──────
(defn of-findist
  "Lift a discrete `FinDist` (a map outcome→prob, from wandler.inference.dist) to a Giry measure (a sampler) — so the
   L0 discrete case is literally the discrete sub-object of the L2 continuous one; their `expectation`s agree."
  [dist]
  (let [pairs (vec dist) cum (reductions + (map second pairs))]
    (fn [^Random r] (let [u (.nextDouble r)] (loop [i 0] (if (or (>= i (dec (count pairs))) (< u (nth cum i))) (first (nth pairs i)) (recur (inc i))))))))
