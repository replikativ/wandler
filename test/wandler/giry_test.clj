(ns wandler.giry-test
  "(b) The Giry L2 boundary (wandler.inference.giry): continuous probability as a sampler-based monad whose `expectation`
   is the single TRUSTED seam (Monte Carlo here). Shows: continuous-prior expectations; a two-step Giry
   program; the L0/L2 consistency (a discrete FinDist lifts to Giry and the expectations agree); and that the
   DECISION that consumes the expectation (argmin E[cost]) is exact L0/L1 over the trusted numbers."
  (:require [clojure.test :refer [deftest is testing]]
            [wandler.inference.giry :as g]
            [wandler.inference.dist :as d]))

(defn- close? [a b tol] (< (Math/abs (- (double a) (double b))) tol))

(deftest continuous-expectations
  (testing "continuous priors: E by Monte-Carlo matches the analytic mean"
    (is (close? (g/expectation (g/uniform-c 0.0 1.0) identity) 0.5  0.01) "E[Uniform(0,1)] ≈ 0.5")
    (is (close? (g/expectation (g/gaussian 2.0 1.0) identity)  2.0  0.02) "E[Normal(2,1)] ≈ 2.0")
    (is (close? (g/prob (g/gaussian 0.0 1.0) (fn [x] (< x 0.0))) 0.5 0.01) "P(Normal(0,1) < 0) ≈ 0.5"))
  (testing "a two-step Giry PROGRAM (bind): X~Uniform(0,1), Y~Normal(X,0.5) ⇒ E[Y] = E[X] = 0.5"
    (let [prog (g/giry-bind (g/uniform-c 0.0 1.0) (fn [x] (g/gaussian x 0.5)))]
      (is (close? (g/expectation prog identity) 0.5 0.02)))))

(deftest discrete-is-the-L0-subcase
  (testing "a discrete FinDist lifted to Giry has the SAME expectation as FinDist's exact (L0) sum"
    (let [dist {:a 0.3 :b 0.7} val {:a 1.0 :b 0.0}
          exact (d/expectation dist val)                       ; L0: 0.3·1 + 0.7·0 = 0.3 (exact)
          mc    (g/expectation (g/of-findist dist) val)]       ; L2: Monte-Carlo over the lifted sampler
      (is (close? exact 0.3 1e-12) "FinDist exact expectation = 0.3")
      (is (close? mc exact 0.01)   "Giry Monte-Carlo agrees with the exact discrete sum"))))

(deftest the-decision-is-exact-over-trusted-numbers
  (testing "a planner's argmin E[cost] is exact L0/L1; only the expectations are the trusted L2 oracle"
    (let [plans {:A (g/gaussian 100.0 20.0) :B (g/gaussian 120.0 10.0) :C (g/gaussian 90.0 30.0)}
          costs (into {} (map (fn [[k m]] [k (g/expectation m identity)])) plans)   ; trusted L2 estimates
          best  (key (apply min-key val costs))]                                    ; exact decision (L0/L1)
      (is (= :C best) "argmin expected cost picks C (~90) — the decision rule is certifiable; the E's are sampled")
      (is (close? (costs :A) 100.0 1.0) "and the estimates are sound (E[A] ≈ 100)"))))
