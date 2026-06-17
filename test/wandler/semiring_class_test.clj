(ns wandler.semiring-class-test
  "WSemiring typeclass front door (L4): WAddMonoid ⊂ WSemiring via ansatz :extends, with verified
   instances built straight from carrier registry rows. Proves the bundled-axiom class admits a
   kernel-checked instance — the distributivity proof lines up through the subobject projection."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [wandler.semiring-class :as sc]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

;; Nat row using the core-name distributivity lemma present in init-medium (Nat.left_distrib);
;; the production registry (full store) uses the synonym Nat.mul_add — same statement.
(def ^:private nat-row
  {:add "Nat.add" :mul "Nat.mul" :zero "Nat.zero"
   :hAA "Nat.add_assoc" :hZA "Nat.zero_add" :hAZ "Nat.add_zero"
   :hMA "Nat.left_distrib" :hMZ "Nat.mul_zero" :hZM "Nat.zero_mul"})

(deftest classes-and-instance-install
  (a/load-init!)
  (is (= :installed (sc/install-classes!)))
  (is (sc/classes-installed?) "WAddMonoid + WSemiring defined")
  ;; the hierarchy machinery: subobject projection + an inherited accessor
  (is (has? "WSemiring.toWAddMonoid") "packed parent projection")
  (is (has? "WSemiring.add") "inherited accessor through the subobject")

  ;; verified Nat instance from the row (parent then child, child references parent instance)
  (let [r (sc/build-instance! "Nat" nat-row)]
    (is (= :verified (:status r)) (str "Nat instance should verify: " (:error r)))
    (is (has? "instWAddMonoid_Nat"))
    (is (has? "instWSemiring_Nat") "WSemiring Nat kernel-verified through the subobject")
    (is (some? (sc/instance-term "Nat")))))

(deftest bad-row-fails-gracefully
  (a/load-init!)
  (sc/install-classes!)
  ;; a wrong proof name can't fool the kernel gate — it reports :failed, doesn't throw
  (let [r (sc/build-instance! "Nat" (assoc nat-row :hAA "Nat.mul_comm"))]
    (is (= :failed (:status r)))
    (is (string? (:error r)))))
