(ns wandler.mode-edn-test
  "The MODE LATTICE + ∂ pass (wandler.exec.mode): one surface pipeline mixing BATCH / DIFFERENTIAL / ASYNC,
   organized by a 2-axis (×clock) mode lattice, with the ∂ pass lowering a plan-lens into the Z-set
   incremental engine + a kernel certificate. Grounded in Uustalu–Vene comonadic dataflow + distributive
   laws, Bahr modal FRP, and Rhine type-level clocks (../rhine → ../spindel)."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [ansatz.core :as a]
            [wandler.exec.mode :as m]
            [wandler.exec.live :as live]
            [wandler.exec.zset :as zs]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as kenv]))

;; deferred: the EDN/Value tier (see test-deferred/README.md)

(defn- ready? [] (some? @test-env/init-full-env))
(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

(deftest value-pipeline-edn-aligned
  (when (ready?)
    (testing "EDN keyword-maps flow through the certified incremental engine over the kernel-native Value rep"
      ((requiring-resolve 'wandler.surface.edn/install-core!))
      (let [ValueT (e/const' (nm "Value") [])
            prodVV (e/app* (e/const' (nm "Prod") [z z]) ValueT ValueT)
            vkw    (fn [s] (e/app (e/const' (nm "Value.vkw") []) (e/lit-str s)))
            vget*  (fn [k r] (e/app* (e/const' (nm "vget") []) k r))
            fst*   (fn [p] (e/app* (e/const' (nm "Prod.fst") [z z]) ValueT ValueT p))
            snd*   (fn [p] (e/app* (e/const' (nm "Prod.snd") [z z]) ValueT ValueT p))
            kf     (e/lam "o" ValueT (vget* (vkw "cid") (e/bvar 0)) :default)        ; join order.cid
            lf     (e/lam "c" ValueT (vget* (vkw "id")  (e/bvar 0)) :default)        ;   = cust.id
            pred   (e/lam "p" prodVV (e/app* (e/const' (nm "vkeq") []) (vget* (vkw "tier") (snd* (e/bvar 0))) (vkw "premium")) :default)
            mapf   (e/lam "p" prodVV (vget* (vkw "amt") (fst* (e/bvar 0))) :default) ; project order.amt
            plan   {:op :map :fn mapf
                    :input {:op :filter :pred pred
                            :input {:op :join :kf kf :lf lf :left {:op :source} :right {:op :source}}}}
            inc    (m/incrementalize (a/env) plan m/async)
            run    (m/run-edn (:run inc))
            custs  {{:id 1 :tier :premium} 1 {:id 2 :tier :basic} 1}
            deltas [[{} custs] [{{:cid 1 :amt 100} 1} {}] [{{:cid 2 :amt 50} 1} {}]
                    [{{:cid 1 :amt 30} 1} {}] [{{:cid 1 :amt 100} -1} {}]]
            views  (vec (run deltas))]
        (is (= :async-incremental (:route inc)))
        (is (= [{} {100 1} {100 1} {100 1 30 1} {30 1}] views)
            "EDN in → certified incremental join/filter(premium)/map(amt) over Value → EDN out (basic filtered, retraction drops 100)")))))
