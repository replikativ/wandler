(ns wandler.live-test
  "The LIVE async executor (wandler.live): push-driven certified incremental views wired into a reactive
   DATAFLOW GRAPH. Pure runtime over wandler.zset — no kernel env needed; the certificates live in the
   operators (Zproduct_product_rule for the join, Mode.diff_async_dist for the linear stages)."
  (:require [clojure.test :refer [deftest is testing]]
            [wandler.live :as live]
            [wandler.zset :as zs]))

(deftest fanout-dataflow-graph
  (testing "a reactive DAG: orders ⋈ customers fans out to premium-revenue AND count, both incremental"
    (let [custs    {{:id 1 :tier :premium} 1 {:id 2 :tier :basic} 1}
          premium? (fn [[_o c]] (= :premium (:tier c)))
          revenue  (fn [[o _c]] (:amt o))
          in   (atom nil)                                       ; the reactive input node (events)
          jn   (live/join-node :cid :id)                        ; orders ⋈ customers
          prem (live/linear-node [[:filter premium?] [:sum revenue]])  ; ↳ premium revenue
          cnt  (live/linear-node [[:filter (constantly true)] [:sum (constantly 1)]]) ; ↳ count
          _    (live/connect! jn prem)                          ; graph edges (fan-out)
          _    (live/connect! jn cnt)
          _    (live/drive! in jn)                              ; wire the source
          events [[{} custs]                                    ; load customers
                  [{{:cid 1 :amt 100} 1} {}]                    ; Ann (premium) buys 100
                  [{{:cid 2 :amt 50}  1} {}]                    ; Bo (basic) — filtered from premium
                  [{{:cid 1 :amt 30}  1} {}]                    ; Ann +30
                  [{{:cid 1 :amt 100} -1} {}]]                  ; retract Ann's first order
          prem-traj (atom []) cnt-traj (atom [])]
      (doseq [ev events]
        (reset! in ev)                                          ; fire an event → propagates through the graph
        (swap! prem-traj conj @(:out prem))
        (swap! cnt-traj  conj @(:out cnt)))
      (is (= [0 100 100 130 30] @prem-traj) "premium running revenue maintained incrementally across events")
      (is (= [0 1 2 3 2] @cnt-traj) "running join cardinality maintained incrementally (last event retracts)")
      (is (= 30 @(:out prem)) "final premium revenue")
      (is (= 2  @(:out cnt)) "final count"))))

(deftest flow-copy-paste-clojure-core
  (testing "a clojure.core pipeline with BLACK-BOX fns compiles to a live graph == batch; report flags trust"
    (let [premium? (fn [[_o c]] (= :premium (:tier c)))     ; black-box predicate — plain Clojure, not ansatz
          amount   (fn [[o _c]] (:amt o))                   ; black-box projection
          g  (live/flow (join :cid :id)                     ; SAME vocabulary as batch — no filtering/summing
                        (filter premium?)
                        (map amount)
                        (reduce + 0))
          in (atom nil)
          _  (live/drive! in g)
          custs  {{:id 1 :tier :premium} 1 {:id 2 :tier :basic} 1}
          events [[{} custs] [{{:cid 1 :amt 100} 1} {}] [{{:cid 2 :amt 50} 1} {}]
                  [{{:cid 1 :amt 30} 1} {}] [{{:cid 1 :amt 100} -1} {}]]
          traj (atom [])]
      (doseq [ev events] (reset! in ev) (swap! traj conj @(:out g)))
      (is (= [0 100 100 130 30] @traj) "copy-pasted clojure.core (filter/map/reduce) maintained incrementally")
      (is (= [:join :filter :map :sum] (mapv :op (:report g))) "operators recognized straight from the clojure.core forms")
      (is (every? #(= :trusted (:payload %)) (:report g)) "every leaf fn is a black box ⇒ trusted, not verified")
      (is (string? (live/report-str g)) "the gradual coach report renders"))))

(defn- expand-err
  "Root-cause message of expanding `form` (a macro that throws during expansion is wrapped in a
   Compiler$CompilerException, so unwrap to the original coach message)."
  [form]
  (try (macroexpand form) "(no error)"
       (catch Throwable e (loop [x e] (if-let [c (.getCause x)] (recur c) (.getMessage x))))))

(deftest flow-rejects-non-incrementalizable
  (testing "the coach flags what can't be incrementalized (barriers), instead of silently doing the wrong thing"
    (is (re-find #"group" (expand-err '(wandler.live/flow (join :cid :id) (reduce max 0))))
        "a non-group reduce (max under deletion) is rejected with guidance")
    (is (re-find #"BARRIER" (expand-err '(wandler.live/flow (join :cid :id) (frobnicate x))))
        "an unrecognized operator is flagged as an incremental barrier")))

(deftest live-equals-batch
  (testing "the push-driven live join == the pull/lazy batch recompute at every event"
    (let [custs  {{:id 1} 1 {:id 2} 1}
          in     (atom nil)
          jn     (live/join-node :cid :id)
          _      (live/drive! in jn)
          events [[{} custs] [{{:cid 1 :amt 10} 1} {}] [{{:cid 2 :amt 20} 1} {}] [{{:cid 1 :amt 10} -1} {}]]
          live-traj (atom [])]
      (doseq [ev events] (reset! in ev) (swap! live-traj conj @(:out jn)))
      (is (= (vec (zs/batch-join :cid :id events)) @live-traj)
          "live FRP-driven view == batch recompute, event by event"))))
