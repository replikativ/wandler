(ns wandler.talk-demo-test
  "PRESENTATION DEMO (Clojurians) — ONE pipeline shape, the SOURCE TYPE picks the mode: batch (lazy-seq) ·
   incremental (Z-set view) · async (push source / spindel). And a DATALOG QUERY IN THE MIDDLE is
   TRANSPARENT through datahike (a per-event lookup DECORRELATES to a join we can lift, optimize, and
   incrementalize — predicates push INTO datahike's index) but a BARRIER through an OPAQUE engine (an
   external service call runs as-is — we can't see through it to lift constraints).

   Every assertion here is a talk punchline backed by a passing test. The kernel-certified facts (the
   filter→datahike pushdown, incremental ≡ batch) ride the already-proven laws; this just stages them."
  (:require [clojure.test :refer [deftest is testing]]
            [wandler.live :as live]
            [wandler.bridge :as bridge]
            [wandler.bridge.datahike :as dh]
            [wandler.rel-laws :as rl]
            [wandler.kmap :as kmap]
            [ansatz.core :as a]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]))

;; domain: orders {:cid :amt :tier}; premium? = gold tier; revenue = Σ amount of premium orders
(defn premium? [o] (= :gold (:tier o)))
(def ^:private O1 {:cid 1 :amt 100 :tier :gold})
(def ^:private O2 {:cid 2 :amt 50  :tier :silver})
(def ^:private O3 {:cid 1 :amt 80  :tier :gold})

;; ════ ACT 1 — BATCH (lazy-seq): it's just clojure.core ════════════════════════════════════════════
(deftest act1-batch-is-plain-clojure
  (is (= 180 (->> [O1 O2 O3] (filter premium?) (map :amt) (reduce + 0)))
      "ordinary clojure.core over a vector — premium revenue = 180. (Fuses + kernel-verifies under a/defn.)"))

;; ════ ACT 2 — INCREMENTAL: the SAME pipeline as a live view; events update it; retractions undo ════
(deftest act2-incremental-equals-batch-and-retracts
  (let [in (atom nil)
        view (live/linear-node [[:filter premium?] [:sum :amt]])]  ; SAME ops as Act 1, as ∂-nodes
    (live/drive! in view)
    (reset! in {O1  1})                                            ; an order arrives (Z-set delta +1)
    (reset! in {O2  1})                                            ; silver — filtered out
    (reset! in {O3  1})
    (is (= 180 @(:out view)) "the live view = the batch answer, maintained per event (no recompute)")
    (reset! in {O1 -1})                                            ; a RETRACTION (delta −1)
    (is (= 80 @(:out view)) "the certified differential undoes it EXACTLY — incremental ≡ batch, proven")))

;; ════ ACT 3 — ASYNC: the SAME graph, driven by a push SOURCE (spindel / core.async plug in here) ════
(deftest act3-async-same-certified-graph
  (let [subs (atom []) subscribe (fn [cb] (swap! subs conj cb) (fn [])) emit! (fn [d] (doseq [cb @subs] (cb d)))
        view (live/linear-node [[:filter premium?] [:sum :amt]])]
    (live/drive-source! subscribe view)   ; ← a live spindel node's subscription fits `subscribe` verbatim
    (emit! {O1 1}) (emit! {O3 1})
    (is (= 180 @(:out view)) "identical certified graph, now event-driven (async). The TYPE chose the mode, not the code")))

;; ════ ACT 4 — A DATALOG QUERY IN THE MIDDLE, two ways ═════════════════════════════════════════════
(defn- env-ready? [] (some? @test-env/init-full-env))

(deftest act4a-datahike-is-TRANSPARENT
  (when (env-ready?)
    (reset! a/ansatz-env @test-env/init-full-env) (kmap/install!) (rl/install!)
    (testing "a per-order datahike lookup is a CORRELATED subquery → DECORRELATES to ONE join (we see through it)"
      ;; mapcat (λorder. q[where customer.id = order.cid] db) orders   ≡   Map.join cid id orders customers
      (let [nat (e/const' (nm/from-string "Nat") []) prodNN (e/app* (e/const' (nm/from-string "Prod") [lvl/zero lvl/zero]) nat nat)
            idf (e/lam "x" nat (e/bvar 0) :default)
            joined (dh/decorrelate {:row-type prodNN :key-type nat :deceq (e/const' (nm/from-string "instDecidableEqNat") [])
                                    :kf idf :lf idf :rows (e/fvar 1) :scan (e/fvar 2)})]
        (is (= "Map.join" (nm/->string (e/const-name (first (e/get-app-fn-args joined)))))
            "N per-order datahike queries collapse to ONE join — the planner can now optimize + incrementalize it")))
    (testing "and a predicate ABOVE the join is PUSHED INTO datahike's index (certified plan ≡ original)"
      (let [z lvl/zero nat (e/const' (nm/from-string "Nat") []) prodNN (e/app* (e/const' (nm/from-string "Prod") [z z]) nat nat)
            deceq (e/const' (nm/from-string "instDecidableEqNat") []) listN (e/app (e/const' (nm/from-string "List") [z]) nat)
            idf (e/lam "x" nat (e/bvar 0) :default) active? (e/fvar 2)
            pred (e/lam "o" prodNN (e/app active? (e/app* (e/const' (nm/from-string "Prod.fst") [z z]) nat nat (e/bvar 0))) :default)
            query {:op :filter :pred pred
                   :in {:op :join :key-type nat :row nat :deceq deceq :kf idf :lf idf
                        :left {:op :scan :src (e/fvar 3)} :right {:op :scan :src (e/fvar 4)}}}
            lctx {2 {:name "active?" :type (e/forall' "_" nat (e/const' (nm/from-string "Bool") []) :default)}
                  3 {:name "orders" :type listN} 4 {:name "customers" :type listN}}
            {:keys [plan verified? rewrites]} (bridge/optimize-plan (a/env) (fn [ir] (dh/lift ir nat)) query :lctx lctx)]
        (is (true? verified?) "kernel-certified")
        (is (contains? (set rewrites) "Map.filter_join_pushdown") "the filter moved INTO the datahike side")
        (is (= :filter (:op (:left (dh/lower plan)))) "γ-lowered: datahike's index now does the filter (fewer datoms fetched)")))))

(deftest act4b-an-opaque-engine-is-a-BARRIER
  ;; A truly EXTERNAL engine (a black-box service call) is NOT liftable — the optimizer can't see through it
  ;; to push constraints in. `live/flow` recognizes the relational operators and REFUSES to fake-incrementalize
  ;; an unknown one: it names it a BARRIER (runs as batch), rather than silently producing a wrong delta.
  (let [expand-err (fn [form] (try (macroexpand form) nil (catch Throwable e (str (.getMessage e) (some-> (.getCause e) .getMessage)))))]
    (is (re-find #"(?i)barrier" (or (expand-err '(wandler.live/flow (join :cid :id) (call-external-service x))) ""))
        "an opaque external call is a BARRIER — honestly flagged, not silently lifted (contrast datahike)")))
