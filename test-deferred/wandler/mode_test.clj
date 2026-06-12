(ns wandler.mode-test
  "The MODE LATTICE + ∂ pass (wandler.mode): one surface pipeline mixing BATCH / DIFFERENTIAL / ASYNC,
   organized by a 2-axis (×clock) mode lattice, with the ∂ pass lowering a plan-lens into the Z-set
   incremental engine + a kernel certificate. Grounded in Uustalu–Vene comonadic dataflow + distributive
   laws, Bahr modal FRP, and Rhine type-level clocks (../rhine → ../spindel)."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [ansatz.core :as a]
            [wandler.mode :as m]
            [wandler.live :as live]
            [wandler.zset :as zs]
            [wandler.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as kenv]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero)

(defn- setup [f]
  (when @test-env/init-full-env
    (reset! a/ansatz-env @test-env/init-full-env)
    (m/install!))
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; ── the lattice is pure data — no env needed ─────────────────────────────────────────────────────
(deftest lattice-lub
  (testing "∂ propagates, async dominates, clocks must agree (else a resampling seam)"
    (is (= true  (:diff (m/lub m/batch m/diff)))   "batch ⊔ diff = differential")
    (is (= :sync (:sched (m/lub m/batch m/diff)))  "both pull ⇒ stays sync")
    (is (= :async (:sched (m/lub m/async m/diff)))  "one async source ⇒ whole pipeline reactive")
    (is (= true  (:diff (m/lub m/async m/diff)))   "async ⊔ diff = async + differential")
    (is (false? (:resample? (m/lub m/async m/diff))) "same base clock ⇒ no resample")
    (is (true? (:resample? (m/lub m/async {:diff false :sched :async :clock :fast})))
        "two different clocks ⇒ a typed resampling seam (Rhine)")))

(deftest router
  (testing "a composed mode picks its γ-lowering"
    (is (= :batch-fuse        (m/route m/batch)))
    (is (= :reactive          (m/route m/async)))
    (is (= :incremental       (m/route m/diff)))
    (is (= :async-incremental (m/route (m/lub m/async m/diff)))
        "streamed differential join ⇒ async incremental (DBSP view on the spindel substrate)")))

;; ── mode-of-type reads the kernel type head (no whnf) ────────────────────────────────────────────
(deftest mode-from-type-head
  (when (ready?)
    (testing "the element type's head constant traces the computational mode"
      (let [natT (e/const' (nm "Nat") [])
            listNat (e/app (e/const' (nm "List") [z]) natT)
            strmNat (e/app (e/const' (nm "Strm") []) natT)
            zsetNat (e/app (e/const' (nm "Zset") []) natT)]
        (is (= m/batch (m/mode-of-type listNat)) "List → batch")
        (is (= m/async (m/mode-of-type strmNat)) "Strm → async (reactive source)")
        (is (= m/diff  (m/mode-of-type zsetNat)) "Zset → differential")))))

;; ── the ONE admitted law + the modality/zero defs are kernel-checked ─────────────────────────────
(deftest kernel-constants-installed
  (when (ready?)
    (testing "Box (□ batch modality), Zzero (empty Z-set), and the diff×async law all check-constant"
      (doseq [n ["Box" "Zzero" "Mode.diff_async_dist"]]
        (is (some? (kenv/lookup (a/env) (nm n))) (str n " present + kernel-verified")))
      (is (not (.isAxiom (kenv/lookup (a/env) (nm "Mode.diff_async_dist"))))
          "the diff×async distributive law is now a PROVEN theorem (induction via Strm.scan_step), not an axiom")
      (is (not (.isAxiom (kenv/lookup (a/env) (nm "Zzero")))) "Zzero is a real def, not an axiom"))))

;; a synthetic plan-lens: source ⋈ source → filter → sum  (the shape term->plan produces for a streamed
;; join pipeline). differentiate consumes the plan IR; :node carries the (here-omitted) kernel-term fns.
(defn- demo-plan []
  (let [src {:op :source :term nil}]
    {:op :foldl :fn nil :init nil
     :input {:op :filter :pred nil
             :input {:op :join :kf nil :lf nil :left src :right src}}}))

(deftest differentiate-structure-and-certificate
  (when (ready?)
    (testing "∂ lowers the plan to join-first stages and cites the right kernel law per stage"
      (let [dr (m/differentiate (demo-plan) m/async)]
        (is (= [:join :filter :sum] (mapv :stage (:stages dr))) "join becomes the base stage; linear ops follow")
        (is (= :async-incremental (:route dr)) "streamed differential ⇒ async-incremental lowering")
        (is (= {:diff true :sched :async :clock :base} (select-keys (:mode dr) [:diff :sched :clock]))
            "the ∂ pass IS the diff modality — sets :diff true, preserves the async clock")
        (let [by-stage (into {} (map (juxt :stage identity)) (:stages dr))]
          (is (true?  (:proven? (by-stage :join)))  "the join is PROVEN incremental")
          (is (contains? (set (:cert (by-stage :join))) "Zproduct_product_rule") "join cites the bilinear differential")
          (is (contains? (set (:cert (by-stage :join))) "Strm.joinCount2_step") "async join also cites the streamed recurrence")
          (is (true? (:proven? (by-stage :filter))) "the linear filter rides the now-PROVEN distributive law")
          (is (= :linearity (:obligation (by-stage :filter))) "its remaining per-op obligation is a linearity witness")
          (is (= ["Mode.diff_async_dist"] (:cert (by-stage :sum))) "sum cites the diff×async distributive law"))
        (is (true? (:all-proven? dr)) "every stage's licensing law is kernel-proven")
        (let [c (m/certificate dr)]
          (is (str/includes? c "async-incremental"))
          (is (str/includes? c "Zproduct_product_rule"))
          (is (str/includes? c "★") "the kernel-proven marker appears")
          (is (str/includes? c "obligation: linearity") "linear stages note their per-op linearity witness"))))))

(deftest differentiate-runs-incrementally-equals-batch
  (when (ready?)
    (testing "the ∂-lowered query RUNS incrementally and matches the batch recompute at every step"
      (let [custs {{:id 1 :name "Ann" :tier :premium} 1 {:id 2 :name "Bo" :tier :basic} 1}
            deltas [[{} custs]
                    [{{:cid 1 :amt 100} 1} {}]        ; Ann (premium) buys 100
                    [{{:cid 2 :amt 50}  1} {}]        ; Bo (basic) — filtered out
                    [{{:cid 1 :amt 30}  1} {}]        ; Ann +30
                    [{{:cid 1 :amt 100} -1} {}]]      ; retract Ann's first order
            premium? (fn [[_o c]] (= :premium (:tier c)))
            revenue  (fn [[o _c]] (:amt o))
            dr   (m/differentiate (demo-plan) m/async)
            ;; runtime impls parallel to the ∂ stages: [kf lf] for the join, then the linear fns
            run  (m/to-zset-query dr [[:cid :id] premium? revenue])
            inc  (run deltas)
            bat  (->> (zs/batch-join :cid :id deltas)
                      (map #(zs/z-sum revenue (zs/z-filter premium? %))))]
        (is (= [0 100 100 130 30] (vec inc)) "premium running revenue (basic filtered; retraction drops it)")
        (is (= (vec inc) (vec bat)) "∂-pass incremental query == batch recompute at every step")))))

(deftest auto-codegen-leaf-fns
  (when (ready?)
    (testing "kernel-term leaf fns CODEGEN to runnable Clojure fns — incrementalize needs no hand impls"
      (let [natT   (e/const' (nm "Nat") [])
            prodNN (e/app* (e/const' (nm "Prod") [z z]) natT natT)
            fst    (fn [body] (e/app* (e/const' (nm "Prod.fst") [z z]) natT natT body))
            idNat  (e/lam "x" natT (e/bvar 0) :default)                          ; kf = lf = identity
            pred   (e/lam "p" prodNN (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 5) (fst (e/bvar 0))) :default) ; fst ≥ 5
            mapf   (e/lam "p" prodNN (fst (e/bvar 0)) :default)                  ; project fst
            plan   {:op :map :fn mapf
                    :input {:op :filter :pred pred
                            :input {:op :join :kf idNat :lf idNat :left {:op :source} :right {:op :source}}}}
            inc    (m/incrementalize (a/env) plan m/async)
            deltas [[{3 1 7 1} {3 1 7 1}] [{9 1} {9 1}] [{4 1} {4 1}]]
            auto   (vec ((:run inc) deltas))
            ;; equivalent hand-written fns — identity keys, fst≥5, project fst
            hand   (vec ((m/to-zset-query (:diff inc) [[identity identity] (fn [[a _]] (<= 5 a)) (fn [[a _]] a)]) deltas))]
        (is (= [:join :filter :map] (mapv :stage (:stages (:diff inc)))))
        (is (= auto hand) "codegen'd leaf fns (Prod.fst↦nth0, Nat.ble↦<=) == hand-written equivalents")
        (is (= {7 1} (first auto)) "join id∘filter(fst≥5)∘map fst over {3,7} ⇒ {7}")
        (is (= {7 1 9 1} (last auto)) "after +9 and +4: {7,9} survive (4<5 filtered)")))))

(deftest route-surface-by-source-type
  (when (ready?)
    (testing "the SOURCE TYPE selects the lowering — mode wired into the surface front door"
      (let [natT (e/const' (nm "Nat") [])
            src  (e/fvar 1)
            listRow (e/app (e/const' (nm "List") [z]) natT)
            zsetRow (e/app (e/const' (nm "Zset") []) natT)
            strmZ   (e/app (e/const' (nm "Strm") []) zsetRow)
            elab (fn [ty] {:term src :lctx {0 {:type ty}}})
            r-list (m/route-surface (a/env) (elab listRow))
            r-zset (m/route-surface (a/env) (elab zsetRow))
            r-strm (m/route-surface (a/env) (elab strmZ))]
        (is (= :batch-fuse        (:route r-list)) "List source ⇒ batch fusion")
        (is (= :incremental       (:route r-zset)) "Zset source ⇒ pull-driven incremental")
        (is (= :async-incremental (:route r-strm)) "Strm(Zset) = a stream of changes ⇒ async incremental")
        (is (false? (:diff (:mode r-list))) "List is not differential")
        (is (true?  (:diff (:mode r-strm))) "a stream of Z-set changes is differential + async")))))

(deftest route-surface-batch-runnable
  ;; UNIFY THE ENTRY POINT: route-surface now yields a `:run` for BATCH too (not only incremental) —
  ;; one type-driven front door produces a runnable in every mode.
  (when (ready?)
    ((requiring-resolve 'wandler.kmap/install!))
    ((requiring-resolve 'wandler.rel-laws/install!))
    ((requiring-resolve 'wandler.collections/install!))
    (let [natT (e/const' (nm "Nat") [])
          listNat (e/app (e/const' (nm "List") [z]) natT)
          xs (e/fvar 1)
          ;; (List.foldl Nat.add Nat.zero xs) — a real batch query (sum a list)
          term (e/app* (e/const' (nm "List.foldl") [z z]) natT natT
                       (e/const' (nm "Nat.add") []) (e/const' (nm "Nat.zero") []) xs)
          r (m/route-surface (a/env) {:term term :lctx {1 {:name "xs" :type listNat}}})]
      (is (= :batch-fuse (:route r)) "List source ⇒ batch route")
      (is (fn? (:run r)) "batch route now produces a runnable (one front door for all modes)")
      (is (= 10 ((:run r) [1 2 3 4])) "and the batch runnable executes correctly"))))

(deftest cost-gated-rebuilder
  (testing "incremental only pays off when |Δ| ≪ base (pure cost model)"
    (is (= :incremental (m/choose-rebuilder {:base-size 1000 :delta-size 5 :fanout 1})))
    (is (= :batch-fuse  (m/choose-rebuilder {:base-size 1000 :delta-size 900 :fanout 2})))
    (is (= :incremental (m/choose-rebuilder {:base-size 1000 :delta-size 100 :fanout 1}))))
  (when (ready?)
    (testing "route-surface downgrades a differential source to recompute when Δ is large"
      (let [zsetRow (e/app (e/const' (nm "Zset") []) (e/const' (nm "Nat") []))
            elab {:term (e/fvar 1) :lctx {0 {:type zsetRow}}}
            small (m/route-surface (a/env) elab :sizes {:base-size 1000 :delta-size 5})
            large (m/route-surface (a/env) elab :sizes {:base-size 1000 :delta-size 600 :fanout 2})]
        (is (= :incremental (:route small)) "small Δ keeps the differential incremental view")
        (is (true? (:diff (:mode small))))
        (is (not= :incremental (:route large)) "large Δ downgrades to recompute")
        (is (true? (:cost-downgraded? large)) "the cost gate flags the downgrade")
        (is (false? (:diff (:mode large))) "downgraded mode is no longer differential")))))

(deftest resample-clock-seam
  (when (ready?)
    (testing "resampling a fast Δ-stream to a slow clock (accumulate) == fast run sampled at slow ticks"
      (let [custs {{:id 1} 1 {:id 2} 1}
            deltas [[{} custs]                         ; 4 fast Δ batches
                    [{{:cid 1 :amt 10} 1} {}]
                    [{{:cid 2 :amt 20} 1} {}]
                    [{{:cid 1 :amt 5} 1} {}]]
            run    (zs/query [[:join :cid :id]])
            fast   (vec (run deltas))
            tick?  (m/every-nth 2)                     ; slow clock fires at fast indices 1 and 3
            slow   (vec (run (m/resample-deltas tick? deltas)))
            sampled (vec (keep-indexed (fn [i v] (when (tick? i) v)) fast))]
        (is (= 2 (count slow)) "slow clock fires twice over 4 fast ticks")
        (is (= sampled slow) "accumulate-resampled slow-clock views == fast run sampled at the ticks")))))

(deftest incrementalize-live-graph
  (when (ready?)
    (testing "the kernel ∂ pipeline ALSO lowers to a live PUSH graph (incrementalize :live?) == the pull query"
      (let [natT   (e/const' (nm "Nat") [])
            prodNN (e/app* (e/const' (nm "Prod") [z z]) natT natT)
            fst    (fn [b] (e/app* (e/const' (nm "Prod.fst") [z z]) natT natT b))
            idNat  (e/lam "x" natT (e/bvar 0) :default)
            pred   (e/lam "p" prodNN (e/app* (e/const' (nm "Nat.ble") []) (e/lit-nat 5) (fst (e/bvar 0))) :default)
            mapf   (e/lam "p" prodNN (fst (e/bvar 0)) :default)
            plan   {:op :map :fn mapf
                    :input {:op :filter :pred pred
                            :input {:op :join :kf idNat :lf idNat :left {:op :source} :right {:op :source}}}}
            pull   (m/incrementalize (a/env) plan m/async)
            live   (m/incrementalize (a/env) plan m/async :live? true)
            in     (atom nil)
            _      (live/drive! in live)
            deltas [[{3 1 7 1} {3 1 7 1}] [{9 1} {9 1}] [{4 1} {4 1}]]
            pull-traj (vec ((:run pull) deltas))
            live-traj (atom [])]
        (doseq [d deltas] (reset! in d) (swap! live-traj conj @(:out live)))
        (is (= pull-traj @live-traj) "kernel-grounded live push-graph == incremental pull-query at every event")
        (is (every? #(= :verified (:payload %)) (:report live)) "all leaves codegen'd from kernel terms ⇒ verified")))))

(deftest foreign-fn-as-axiom
  (when (ready?)
    (testing "a black-box fn is admitted as a typed boundary axiom; the coach detects + flags it trusted"
      (let [natT (e/const' (nm "Nat") [])
            _  (m/register-foreign! a/ansatz-env 'customer-summary natT natT (fn [x] (inc x)))
            ci (kenv/lookup (a/env) (nm "customer-summary"))]
        (is (some? ci))
        (is (.isAxiom ci) "the foreign fn is a typed AXIOM (trusted boundary), not a verified def")
        (is (true?  (m/references-axiom? (a/env) (e/app (e/const' (nm "customer-summary") []) (e/fvar 1))))
            "references-axiom? detects the black-box boundary inside a pipeline term")
        (is (false? (m/references-axiom? (a/env) (e/app (e/const' (nm "Nat.succ") []) (e/fvar 1))))
            "a verified leaf (Nat.succ) is not flagged as trusted")
        (is (contains? @m/foreign-registry "customer-summary") "its runtime fn is registered for codegen")))))

(deftest live-runs-foreign-leaf
  (when (ready?)
    (testing "a kernel ∂ pipeline with a BLACK-BOX leaf (admitted axiom) RUNS — codegen resolves the foreign fn"
      (let [natT   (e/const' (nm "Nat") [])
            prodNN (e/app* (e/const' (nm "Prod") [z z]) natT natT)
            idNat  (e/lam "x" natT (e/bvar 0) :default)
            ;; a third-party black box: pair-sum : Prod Nat Nat → Nat, runtime (fn [[a b]] (+ a b))
            _    (m/register-foreign! a/ansatz-env 'pair-sum prodNN natT (fn [[a b]] (+ a b)))
            mapf (e/lam "p" prodNN (e/app (e/const' (nm "pair-sum") []) (e/bvar 0)) :default)  ; map pair-sum
            plan {:op :map :fn mapf
                  :input {:op :join :kf idNat :lf idNat :left {:op :source} :right {:op :source}}}
            live (m/incrementalize (a/env) plan m/async :live? true)
            in   (atom nil)
            _    (live/drive! in live)]
        (reset! in [{3 1 7 1} {3 1 7 1}])
        (is (= {6 1 14 1} @(:out live))
            "join id∘map(pair-sum) over {3,7}: [3 3]→6, [7 7]→14 — the BLACK-BOX fn executed in the certified graph")
        (is (= :trusted  (:payload (last (:report live))))  "the foreign leaf is reported trusted (admitted axiom)")
        (is (= :verified (:payload (first (:report live)))) "the join (idNat) is verified")))))

(deftest value-pipeline-edn-aligned
  (when (ready?)
    (testing "EDN keyword-maps flow through the certified incremental engine over the kernel-native Value rep"
      ((requiring-resolve 'wandler.edn/install-core!))
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
