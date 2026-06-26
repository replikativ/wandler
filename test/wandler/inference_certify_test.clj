(ns wandler.inference-certify-test
  "The A→B bridge: `certify/certified-eliminate` is a drop-in for
   `(semiring/factor-marginalize sr v (semiring/factor-join sr f1 f2))` that additionally carries a
   per-run kernel certificate (`Map.foldl_join_factor`). We check the certified result EQUALS the
   reference `semiring/faq` value-level computation, and that the rewrite verified."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [wandler.core :as wc] [wandler.kmap :as km]
            [wandler.inference.semiring :as sr]
            [wandler.inference.certify :as certify]
            [wandler.laws.tropical :as trop]
            [wandler.test-env :as test-env]))

(defn- setup [f]
  (when-let [k @test-env/init-full-env]
    (reset! a/ansatz-env k) (wc/install!) (km/install!) (wc/install-laws!)
    (trop/install!))                          ; the ℕ∞ (ENat) carrier for the tropical cross-validation
  (f))
(clojure.test/use-fixtures :once setup)
(defn- ready? [] (some? @test-env/init-full-env))

;; the cross-engine demo's factor graph: φ₁(channel,region), φ₂(channel,highvalue), eliminate channel.
(def ^:private f1 (sr/factor [:c :r] {{:c 0 :r 0} 3, {:c 0 :r 1} 1, {:c 1 :r 0} 1, {:c 1 :r 1} 2}))
(def ^:private f2 (sr/factor [:c :h] {{:c 0 :h 0} 1, {:c 0 :h 1} 4, {:c 1 :h 0} 3, {:c 1 :h 1} 1}))

(deftest certified-elimination-matches-faq
  (if-not (ready?)
    (is true "skipped — needs the full Init env")
    (let [ref (sr/factor-marginalize sr/counting :c (sr/factor-join sr/counting f1 f2))
          got (certify/certified-eliminate :c f1 f2)]
      (testing "the elimination step is kernel-certified"
        (is (:verified? got) "factored ≡ naive — the variable-elimination certificate")
        (is (some #{:fold-factor} (:rewrites got)) "the aggregation-through-join factorization fired"))
      (testing "and it computes exactly what semiring/faq computes (a drop-in)"
        (is (= (:vars ref) (:vars (:factor got))) "same surviving variables {:r :h}")
        (is (= (:rel ref) (:rel (:factor got))) "same marginal factor, value for value")))))

(deftest multi-step-chain-one-composed-certificate
  ;; Option C: a 2-elimination chain composed into ONE check-constant'd kernel theorem
  ;;   ∀ f1 f2 f3, whole-naive ≡ whole-factored
  ;; threading each step's output factor into the next purely as a kernel term (Map.entries) — no
  ;; trusted runtime hand-off. Single-var intermediate: f1(s,k), f2(s) → τ(k) ; f3(k,m) → result(m).
  (if-not (ready?)
    (is true "skipped")
    (let [c   certify/counting
          l1  (certify/base-layout c [:s :k] 101)
          l2  (certify/base-layout c [:s]    102)
          s1  (certify/certify-step c l1 l2 :s 201)               ; f1[s,k] ⋈ f2[s] → Map k S
          l3  (certify/base-layout c [:k :m] 103)
          s2  (certify/certify-step c (:out-layout s1) l3 :k 202) ; τ[k] ⋈ f3[k,m] → Map m S
          r   (certify/chain-certificate [s1 s2] "WChain.test_2step")]
      (is (:verified? s1) "step 1 per-run certified")
      (is (:verified? s2) "step 2 per-run certified")
      (is (:verified? r) "the COMPOSED 2-step chain proof is admitted by check-constant")
      (is (nil? (:error r)) (str "no composition error: " (:error r))))))

(deftest multi-step-chain-composite-key-intermediate
  ;; The layout generalization: the intermediate factor keeps TWO variables (a composite Prod key),
  ;; and still threads into the next step as a kernel term. Markov-ish chain
  ;;   f1(a,b), f2(b,c) ; eliminate b keep {a,c} → τ(a,c)  [composite key]
  ;;   f3(c,d)          ; eliminate c keep {a,d} → result(a,d)
  ;; composed into ONE admitted kernel theorem.
  (if-not (ready?)
    (is true "skipped")
    (let [c   certify/counting
          l1  (certify/base-layout c [:a :b] 301)
          l2  (certify/base-layout c [:b :c] 302)
          s1  (certify/certify-step c l1 l2 :b 401)               ; → Map (Prod a c) S
          l3  (certify/base-layout c [:c :d] 303)
          s2  (certify/certify-step c (:out-layout s1) l3 :c 402) ; τ(a,c) ⋈ f3(c,d) → Map (Prod a d) S
          r   (certify/chain-certificate [s1 s2] "WChain.test_composite")]
      (is (= [:a :c] (:kept-vars s1)) "intermediate keeps a composite (a,c) key")
      (is (:verified? s1) "step 1 certified (composite-key output)")
      (is (:verified? s2) "step 2 certified (composite-key input threaded)")
      (is (:verified? r) "COMPOSED chain over a composite-key intermediate is admitted")
      (is (nil? (:error r)) (str "no composition error: " (:error r))))))

(deftest n-step-chain-three-eliminations
  ;; N-step driver: a 3-elimination chain (each step keeps a composite key carried through) composed
  ;; into ONE admitted theorem. f1(a,b) f2(b,c) →[b] τ1(a,c) ; f3(c,d) →[c] τ2(a,d) ; f4(d,e) →[d] (a,e).
  (if-not (ready?)
    (is true "skipped")
    (let [c   certify/counting
          s1  (certify/certify-step c (certify/base-layout c [:a :b] 501) (certify/base-layout c [:b :c] 502) :b 601)
          s2  (certify/certify-step c (:out-layout s1) (certify/base-layout c [:c :d] 503) :c 602)
          s3  (certify/certify-step c (:out-layout s2) (certify/base-layout c [:d :e] 504) :d 603)
          r   (certify/chain-certificate [s1 s2 s3] "WChain.test_3step")]
      (is (every? :verified? [s1 s2 s3]) "all 3 steps per-run certified")
      (is (:verified? r) "the COMPOSED 3-step chain proof is admitted by check-constant")
      (is (nil? (:error r)) (str "no composition error: " (:error r))))))

(deftest certify-faq-chain-matches-semiring-faq
  ;; The engine front-end: ingest {:vars :rel} factors forming a chain, auto-derive the elimination
  ;; order, run the whole chain backed by ONE check-constant'd certificate, and get the SAME marginal
  ;; as semiring/faq. f1(a,b) f2(b,c) f3(c,d), keep {a,d} → eliminate b,c.
  (if-not (ready?)
    (is true "skipped")
    (let [f1 (sr/factor [:a :b] {{:a 0 :b 0} 2, {:a 0 :b 1} 1, {:a 1 :b 0} 3, {:a 1 :b 1} 1})
          f2 (sr/factor [:b :c] {{:b 0 :c 0} 1, {:b 0 :c 1} 2, {:b 1 :c 0} 4, {:b 1 :c 1} 1})
          f3 (sr/factor [:c :d] {{:c 0 :d 0} 3, {:c 0 :d 1} 1, {:c 1 :d 0} 1, {:c 1 :d 1} 2})
          got (certify/certify-faq certify/counting [f1 f2 f3] #{:a :d} "WFaq.chain3")
          ref (sr/faq sr/counting [:a :d] (:order got) [f1 f2 f3])]
      (is (= #{:b :c} (set (:order got))) "auto-derived (min-degree) elimination order eliminates b,c")
      (is (:verified? got) "the whole-chain certificate is admitted by check-constant")
      (is (= (:vars ref) (:vars (:factor got))) "same surviving variables {:a :d}")
      (is (= (:rel ref) (:rel (:factor got))) "certified FAQ == semiring/faq, value for value"))))

(deftest certify-faq-bool-existence-carrier
  ;; OTHER CARRIER #1: the Boolean / existence semiring (⊕=∨, ⊗=∧). A reachability chain
  ;; f1(a,b) f2(b,c) f3(c,d), keep {a,d}, eliminate b,c — the certified factorization must agree
  ;; with semiring/faq at sr/existence value-for-value (a is reachable-to d via SOME b,c path).
  (if-not (ready?)
    (is true "skipped")
    (let [f1 (sr/factor [:a :b] {{:a 0 :b 0} true,  {:a 0 :b 1} false, {:a 1 :b 0} true,  {:a 1 :b 1} true})
          f2 (sr/factor [:b :c] {{:b 0 :c 0} true,  {:b 0 :c 1} true,  {:b 1 :c 0} false, {:b 1 :c 1} true})
          f3 (sr/factor [:c :d] {{:c 0 :d 0} true,  {:c 0 :d 1} false, {:c 1 :d 0} true,  {:c 1 :d 1} true})
          got (certify/certify-faq certify/existence [f1 f2 f3] #{:a :d} "WFaq.bool3")
          ref (sr/faq sr/existence [:a :d] (:order got) [f1 f2 f3])]
      (is (:verified? got) "the whole-chain certificate is admitted at S=Bool")
      (is (= (:vars ref) (:vars (:factor got))) "same surviving variables {:a :d}")
      (is (= (:rel ref) (:rel (:factor got))) "certified reachability == semiring/faq existence, value for value"))))

(deftest certify-faq-tropical-enat-carrier
  ;; OTHER CARRIER #2: the tropical / shortest-path semiring (⊕=min, ⊗=+ over ℕ∞ = ENat). The certified
  ;; factorization must agree with semiring/faq at sr/tropical — the min-cost a→d path summed over b,c.
  (if-not (ready?)
    (is true "skipped")
    (let [f1 (sr/factor [:a :b] {{:a 0 :b 0} 2, {:a 0 :b 1} 5, {:a 1 :b 0} 1, {:a 1 :b 1} 3})
          f2 (sr/factor [:b :c] {{:b 0 :c 0} 1, {:b 0 :c 1} 4, {:b 1 :c 0} 2, {:b 1 :c 1} 1})
          f3 (sr/factor [:c :d] {{:c 0 :d 0} 3, {:c 0 :d 1} 1, {:c 1 :d 0} 2, {:c 1 :d 1} 2})
          got (certify/certify-faq certify/tropical [f1 f2 f3] #{:a :d} "WFaq.tropical3")
          ref (sr/faq sr/tropical [:a :d] (:order got) [f1 f2 f3])]
      (is (:verified? got) "the whole-chain certificate is admitted at S=ENat")
      (is (= (:vars ref) (:vars (:factor got))) "same surviving variables {:a :d}")
      (is (= (:rel ref) (:rel (:factor got))) "certified shortest-path == semiring/faq tropical, value for value"))))

(deftest certify-faq-tree-marginalize-one
  ;; GENERAL GRAPH (#176): keep only {:a}, so the min-degree plan eliminates b,c,d — and `d` is mentioned
  ;; by exactly ONE factor (f3), an arity-1 elimination (marginalize-one, no join, proof=refl). Exercises
  ;; the live-factor fold's degree-1 path + min-degree ordering, certified end-to-end vs semiring/faq.
  (if-not (ready?)
    (is true "skipped")
    (let [f1 (sr/factor [:a :b] {{:a 0 :b 0} 2, {:a 0 :b 1} 1, {:a 1 :b 0} 3, {:a 1 :b 1} 1})
          f2 (sr/factor [:b :c] {{:b 0 :c 0} 1, {:b 0 :c 1} 2, {:b 1 :c 0} 4, {:b 1 :c 1} 1})
          f3 (sr/factor [:c :d] {{:c 0 :d 0} 3, {:c 0 :d 1} 1, {:c 1 :d 0} 1, {:c 1 :d 1} 2})
          got (certify/certify-faq certify/counting [f1 f2 f3] #{:a} "WFaq.tree1")
          ref (sr/faq sr/counting [:a] (:order got) [f1 f2 f3])]
      (is (= #{:b :c :d} (set (:order got))) "eliminates b,c,d — d via arity-1 marginalize-one")
      (is (:verified? got) "the whole-graph certificate is admitted (incl. the marginalize-one step)")
      (is (= (:rel ref) (:rel (:factor got))) "certified == semiring/faq, value for value"))))

(deftest certify-faq-explicit-order-override
  ;; the :order param overrides the min-degree plan; the certificate must still admit and match.
  (if-not (ready?)
    (is true "skipped")
    (let [f1 (sr/factor [:a :b] {{:a 0 :b 0} 2, {:a 1 :b 0} 1, {:a 0 :b 1} 1, {:a 1 :b 1} 3})
          f2 (sr/factor [:b :c] {{:b 0 :c 0} 1, {:b 1 :c 0} 2, {:b 0 :c 1} 3, {:b 1 :c 1} 1})
          f3 (sr/factor [:c :d] {{:c 0 :d 0} 1, {:c 1 :d 0} 2, {:c 0 :d 1} 1, {:c 1 :d 1} 2})
          got (certify/certify-faq certify/counting [f1 f2 f3] #{:a :d} "WFaq.ord" :order [:b :c])
          ref (sr/faq sr/counting [:a :d] [:b :c] [f1 f2 f3])]
      (is (= [:b :c] (:order got)) "honored the explicit elimination order")
      (is (:verified? got))
      (is (= (:rel ref) (:rel (:factor got))) "explicit-order certified FAQ == semiring/faq"))))

(deftest certify-faq-star-arity3-multiway
  ;; #177: a variable shared by 3 factors (a STAR) — eliminating it is a multi-way (arity-3) join, built as
  ;; a left-nested Map.join chain and factored join-by-join by try-fold-factor*. Certified end-to-end and
  ;; equal to semiring/faq (the result is the full a×b×c cross product, here 8 rows).
  (if-not (ready?)
    (is true "skipped")
    (let [s1 (sr/factor [:v :a] {{:v 0 :a 0} 2, {:v 0 :a 1} 1, {:v 1 :a 0} 3, {:v 1 :a 1} 1})
          s2 (sr/factor [:v :b] {{:v 0 :b 0} 1, {:v 0 :b 1} 4, {:v 1 :b 0} 2, {:v 1 :b 1} 1})
          s3 (sr/factor [:v :c] {{:v 0 :c 0} 3, {:v 0 :c 1} 1, {:v 1 :c 0} 1, {:v 1 :c 1} 2})
          got (certify/certify-faq certify/counting [s1 s2 s3] #{:a :b :c} "WFaq.star3")
          ref (sr/faq sr/counting [:a :b :c] (:order got) [s1 s2 s3])]
      (is (= [:v] (:order got)) "one elimination of the degree-3 variable")
      (is (:verified? got) "the multi-way (arity-3) elimination is certified")
      (is (= 8 (count (:rel (:factor got)))) "the a×b×c cross product")
      (is (= (:rel ref) (:rel (:factor got))) "certified multi-way FAQ == semiring/faq, value for value"))))

(deftest certify-faq-loop-natural-join
  ;; #179: eliminating a variable whose factors ALSO share another variable (a loop) — a NATURAL join on
  ;; the composite key {v,w}, so the shared `w` is equated (not cross-producted). Map.foldl_join_factor is
  ;; key-agnostic, so the composite-key join still factors. Certified == semiring/faq.
  (if-not (ready?)
    (is true "skipped")
    (let [g1 (sr/factor [:v :w] {{:v 0 :w 0} 1, {:v 1 :w 0} 2, {:v 0 :w 1} 1, {:v 1 :w 1} 1})
          g2 (sr/factor [:v :w] {{:v 0 :w 0} 3, {:v 1 :w 0} 1, {:v 0 :w 1} 2, {:v 1 :w 1} 1})
          got (certify/certify-faq certify/counting [g1 g2] #{:w} "WFaq.loop2")
          ref (sr/faq sr/counting [:w] (:order got) [g1 g2])]
      (is (:verified? got) "the natural-join (composite-key) elimination is certified")
      (is (= (:rel ref) (:rel (:factor got))) "Σ_v g1(v,w)·g2(v,w) == semiring/faq, value for value"))))

(deftest certify-faq-four-cycle
  ;; a loopy graph (4-cycle a–b–c–d–a): min-degree elimination hits a step whose two factors share TWO
  ;; variables (the natural join). Certified end-to-end and equal to semiring/faq.
  (if-not (ready?)
    (is true "skipped")
    (let [c1 (sr/factor [:a :b] {{:a 0 :b 0} 2, {:a 0 :b 1} 1, {:a 1 :b 0} 1, {:a 1 :b 1} 3})
          c2 (sr/factor [:b :c] {{:b 0 :c 0} 1, {:b 0 :c 1} 2, {:b 1 :c 0} 1, {:b 1 :c 1} 1})
          c3 (sr/factor [:c :d] {{:c 0 :d 0} 1, {:c 0 :d 1} 1, {:c 1 :d 0} 2, {:c 1 :d 1} 1})
          c4 (sr/factor [:d :a] {{:d 0 :a 0} 1, {:d 0 :a 1} 2, {:d 1 :a 0} 1, {:d 1 :a 1} 1})
          got (certify/certify-faq certify/counting [c1 c2 c3 c4] #{:a} "WFaq.cyc4")
          ref (sr/faq sr/counting [:a] (:order got) [c1 c2 c3 c4])]
      (is (:verified? got) "the 4-cycle elimination (incl. a natural-join step) is certified")
      (is (= (:rel ref) (:rel (:factor got))) "certified == semiring/faq, value for value"))))

(defn- rel≈
  "Two factor rels agree within `eps` per assignment (float weights fold in different orders in the kernel
   plan vs semiring/faq, so compare with tolerance — the per-run certificate is the exact guarantee)."
  [a b eps]
  (and (= (set (keys a)) (set (keys b)))
       (every? (fn [[k v]] (< (abs (- (double v) (double (b k)))) eps)) a)))

(deftest certify-faq-probability-float-carrier
  ;; #51 (inference half): a FLOAT probability carrier. Map.foldl_join_factor is order-preserving, so it
  ;; certifies at S=Float with NO algebra (Float need not be a lawful semiring) — `factored ≡ naive` holds
  ;; because the two folds are bit-identical. The unnormalized marginal matches semiring/faq's.
  (if-not (ready?)
    (is true "skipped")
    (let [p1 (sr/factor [:a :b] {{:a 0 :b 0} 0.3, {:a 0 :b 1} 0.7, {:a 1 :b 0} 0.5, {:a 1 :b 1} 0.5})
          p2 (sr/factor [:b :c] {{:b 0 :c 0} 0.2, {:b 0 :c 1} 0.8, {:b 1 :c 0} 0.6, {:b 1 :c 1} 0.4})
          p3 (sr/factor [:c :d] {{:c 0 :d 0} 0.1, {:c 0 :d 1} 0.9, {:c 1 :d 0} 0.5, {:c 1 :d 1} 0.5})
          got (certify/certify-faq certify/probability [p1 p2 p3] #{:a :d} "WFaq.prob3")
          ref (sr/faq sr/probability [:a :d] (:order got) [p1 p2 p3])]
      (is (:verified? got) "the whole-chain certificate is admitted at S=Float")
      (is (= (:vars ref) (:vars (:factor got))) "same surviving variables {:a :d}")
      (is (rel≈ (:rel ref) (:rel (:factor got)) 1e-9) "certified Float marginal ≈ semiring/faq probability"))))

(deftest certified-elimination-keeping-one-variable
  ;; degenerate composite key (a single kept var) still goes through the same general path.
  (if-not (ready?)
    (is true "skipped")
    (let [g1 (sr/factor [:c :r] {{:c 0 :r 0} 2, {:c 1 :r 0} 5, {:c 0 :r 1} 1})
          g2 (sr/factor [:c] {{:c 0} 10, {:c 1} 3})
          ref (sr/factor-marginalize sr/counting :c (sr/factor-join sr/counting g1 g2))
          got (certify/certified-eliminate :c g1 g2)]
      (is (:verified? got))
      (is (= (:rel ref) (:rel (:factor got))) "single kept var :r, certified == faq"))))
