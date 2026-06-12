;; Wandler demo — verified data pipelines on the ansatz CIC kernel.
;;
;; Run:  clj -M:repl  →  (load-file "dev/demo.clj")  (or evaluate act by act)
;;
;; The through-line: you write ORDINARY Clojure. It elaborates to a CIC kernel
;; term (the term IS the query plan), the optimizer rewrites it, and the KERNEL
;; certifies every adopted rewrite — `optimized ≡ original` is a theorem checked
;; by the same checker that admits Mathlib. Then it lowers to fast Clojure.
;; The search is untrusted; only the certificate is. A bad rewrite is rejected,
;; never miscompiled.

(require '[ansatz.core :as a])
(binding [a/*verbose* false]
  (a/init! "test-data/init-store" "init"))   ;; the full Lean Init env (~40ms, lazy store)
(require '[wandler.core :as w]
         '[wandler.rel-laws :as laws])
(w/install!)        ;; fills ansatz's three seams: surface verbs · optimizer hook · runtime lowering

;; ═══════════════════════════════════════════════════════════════════════════
;; ACT 1 — verified rewrites: fusion with a kernel certificate
;; ═══════════════════════════════════════════════════════════════════════════

(binding [a/*verbose* false]
  (eval '(ansatz.core/defn big-squares [xs :- (List Nat)] (List Nat)
           (map (fn [x] (* x x)) (filter (fn [x] (< 2 x)) xs)))))

(big-squares '(1 2 3 4 5))      ;; => (9 16 25) — an ordinary Clojure fn
(w/explain "big-squares")
;; => {:verified? true, :changed? true,
;;     :rewrites ["List.map_filter_filterMap"],
;;     :stages-before ["map" "filter"], :stages-after ["filterMap"],
;;     :passes-before 2, :passes-after 1}
;;
;; Two passes became one. The rewrite is not a trusted rule: THIS program's
;; fused term was proven equal to THIS program's naive term, in the kernel
;; (translation validation). :verified? is the kernel's verdict.

;; ═══════════════════════════════════════════════════════════════════════════
;; ACT 2 — transducers/reducers, re-executed under a certificate
;; ═══════════════════════════════════════════════════════════════════════════
;; Idiomatic transducer code is just another spelling of the same pipeline IR —
;; it desugars, fuses, certifies, and runs like Act 1.

(binding [a/*verbose* false]
  (eval '(ansatz.core/defn sum-big-squares [xs :- (List Nat)] Nat
           (transduce (comp (filter (fn [x] (< 2 x))) (map (fn [x] (* x x)))) + 0 xs))))

(sum-big-squares '(1 2 3 4 5))  ;; => 50
(w/explain "sum-big-squares")   ;; the whole stack fused into a single fold
;; A fold over a PROVEN associative monoid (+,0) may additionally lower to the
;; parallel fork-join apfoldl — the associativity proof is the licence to
;; re-associate. Verification licenses the fast representation.

;; ═══════════════════════════════════════════════════════════════════════════
;; ACT 3 — the planner: relational rewrites, certified per plan
;; ═══════════════════════════════════════════════════════════════════════════

;; joins + aggregation are the same surface
(binding [a/*verbose* false]
  (eval '(ansatz.core/defn rev-by-user
           [users :- (List (Prod Nat Nat)), orders :- (List (Prod Nat Nat))] Nat
           (reduce + 0 (map (fn [p] (second (second p)))
                            (join first first users orders))))))
(rev-by-user '([1 10] [2 20]) '([1 5] [1 7] [2 9]))  ;; => 21
(w/explain "rev-by-user")   ;; map fused into the fold over the join

;; install the PROVEN relational law library (each law is a kernel theorem,
;; proved once here, ~5s) — this is the optimizer's rule set, with receipts
(binding [a/*verbose* false] (laws/install!))

;; a naive O(n·m) membership scan…
(binding [a/*verbose* false]
  (eval '(ansatz.core/defn only-known [xs :- (List Nat), ys :- (List Nat)] (List Nat)
           (filter (fn [x] (member x ys)) xs))))
(only-known '(1 2 3 4) '(2 4))  ;; => [2 4]
(w/explain "only-known")
;; => {:verified? true, :changed? true,
;;     :rewrites ["List.elem_filter_eq_index_probe"], …}
;;
;; …became a build-once hash-index SEMIJOIN — the classic planner move, except
;; the plan ships with a proof. Selectivity/size profiles plug into the same
;; cost model (wandler.optimize/optimize-cost :selectivity …): measure at
;; runtime, re-plan, re-certify — the JIT loop where every plan is checked.

;; ═══════════════════════════════════════════════════════════════════════════
;; ACT 4 — batch · incremental (DBSP) · stream: the TYPE picks the mode
;; ═══════════════════════════════════════════════════════════════════════════
;; The same logical pipeline reads as a batch job over List, an incremental
;; view over Z-sets (deltas with deletions, DBSP), or a windowed computation
;; over an infinite stream — see wandler.zset / wandler.dbsp / wandler.stream
;; (each law in those algebras is kernel-proven the same way).
