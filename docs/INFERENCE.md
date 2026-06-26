# Inference — sum-product over a chosen semiring

A surprising amount of "different" computation is **one** computation: a sum-product over a
semiring. Counting query answers, set semantics, shortest paths, provenance, and *probabilistic
inference* are all `⊕`-combine-the-`⊗`-products — they differ only in which semiring `S` you
plug in. Wandler makes that literal: `Rel A S := A → S`, one relational algebra parameterized
over `S` (`wandler.inference.semiring`). And the optimizer's headline — **aggregation-through-join
factorization** — *is* variable elimination, so the kernel proof that the join need never be
built is the elimination certificate.

The split that keeps it honest: the **symbolic** part (which paths exist, the provenance
formula, the semiring laws) is L0-proven; the **numbers** (a probability, a weighted model
count) are an L2 trusted oracle, differentially cross-checked.

> Setup: `(require '[wandler.inference.semiring :as sr] '[wandler.inference.wmc :as wmc]
> '[wandler.inference.dist :as dist] '[wandler.inference.certify :as cert])`. The semiring core
> is plain Clojure; `certify` additionally needs the kernel env + `w/install-laws!`.

## One algebra, many domains

A **factor** is `{:vars #{…} :rel {assignment → weight}}`. The same query — two edge factors,
eliminate the middle variable `:m` — computes a *different thing* per semiring:

```clojure
(defn f [vars rel] {:vars (set vars) :rel rel})

;; counting: how many 2-hop paths 1 ⇝ 9?
(sr/faq sr/counting [:x :y] [:m]
  [(f [:x :m] {{:x 1 :m 2} 1 {:x 1 :m 3} 1})
   (f [:m :y] {{:m 2 :y 9} 1 {:m 3 :y 9} 1})])
;;=> {{:x 1, :y 9} 2}          ; 1→2→9 and 1→3→9

;; tropical (min,+): the SHORTEST 1 ⇝ 9
(sr/faq sr/tropical [:x :y] [:m]
  [(f [:x :m] {{:x 1 :m 2} 5 {:x 1 :m 3} 2})
   (f [:m :y] {{:m 2 :y 9} 1 {:m 3 :y 9} 4})])
;;=> {{:x 1, :y 9} 6}          ; min(5+1, 2+4)
```

`existence` (Bool, ∧/∨) gives reachability; `provenance` gives the Boolean formula behind each
answer (below). The relational operators (`rel-add` `⊕`, `rel-mul` `⊗`, `rel-join`, `rel-sum`)
are generic over the carrier — you change the domain by changing `S`, not the query.

## Variable elimination = certified factorization

Eliminating a variable is `Σ_X ∏(factors mentioning X)` — a **sum over a join** on the shared
variable. That is exactly the shape the optimizer factorizes: the proven `Map.foldl_join_factor`
says the per-key bucket fold equals the fold over the materialized join, so `Σ over (f₁ ⋈ f₂)`
**never builds the product**. `certify-faq` runs the elimination *and carries the kernel proof*
that the factored plan equals the naive one — a drop-in for `factor-marginalize ∘ factor-join`
with a certificate:

```clojure
(def r (cert/certify-faq cert/counting
         [(f [:a :b] {{:a 0 :b 0} 1 {:a 0 :b 1} 2 {:a 1 :b 0} 3 {:a 1 :b 1} 4})
          (f [:b :c] {{:b 0 :c 0} 1 {:b 1 :c 0} 1 {:b 0 :c 1} 1 {:b 1 :c 1} 1})]
         #{:a :c} "chain"))
(:verified? r)   ;;=> true      ; factored ≡ naive, kernel-checked
(:order r)       ;;=> [:b]      ; the elimination order (min-degree)
```

> **✓ proven.** The variable-elimination *certificate* and the FAQ-factorization *certificate*
> are the same theorem. The asymptotic win of VE (never form the `|φ₁|·|φ₂|` joint) is the
> asymptotic win of the factorization — by proof. Today: counting / existence / tropical /
> probability carriers, single shared elimination variable per step; arity-≥3 (a variable shared
> by ≥3 live factors) is the honest open frontier (it reports a clear error, not a wrong answer).

## Probabilistic queries: provenance → WMC

For *probabilities* you can't just multiply along paths — when answers share a fact, the naive
product double-counts the correlation. The exact route is two layers: run the **provenance**
semiring to get a Boolean formula (a DNF over independent fact-ids), then **weighted model count**
it.

```clojure
;; two DISJOINT paths, each an edge with its own fact-id
(def formula
  (get (:rel (sr/faq sr/provenance [:x :y] [:m]
               [(f [:x :m] {{:x 1 :m 2} #{#{:e12}} {:x 1 :m 3} #{#{:e13}}})
                (f [:m :y] {{:m 2 :y 9} #{#{:e29}} {:m 3 :y 9} #{#{:e39}}})]))
       {:x 1 :y 9}))
;;=> #{#{:e12 :e29} #{:e39 :e13}}            ; (e12∧e29) ∨ (e13∧e39)

(wmc/wmc {:e12 0.9 :e29 0.8 :e13 0.5 :e39 0.4} formula)
;;=> 0.776                                   ; 1 − (1−0.9·0.8)(1−0.5·0.4), exact
```

When paths **share** a fact, WMC is exact where a product is wrong:

```clojure
;; two 3-hop paths that share edge [1 2]
(wmc/wmc (zipmap [[1 2] [2 3] [3 9] [2 4] [4 9]] (repeat 0.5))
         #{#{[1 2] [2 3] [3 9]} #{[1 2] [2 4] [4 9]}})
;;=> 0.21875        ; accounts for the shared [1 2]; treating the paths as independent over-counts
```

> **✓ proven symbolic, ⚠ trusted count.** Wandler proves the provenance *algebra* and the WMC
> *homomorphism*; the #P-hard model count itself is the L2 oracle. The pluggable seam
> (`wandler.inference.wmc`) ships `:enumeration` (exact 2ⁿ reference, always present) and
> `:logicng` (a BDD weighted DP, opt-in via the `:logicng` alias, scaling to ~31 facts). A
> compiled backend is **differentially cross-checked** against the enumeration reference on small
> formulas, so a wiring bug surfaces immediately. (`dnf->weighted-cnf` exports MCC-2024 for native
> counters like Ganak/d4 — a documented seam, not yet wired.)

## The monad view: FinSet / FinDist

The same algebra is a **monad** (`wandler.inference.dist`): a branching computation is a finite
weighted map, and `fin-return`/`fin-bind` are the semiring's unit and sum-product. Pick the
semiring and you pick the monad — `existence` → FinSet (the powerset / nondeterminism monad),
`probability` → FinDist (the distribution monad):

```clojure
(def joint
  (dist/fin-bind sr/probability (dist/bernoulli 0.7)
    (fn [cause] (if cause (dist/bernoulli 0.9) (dist/bernoulli 0.2)))))
(dist/prob joint true?)   ;;=> 0.69      ; 0.7·0.9 + 0.3·0.2 — the law of total probability
```

So a probabilistic query's marginal *via the monad* equals its marginal *via provenance→WMC* —
they are the same sum-product two ways. The continuous analogue (the **Giry** monad,
`wandler.inference.giry`) is a sampler-based L2 boundary with `expectation` as its single trusted
seam.

## Recursion is gated by a kernel theorem

A semiring may safely recurse (a transitive closure / datalog fixpoint) iff it **absorbs**:
`a ⊕ (a ⊗ b) = a` (Khamis et al., datalog° POPS). Where Scallop/datalog° *document* a
compatibility matrix, wandler makes the gate a **kernel theorem**:

```clojure
(mapv #(:status (sr/recursion-safe? %)) [sr/existence sr/tropical sr/counting])
;;=> [:certified :provable-pending :unsafe]
```

`Bool.absorptive` (`∨ a (∧ a b) = a`) is proven, so classical datalog recurses safely; counting
absorption fails (`1 + 1·1 = 2 ≠ 1`), so a counting fixpoint is **rejected at the gate** rather
than silently diverging.

> **✓ proven.** `sr/fixpoint` over `existence` runs; over `counting` it throws with `:GATED`,
> citing the missing absorption law. Recursion safety is a property the kernel checked, not a
> footnote.

## Where to go next

- **ENGINES.md** — the *cross-engine* joint inference: factors read from a datahike DB and a
  stratum dataset, eliminated by the same certified factorization.
- **OPTIMIZER.md** — the FAQ factorization family that VE rides on (`try-fold-factor`,
  `Map.foldl_join_factor`).
- **PROGRAMMING_MODEL.md** — the formal account of the semiring view and the measure structure.
