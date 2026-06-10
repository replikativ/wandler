# A Language for Models and Inference — design notes

> Status: **thinking document, to revisit.** Not a spec yet. It exists to answer one worry — *"with too
> much flexibility, modeling tasks become unclear"* — by proposing a small, closed shape that the same
> machine can hold whether the task is "optimize a transduce with DB queries", "run inference over a
> semiring", or "find the non-identifiable subspace of a causal model with Gröbner bases".
>
> Companion to `CORE.md` (the runtime architecture) and `PROGRAMMING_MODEL.md` (the four structures). This
> document is the layer *above* both: what the thing **is for**, and why it is one thing.

---

## 0. The worry, taken seriously

Flexibility is not the goal; flexibility is the risk. A framework that can express anything tells a modeler
nothing about *what to do*. So the design question is not "how much can it express" but **"what is the small,
fixed set of moves, such that every task — a Clojure optimization, a semiring inference, an identifiability
analysis — is the *same* sequence of moves?"**

The claim of this document: there is such a set. It is not a new surface language. It is a **discipline with
four nouns and one verb**, and the apparent diversity of tasks is diversity in *which translation you take*,
not in the workflow.

```
   nouns:   MODEL   ·   VIEW   ·   QUESTION   ·   CLAIM
   verb:    ANALYZE   (translate a model under a view, so a question becomes tractable)
```

A model is a value. A view is an algebraic translation of it. A question is what you pair against it. Analysis
is the act of choosing the translation that makes the pairing cheap. A claim is the answer plus its
certificate. That is the whole language. The rest is making each noun precise and showing the three example
tasks collapse onto it.

---

## 1. Why "language", and which tradition

You picked Clojure for the memory model and metaprogramming, not the libraries — so this is explicitly *not*
"the wandler API." It is the older idea your notes and library have circled for a decade: **a relational
program runs in every direction.** (Your Zotero's centre of mass is bidirectional programming, reversible
computing, functional-logic/relational programming — miniKanren, Curry, Mercury — not "ML frameworks". Your
Axtell note states the thesis directly: *"you need to be able to program completely relationally to go back
and forth in all contexts."*)

A **model** is a relation, not a function. `simulate` is one reading of it (forward); `infer` is another
(backward); `identify` is a third (which inputs the output cannot distinguish). The language's job is to keep
those readings of *one* object coherent, and to let a question pick the cheapest reading. This is the same
move logic programming makes (a predicate is not a function), lifted from data to *models with uncertainty
and dynamics*. The semiring algebra already in the runtime is exactly "programs as relations, weighted" — so
the runtime is a first instance of the language, not the language itself.

> **Resolution of the worry, stated once:** the language is *closed* in its **views** (a fixed menu of
> algebraic translations) and *fixed* in its **workflow** (author → view → analyze → plan → run → record).
> Open-endedness lives only in the model's payloads (your functions) and in which view you ask for — never
> in the grammar. A modeler is never staring at a blank page of possibility; they are choosing a lens.

---

## 2. The model is a value at many resolutions (the tower, with feedback)

A model is not a program at one granularity. It is a **value carrying descriptions at several resolutions**,
with maps between them:

```
        amortised / surrogate     (regression · neural net · LLM prior)        coarse, cheap, approximate
              ▲  α        │ γ
        macro / mean-field        (ODE · aggregate dynamics · factor graph)
              ▲  α        │ γ
        micro / mechanism         (ABM rules · SDE · structural equations)     fine, expensive, faithful
```

- `α : fine → coarse` is the **coarse-graining** map (a group-by-and-aggregate — already an algebra
  operator); `γ : coarse → fine` is the **refinement** map (a lens *put*; usually distribution-valued).
- Each level carries a **validity certificate**: the regime where it is a sound stand-in for the level below
  (an effective-theory cutoff). Exact validity (lumpability / block structure of the transfer operator) is
  kernel-checkable (L0); approximate validity is a measured defect ε (L2).

Two corrections from your notes, against a naïve "reduction hierarchy":

1. **Scales couple; they do not just reduce.** Coarse facts feed *down* (downward causation), and a level may
   *adapt while running*. So `α`/`γ` are a standing two-way correspondence, not a one-shot projection. (Your
   *Normalization Group Theory* note: "the reaction of coarse-grained facts 'downwards' to influence the
   microphysics.")
2. **Disagreement between levels is signal, not error.** When two views of the same system fail to glue, the
   obstruction *localizes the modelling problem* — the sheaf-theoretic reading of your *Dialectics* note
   (contradiction → synthesis). The framework should surface obstructions, not hide them.

This is the missing chapter of the vision (the simm.is pages have the fork primitive but not the levels). It
is also the only known way to make hard inference tractable: **inference that works marginalizes what the
question does not need and computes at the coarsest level that is still valid for that question.**

---

## 3. The fixed menu of VIEWS (the closed part)

A **view** is an algebraic translation of a model into a domain where a particular kind of question is
cheap. This is the heart of the answer to the flexibility worry: **the views are a fixed, small set.** Each
is a faithful lens onto the *same* model value; each comes with the analysis it makes tractable and the trust
level of that analysis.

| view | model becomes a … | the question it answers | machinery | trust |
|---|---|---|---|---|
| **relational / semiring** | weighted relation `Rel A S` | query · count · reachability · shortest-path · provenance · **marginal** (sum-product) | FAQ / variable-elimination, the certified planner | **L0** algebra |
| **operator / spectral** | transfer/Koopman operator | dynamics · **coarse-graining** (slow modes = macro coords) · mixing time · surrogate validity (NTK spectrum) | eigendecomposition, DMD/EDMD/MSM | L2 numeric, L0 lumpability |
| **polynomial / variety** | ideal in `k[θ, obs]` | **identifiability** (fibers of θ → obs); non-identified subspace; sensitivity | Gröbner / Buchberger (GF(p)+FGLM), elimination | L1 symbolic (exact over the field) |
| **differential / geometric** | manifold + Fisher metric | sloppiness · which directions data constrains · the *numeric twin* of identifiability | Jacobian/Hessian spectrum, information geometry | L2 numeric |
| **measure / sampling** | a sampler / kernel | approximate posterior when exact is intractable | SMC · MCMC · amortised SBI (the spindel backend, raster AD) | L2 oracle |
| **causal / interventional** | SCM + do-operator | effects · transportability across levels | string-diagram surgery, do-calculus | L1 structural |

The unification you were reaching for: **identifiability (Gröbner), relevance (sum-product), and validity
(spectral) are the same kind of object — an algebraic translation of one model that exposes structure the
question needs *before* any numerics run.** Your `partial_identifiability` work is the "polynomial view"; it
is not a separate tool, it is one entry in this table. (Its own framing already matches: model in →
ADVI-style automatic *structural report* out, via elimination.) Information geometry (your sloppy-models
holdings) is the *differential* twin of the *polynomial* view — Jacobian rank ↔ fibre dimension; Fisher
spectrum ↔ which Gröbner constraints bite. The framework should let you ask for either and reconcile them.

**Why a closed menu is the right call.** Each view is a *category with known structure and known analyses* —
not a free-form DSL. A modeler chooses among six lenses, each with a documented question-class and certificate
type. New views are added deliberately (each is a research-grade commitment, like adding a kernel primitive),
not improvised. That is the discipline that keeps "flexible" from becoming "unclear".

---

## 4. The QUESTION compiles the MODEL (relevance is an adjoint)

A question is a *functional on the model's outputs* — "the marginal of X", "the cost of plan P", "the effect
of do(I) on Y", "which θ are identified". The first act of the engine on any question is the **backward pass
of that functional through the model**, keeping only what it has nonzero pairing with. This single operation
appears in every tradition you collect, and they are computationally the same:

```
   RG relevant operators  ≡  adjoint sensitivity  ≡  d-separation  ≡  program slicing  ≡  Rao–Blackwell/
   (what survives coarse-graining)  (∂out/∂in)     (what's needed)  (live code)         delayed sampling
```

**Marginalize-by-default falls out of this as plan compilation, not as a sampler trick.** Anglican's delayed
sampling is the local, runtime version; here it is the architecture — the planner computes *what the question
needs*, chooses the coarsest valid level that supplies it, and discards the rest before any number is
produced. This is why the same engine serves the trivial and the deep task: "optimize a transduce with DB
queries" is the question `count`/`reduce` over the relational view with the cost functional as the objective
— and the backward pass is exactly the filter-pushdown/aggregation-factorization the planner already does.
"Run inference" is the question `marginal` over the same view with the semiring swapped to probabilities — and
the backward pass is variable elimination. **Same compilation; different functional.**

The plan that comes back carries three composable quantities (they compose along the plan the way costs
already do): **cost** (compute), **error budget** ε (per level-crossing and per solver — adopt the
probabilistic-numerics stance that a solver *returns a distribution*, so numerical and statistical
uncertainty share one currency), and the **trust ledger** (which steps are L0/L1/L2). The answer is never a
bare number; it is a number *with this certificate*.

---

## 5. optimization = inference = control (one spectrum)

Your notes insist these are not three problems: *"inference is more general than optimization … inference is
equivalent to an optimization problem on a higher-order space of distributions."* The language honours this by
making the **terminal object a decision functional**, of which optimization, inference, and control are the
deterministic, the distributional, and the closed-loop reading:

```
   optimize     argmin_θ  L(θ)                         a point
   infer        argmin_q  KL(q ‖ p) = the posterior    a distribution   (optimization over distributions)
   control      argmin_π  E[ L | π ]                    a policy         (closed loop; VOI chooses next probe)
```

This matters operationally because of **value of information**: the most useful question is often *"which run,
observation, or level-refinement would most change my decision?"* — a functional whose answer schedules the
next fork. In a system whose substrate makes forks free, VOI is what turns the fork primitive from a
mechanism into *deliberation*: it scores which world-branch is worth exploring. (This is where dvergr's
`quorum`/`race` get a principled scoring rule, and where "modeling tool" becomes "deliberation engine".)

---

## 6. The ANSWER is a CLAIM (the unit that composes and is remembered)

What a model run produces — and the only thing that crosses a fork boundary or merges back into shared memory
— is a **claim**: an assertion with a certificate.

```
   under model  M@version,  doing  I,   yields   ΔY ± ε    [view: causal; trust: L2 calibrated 2026-06;
                                                            relevance: {a,b}; identifiable: yes]
```

Three consequences, each load-bearing for the larger purpose (humans and agents organizing themselves):

- **Claims are portable across levels iff interventions commute with α** (causal abstraction: Rubenstein et
  al. 2017; Beckers–Halpern 2019; your held *Multi-Level Cause-Effect Systems*). This is the licence that lets
  an agent reason cheaply at the coarse level and have the conclusion *hold* at the fine level — without it,
  coarse reasoning is unsound, which is fatal for a system built on cheap abstraction.
- **Claims are the merge currency** between agents. Dvergr's proposal mechanism + wandler's certificate are
  the two halves; gluing them defines what agents debate, quorum over, and accumulate. The aggregation of
  conflicting claims is *mechanism design*, not averaging — your "democratic cybernetics / collaborative
  self-modelling" lives here, and it is political, not merely technical.
- **Inference has memory** — the feature no PPL has and your substrate makes free. Every run deposits its
  traces, fitted surrogates, calibrated discrepancies and claims as **provenance-carrying datahike facts**,
  indexed by (model-version, query-class, regime). The next question consults this Bayes-cache first: old
  posteriors become proposals, old surrogates become amortised levels, known discrepancies become priors on
  model error. Amortization stops being a per-model trick and becomes a property of the *environment*. "Knowledge
  compounds" made mechanically true.

---

## 7. The three example tasks, as one workflow

The point of the whole design — the three tasks the worry named, shown to be the *same five moves*:

**(a) Optimize a transduce with DB queries** (the simple Clojure task)
```
author   (a/defn report [db] (->> (q db …) (filter …) (map …) (reduce + 0)))
view     relational/semiring  (S = counting)
analyze  backward pass of the COST functional → filter-pushdown, aggregation-through-join relevant
plan     certified rewrites, cost-gated; physical strategy (hash/grace/pre-agg)
run      fused, kernel-certified `plan ≡ naïve`;   claim: "result, L0, 12× fewer rows scanned"
```

**(b) Inference as part of a computation, over a semiring**
```
author   same relational shape; facts carry probabilities
view     relational/semiring  (S = probability; or provenance → WMC for correlated marginals)
analyze  backward pass of the MARGINAL functional = variable elimination; relevance prunes nuisance vars
plan     join-order = elimination-order; exact (FAQ) or, if intractable, drop to measure/sampling view
run      marginal;   claim: "P(anomaly | evidence) = 0.21 ± 0.0, L0 algebra + L2 WMC count"
```

**(c) Find the non-identifiable subspace** (partial_identifiability, Gröbner)
```
author   probabilistic model p(O | Z, θ)
view     polynomial/variety   (translate to ideal in k[θ, obs]; log-space; Taylor for transcendentals)
analyze  Gröbner elimination (GF(p)+FGLM) → fibre dimension;  differential view (Jacobian/Fisher) cross-checks
plan     —  (the analysis IS the answer)
run      report;   claim: "θ = (τ,δ) non-identified on a 1-manifold {τ+δ = c}, L1 symbolic; Fisher rank agrees"
```

Same nouns, same verb. The only thing that changed between a database optimization and an algebraic
identifiability proof is **which view you asked for** — and that the engine's job in all three is *translate
the model so the question is cheap, then certify what it did.*

---

## 8. What this is, in one paragraph

A model is a value that can be read at many resolutions and translated into a fixed menu of algebraic views.
A question is a functional; the engine compiles it by running it backward through the model (relevance =
adjoint), choosing the coarsest valid level and the view in which the question is cheap, and returns a claim:
an answer with a certificate of cost, error budget, and trust. Claims compose across levels when interventions
commute with coarse-graining, compose across agents through a shared proposal/certificate schema, and
accumulate in a branchable memory so inference gets cheaper the more the environment is used. Forward is
simulation, backward is inference, and they are the same relation read in two directions — which is the idea
your whole library has been circling, now given a substrate where every branch is free.

---

## 9. Honest open problems (not hidden)

- **The view menu must stay closed and well-founded.** Each view is a category-sized commitment; resist
  growing it casually. (Six is already ambitious; ship two — relational + polynomial/differential — first.)
- **Float ≠ ℝ.** The polynomial/differential/measure views compute in floats; CIC proofs about ℝ do not
  transfer to IEEE. Minimum: precision-differential tests + interval/affine error bounds as a *named L2 entry*
  in the trust ledger. "Plumbing proven, physics calibrated."
- **α discovery vs α authoring.** Spectral methods (Koopman/MSM, NTK) can *discover* coarse-grainings; your
  Zotero is thin here (~3 items) — this is the part to read into (Mehta–Schwab RG↔DL, Transtrum information
  topology of emergent model classes are the bridges you already hold).
- **Scale coupling breaks the clean tower.** Downward causation and adapting levels mean α/γ are a standing
  correspondence, not a pipeline; the formal object is closer to a *bidirectional/lens between dynamical
  systems* (Spivak, "Dynamical Systems and Sheaves") than a reduction. Keep it bidirectional from day one.
- **Identifiability ↔ relevance ↔ validity reconciliation.** These three analyses constrain each other (a
  non-identified direction is irrelevant to some queries and fatal to others; a valid coarse-graining must not
  collapse an identified, query-relevant direction). The engine should *cross-check* them, not run them in
  isolation. This is the most novel and least-built corner.

---

### Reading the design rests on (held in the user's library)

Bidirectional/relational core: Fong–Spivak *Seven Sketches*; Spivak *Generalized Lens Categories*,
*Dynamical Systems and Sheaves*; the bidirectional-programming / reversible-computing / miniKanren collections.
Levels & coarse-graining: Transtrum–Sethna *Sloppiness and Emergent Theories*, *Information topology
identifies emergent model classes*; Mehta–Schwab *Variational RG ↔ Deep Learning*; *Information-geometric
approach to the RG*. Identifiability/algebra: Cox–Little–O'Shea *Ideals, Varieties, Algorithms*; Sturmfels
*Toric algebra of graphical models*, *Likelihood Geometry*; *Differential elimination for structural
identifiability*. Causal abstraction: Rubenstein et al. 2017; Beckers–Halpern 2019; *Multi-Level Cause-Effect
Systems*; *Causal Inference by String Diagram Surgery*; Schölkopf *Toward Causal Representation Learning*.
Inference: Cranmer–Brehmer–Louppe *Frontier of SBI*; Cusumano-Towner/Mansinghka *Gen* (programmable
inference); Murray *Delayed Sampling / Birch*; Amari *Information Geometry*. Compositional modeling:
Patterson et al. *Catlab/SemanticModels*; *Open Games* (optics). Author's own synthesis: org-roam
*Evolutionary Hierarchy*, *Normalization Group Theory*, *Composition*, *Robert Axtell*, *Datalog/Datahike*.
