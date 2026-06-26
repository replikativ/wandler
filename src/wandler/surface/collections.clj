;; Everyday Clojure collection operations in verified bodies.
;;
;; `count`, `reduce`, `mapv`, `filterv` over `List` compile to the kernel `List.*`
;; ops, with element / accumulator types and universe levels inferred. These are
;; TYPE-DIRECTED surface forms, so they register as TERM elaborators (lean4's
;; elab_rules) via the stable extension API `ansatz.surface.api`:
;;
;;   (a/defn total [xs :- (List Nat)] Nat (reduce Nat.add 0 xs))
;;   (a/defn n     [xs :- (List Nat)] Nat (count xs))
;;
;; `install!` runs on load.

(ns wandler.surface.collections
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [wandler.surface.common :refer [nm head-name univ]]
            [ansatz.surface.ingest]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl])
  (:import [ansatz.kernel TypeChecker]))

(defn list-elem?
  "The element type α of a `coll` of inferred type `List α`, or nil (probe form)."
  [est coll]
  (let [t (api/arg-type est coll)
        [h args] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h) (= "List" (name/->string (e/const-name h))) (seq args))
      (first args))))

(defn list-elem
  "The element type α of a `coll` of inferred type `List α`. THROWS when the receiver's
   type is not an inferable List — an honest error beats silently defaulting to List ops
   (the receiver might be a Strm/Map/Value the verb doesn't mean the same thing on)."
  [est coll]
  (or (list-elem? est coll)
      (throw (ex-info (str "collection verb: receiver type is not an inferable (List _) — "
                           "annotate the receiver, or use the type's own surface "
                           "(inferred: " (let [t (api/arg-type est coll)]
                                           (if t (e/->string t) "nil")) ")")
                      {:kind :uninferable-receiver}))))

(defn unwrap-refined-list
  "Coerce a collection receiver to a bare `List α` for a list verb. Returns `[list-coll α]`:
   for `coll : List α` → `[coll α]`; for a refined `coll : Subtype (List α) P` (e.g. a malli `:set`)
   → `[(Subtype.val … coll) α]` (the underlying list); nil if neither. This is what lets a verb like
   `distinct` operate over a `:set` param: it works on the base list and the refinement (Nodup) rides
   on `coll` for the optimizer to consume."
  [est coll]
  (let [t (api/arg-type est coll)
        [h args] (when t (e/get-app-fn-args t))
        hn (when (and h (e/const? h)) (name/->string (e/const-name h)))]
    (cond
      (and (= hn "List") (seq args)) [coll (first args)]
      (and (= hn "Subtype") (= 2 (count args)))
      (let [base (first args) P (second args)
            [bh bargs] (e/get-app-fn-args base)]
        (when (and bh (e/const? bh) (= "List" (name/->string (e/const-name bh))) (seq bargs))
          (let [u (or (first (e/const-levels h)) lvl/zero)]
            [(e/app* (e/const' (name/from-string "Subtype.val") [u]) base P coll) (first bargs)])))
      :else nil)))

;; operator sugar: a bare `+`/`*`/… function argument → its kernel constant
(def ^:private op->const
  {'+ "Nat.add" '* "Nat.mul" '- "Nat.sub" 'inc "Nat.succ"})

(defn inline-fn?
  "An inline anonymous fn: `(fn …)`, `(lam …)`, or a reader `#(…)` (which the reader
   expands to `(fn* …)`)."
  [form]
  (and (seq? form) (#{'fn 'fn* 'lam} (first form)) (vector? (second form))))

(defn- bare-op-const
  "A bare operator (`+`/`*`/`-`) as a function ARGUMENT resolves to the typed op for the
   element type — so `(reduce + 0 int-list)` is Int.add, not Nat.add. (+/*/- exist for
   Nat/Int/Float.) `inc` stays Nat.succ. Returns the const name or nil."
  [op tname]
  (let [tn (if (#{"Nat" "Int" "Float"} tname) tname "Nat")]
    (case op
      + (str tn ".add") * (str tn ".mul") - (str tn ".sub")
      inc "Nat.succ"
      nil)))

(defn compile-fn
  "Compile a function-position argument given the EXPECTED param types (kernel
   exprs). Handles: a bare operator (`+` → <ElemType>.add, type-inferred from the
   param types), an inline UNTYPED anonymous fn (inject the expected types — the
   ergonomic `#(+ % 1)` / `(fn [x] …)`), an already-typed inline fn, or any other term."
  [est f-form param-types]
  (cond
    ;; set-literal-as-predicate: (filter #{2 4 6} xs) — the ubiquitous membership
    ;; idiom. Requires literal elements; desugars to a Bool.or chain of equalities
    ;; (the 2-arg type-directed ==), so downstream laws see plain comparisons.
    (and (set? f-form) (seq f-form) (every? (complement coll?) f-form))
    (let [g (gensym "mem")
          eqs (map (fn [l] (list '== g l)) (sort-by str f-form))
          body (reduce (fn [acc e] (list 'Bool.or e acc)) (last eqs) (rest (reverse eqs)))]
      (compile-fn est (list 'fn [g] body) param-types))
    ;; fn-value combinators, reified as inline fns (Layer-2 intercepts: the runtime
    ;; meaning of comp/partial is function construction, so rebuild the function):
    ;; (comp f g …) — rightmost applies first; (partial f a …) — prepend the args.
    (and (seq? f-form) (= 'comp (first f-form)) (seq (rest f-form)))
    (let [g (gensym "c")]
      (compile-fn est (list 'fn [g]
                            (reduce (fn [acc f] (list f acc)) g (reverse (rest f-form))))
                  param-types))
    (and (seq? f-form) (= 'partial (first f-form)) (seq (rest f-form)))
    (let [g (gensym "p")]
      (compile-fn est (list 'fn [g] (concat (rest f-form) [g])) param-types))
    ;; keyword-as-function: (map :k xs) ≡ (map (fn [x] (:k x)) xs) — the ubiquitous projection
    ;; idiom. Rewrite to an inline untyped fn; the records/Value `(:k x)` elaborator does the
    ;; field access, and the param type is injected from param-types like any anonymous fn.
    (keyword? f-form)
    (let [g (gensym "kw")]
      (compile-fn est (list 'fn [g] (list f-form g)) param-types))
    ;; a bare REGISTERED VERB as a function value ((join first first …), (map rest xss),
    ;; (reduce max 0 xs), (reduce min … xs)): eta-expand to the EXPECTED ARITY so the verb's own
    ;; (type-directed) elaborator handles the application. Arity = (count param-types), so a binary
    ;; reducer like `max`/`min` becomes `(fn [a b] (max a b))`, a unary fn `(fn [g] (f g))`.
    ;; (Bare kernel-const ops like `+`/`*` skip this — they fall to op->const below and stay bare,
    ;; which the parallel-fold monoid recognizer keys on.)
    (and (symbol? f-form)
         (or (get @ansatz.surface.ingest/term-elaborator-registry f-form)
             (get @ansatz.surface.ingest/elaborator-registry f-form)))
    (let [gs (mapv (fn [_] (gensym "eta")) param-types)]
      (compile-fn est (list 'fn gs (cons f-form gs)) param-types))
    (op->const f-form)
    (e/const' (nm (or (bare-op-const f-form (head-name (first param-types)))
                      (op->const f-form))) [])
    (and (inline-fn? f-form) (not (some #{:-} (second f-form))))
    ;; untyped params: inject the expected KERNEL types into the binder vector — the
    ;; elaborator's Expr passthrough makes splicing Exprs into surface forms legal
    ;; (quotation with term holes). Sequential PAIR destructuring `[[a b]]` over a
    ;; Prod param is rewritten at the binder (first/second) — clojure.core/destructure
    ;; would emit nil-defaulted nths, which have no kernel meaning here.
    (let [params (second f-form)
          body (nth f-form 2)
          [params body]
          (reduce (fn [[ps b] p]
                    (cond
                      (symbol? p) [(conj ps p) b]
                      (and (vector? p) (= 2 (count p)) (every? symbol? p))
                      (let [g (gensym "pr")]
                        [(conj ps g)
                         (list 'let [(first p) (list 'first g) (second p) (list 'second g)] b)])
                      :else (throw (ex-info (str "unsupported destructuring binder " (pr-str p)
                                                 " — only [a b] pair destructuring over Prod is"
                                                 " supported in verified bodies")
                                            {:binder p}))))
                  [[] body] params)]
      ;; flag the SOAC predicate/step lambda so a `Subtype`-refined binder auto-coerces to its carrier
      ;; value (`(<= 5 x)` / `(count s)` / `(:k o)` read naturally over refined elements — see elab-lam).
      (api/elab (assoc est :coerce-refined-binders true)
                (list 'lam
                      (vec (mapcat (fn [p ty] [p ty]) params param-types))
                      body)))
    :else
    (try (api/elab est f-form)
         (catch Exception ex
           (if (and (symbol? f-form)
                    (re-find #"Unknown constant" (str (ex-message ex))))
             (throw (ex-info (str "`" f-form "` is not a registered surface verb and not a kernel "
                                  "constant — it cannot be passed as a function value in a verified "
                                  "body. Options: (1) pass an inline (fn [x] …); (2) use a vocabulary "
                                  "verb — see (wandler.core/vocabulary) / docs/REFERENCE.md; or "
                                  "(3) declare it as a TRUSTED FOREIGN fn and use that — "
                                  "(a/foreign " f-form " [x :- <T>] <U> " f-form ") — the pipeline "
                                  "structure still verifies + optimizes; only `" f-form "` is trusted.")
                             {:kind :unknown-fn-value :form f-form} ex))
             (throw ex))))))

(defn- count-elaborator [est args]
  (let [env (:env est)
        coll (api/elab est (first args))
        ctype (api/arg-type est coll)
        [th targs] (when ctype (e/get-app-fn-args ctype))
        tnm (when (and th (e/const? th)) (name/->string (e/const-name th)))]
    (cond
      ;; `(count s)` over a String → String.length (idiomatic Clojure count over a string)
      (= "String" tnm) (e/app (e/const' (nm "String.length") []) coll)
      ;; `(count v)` over a dynamic EDN Value → vsize (top-level element count)
      (= "Value" tnm) (e/app (e/const' (nm "vsize") []) coll)
      ;; `(count m)` over a Map (e.g. the result of group-by) → number of entries
      (and (= "Map" tnm) (>= (count targs) 2))
      (let [K (first targs) V (second targs)
            KV (e/app* (e/const' (nm "Prod") [(univ env K) (univ env V)]) K V)
            entries (e/app* (e/const' (nm "Map.entries") []) K V coll)]
        (e/app* (e/const' (nm "List.length") [(univ env KV)]) KV entries))
      ;; a refined `:set` receiver (Subtype (List α) Nodup) → count its base list (Subtype.val); a
      ;; bare List → itself. `unwrap-refined-list` returns [list-coll α] (nil if neither → honest throw).
      :else (let [[lc a] (or (unwrap-refined-list est coll) [coll (list-elem est coll)])]
              (e/app* (e/const' (nm "List.length") [(univ env a)]) a lc)))))

(def ^:private fold-op-result-type
  "Inline-step head op → accumulator (result) type name, for the fold-init coercion.
   The accumulator type is the RESULT type of the homogeneous op the step applies."
  {'Int.add "Int" 'Int.mul "Int" 'Int.sub "Int"
   'Nat.add "Nat" 'Nat.mul "Nat" 'Nat.sub "Nat" 'Nat.succ "Nat"
   'Float.add "Float" 'Float.mul "Float" 'Float.sub "Float" 'Float.div "Float"
   'String.append "String"})

(defn- step-acc-type
  "Best-effort accumulator type of a reduce STEP (so the init can be coerced to it,
   not the other way round — faithful when the accumulator type ≠ the init literal's
   default). For an inline `(fn [acc x] (OP acc …))` peek the body's head op; for a bare
   op const/symbol read the first param of its kernel type. Returns a type Expr or nil."
  [est f-form elem]
  (if (and (seq? f-form) (#{'fn 'fn*} (first f-form)) (vector? (second f-form)) (>= (count f-form) 3))
    (let [body (nth f-form 2)]
      (when (seq? body)
        (let [hd (first body)]
          (cond
            (fold-op-result-type hd) (e/const' (nm (fold-op-result-type hd)) [])
            (#{'add 'mul 'sub 'div} hd) (api/elab est (second body))
            :else nil))))
    (try (let [op (compile-fn est f-form [elem elem])
               t (api/arg-type est op)]
           (when (e/forall? t) (e/forall-type t)))
         (catch Throwable _ nil))))

(defn- coerce-init
  "Coerce an integer literal `init` to the accumulator type `acc` (Clojure-faithful:
   `0`/`1` etc. take the type the fold needs — Int by default, Nat when refined). Non-
   literals / matching types pass through unchanged."
  [env init acc]
  (if (and acc (e/lit-nat? init))
    (let [tn (head-name acc), n (e/lit-nat-val init)]
      (cond
        (or (nil? tn) (= tn "Nat")) init
        (= tn "Int") (e/app (e/const' (nm "Int.ofNat") []) init)
        (= n 0) (if-let [zi (a/resolve-basic-instance env "Zero" tn acc)]
                  (e/app* (e/const' (nm "OfNat.ofNat") [lvl/zero]) acc init
                          (e/app* (e/const' (nm "Zero.toOfNat0") [lvl/zero]) acc zi))
                  init)
        (= n 1) (if-let [oi (a/resolve-basic-instance env "One" tn acc)]
                  (e/app* (e/const' (nm "OfNat.ofNat") [lvl/zero]) acc init
                          (e/app* (e/const' (nm "One.toOfNat1") [lvl/zero]) acc oi))
                  init)
        :else init))
    init))

(defn- decay-subtype-coll
  "If `coll`'s element type `elem` is a `Subtype B P`, coerce the collection to `List B` via
   `List.map Subtype.val` and return `[coll' B]`; else `[coll elem]`. A `reduce`/fold over a refined list
   returns a base AGGREGATE (the refinement is erased), so the fold op (`+`→`Nat.add`, or any step)
   should run over the carrier `B`, not the `Subtype` — without this a bare op trips `List.foldl`'s
   `acc → elem → acc` shape. The inserted `map Subtype.val` fuses into the fold by the ordinary
   `foldl_map` law, so there's no extra pass at runtime."
  [est coll elem]
  (let [env (:env est)
        [h targs] (e/get-app-fn-args elem)]
    (if (and (e/const? h) (= "Subtype" (name/->string (e/const-name h))) (= 2 (count targs)))
      (let [B (first targs) P (second targs)
            valfn (e/app* (e/const' (nm "Subtype.val") (vec (e/const-levels h))) B P)]
        [(e/app* (e/const' (nm "List.map") [(univ env elem) (univ env B)]) elem B valfn coll) B])
      [coll elem])))

(defn- reduce-elaborator [est args]
  ;; (reduce f init coll) → List.foldl acc elem f init coll  (f : acc → elem → acc).
  ;; Infer the accumulator type from the STEP (so e.g. (Int.add acc …) makes acc Int) and
  ;; coerce the init literal to it — not the reverse, which forced the init's Nat default
  ;; onto the accumulator and broke Int/Float folds.
  (let [env (:env est)
        [f-form init-form coll-form] args
        coll0 (api/elab est coll-form)
        ;; a refined-element source (List (Subtype …)) decays to List of its carrier — the fold op runs
        ;; over the carrier (the aggregate erases the refinement); the inserted map Subtype.val fuses.
        [coll elem] (decay-subtype-coll est coll0 (list-elem est coll0))
        init0 (api/elab est init-form)
        acc (or (step-acc-type est f-form elem)
                (api/arg-type est init0))
        init (coerce-init env init0 acc)
        f (compile-fn est f-form [acc elem])]
    (e/app* (e/const' (nm "List.foldl") [(univ env acc) (univ env elem)])
            acc elem f init coll)))

(defn- reductions-elaborator [est args]
  ;; (reductions f init coll) → List.scanl acc elem f init coll : List acc (the cumulative
  ;; folds, [init, f init x0, f (f init x0) x1, …]). Same acc-type/init handling as reduce.
  (let [env (:env est)
        [f-form init-form coll-form] args
        coll0 (api/elab est coll-form)
        [coll elem] (decay-subtype-coll est coll0 (list-elem est coll0))  ; refined source → carrier (fold erases)
        init0 (api/elab est init-form)
        acc (or (step-acc-type est f-form elem)
                (api/arg-type est init0))
        init (coerce-init env init0 acc)
        f (compile-fn est f-form [acc elem])]
    (e/app* (e/const' (nm "List.scanl") [(univ env acc) (univ env elem)])
            acc elem f init coll)))

(defn- mapv-elaborator [est args]
  ;; (mapv f coll) → List.map α β f coll  (f : α → β)
  (let [env (:env est)
        [f-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        f (compile-fn est f-form [a])
        b (api/whnf est (e/forall-body (api/arg-type est f)))]   ; β (reduced; #56)
    (e/app* (e/const' (nm "List.map") [(univ env a) (univ env b)]) a b f coll)))

(defn- filterv-elaborator [est args]
  ;; (filterv p coll) → List.filter α p coll   (p : α → Bool)
  (let [env (:env est)
        [p-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        p (compile-fn est p-form [a])]
    (e/app* (e/const' (nm "List.filter") [(univ env a)]) a p coll)))

;; ── Transducer ingestion ────────────────────────────────────────────────────
;; A Clojurian writes idiomatic transducer code — `(into [] (comp (map f)
;; (filter p)) xs)`, `(transduce xf + 0 xs)`, `(sequence xf xs)`. A transducer
;; stack is just a DIFFERENT SURFACE for the same nested SOAC IR we already fuse
;; and certify: `(comp (map f) (filter p))` applied to data is `filter p ∘ map f`,
;; i.e. the naive `(filterv p (mapv f xs))`. So we desugar the stack to that
;; nested FORM and hand it back to the elaborator — it re-dispatches through the
;; existing mapv/filterv/reduce elaborators (type inference included) and the
;; existing optimizer fuses + kernel-certifies it. No new IR code, no new proofs.

(def ^:private xform-stage-heads-1
  "Transducer stages taking one argument (a fn or literal) before the data."
  '#{map filter remove take drop take-while drop-while mapcat map-indexed interpose})

(def ^:private xform-stage-heads-0
  "Nullary transducer stages."
  '#{distinct dedupe})

(defn- xform-steps
  "Flatten a transducer expression to an ordered vector of single stages (the
   arity-without-data transducer forms, NOT the eager `(map f coll)`); `comp`
   nests left-to-right (the leftmost stage sees each element first)."
  [form]
  (cond
    (and (seq? form) (= 'comp (first form)))
    (vec (mapcat xform-steps (rest form)))
    (and (seq? form) (xform-stage-heads-1 (first form)) (= 2 (count form)))
    [form]
    (and (seq? form) (xform-stage-heads-0 (first form)) (= 1 (count form)))
    [form]
    :else
    (throw (ex-info (str "Unsupported transducer: " (pr-str form)
                         " — supported stages: (map f) (filter p) (remove p) (mapcat f)"
                         " (map-indexed f) (take n) (drop n) (take-while p) (drop-while p)"
                         " (interpose x) (distinct) (dedupe), composed with comp")
                    {:form form}))))

(defn- xform->form
  "Build the nested collection FORM a transducer stack denotes when run over
   `coll-form`: fold the stages left-to-right, each wrapping the accumulator
   (leftmost = innermost data transform = first applied). Values agree with the
   transducer semantics over finite pure data (purity makes early-termination an
   efficiency difference, not a value difference)."
  [coll-form steps]
  (reduce (fn [acc st]
            (case (first st)
              map    (list 'mapv (second st) acc)
              filter (list 'filterv (second st) acc)
              ;; remove p = filter (Bool.not ∘ p). Negate an inline predicate's
              ;; body directly; require an inline fn.
              remove (let [p (second st)]
                       (if (and (seq? p) (#{'fn 'fn*} (first p)) (vector? (second p)) (= 3 (count p)))
                         (list 'filterv (list 'fn (second p) (list 'Bool.not (nth p 2))) acc)
                         (throw (ex-info "remove currently requires an inline (fn [x] …) predicate"
                                         {:pred p}))))
              ;; the remaining stages have eager surface verbs of the same name —
              ;; rebuild the eager call and let the existing elaborators dispatch.
              (take drop take-while drop-while mapcat map-indexed interpose)
              (list (first st) (second st) acc)
              (distinct dedupe)
              (list (first st) acc)))
          coll-form steps))

(defn- into-elaborator [est args]
  ;; (into [] xform coll)  or  (into [] coll). Only the vector target [] (eager
  ;; realization into a fresh vector) is supported — the result IS the transformed list.
  (let [target (first args)]
    (when-not (and (vector? target) (empty? target))
      (throw (ex-info "Only (into [] xform? coll) is supported in a verified body"
                      {:target target})))
    (case (count args)
      2 (api/elab est (nth args 1))
      3 (api/elab est (xform->form (nth args 2) (xform-steps (nth args 1))))
      (throw (ex-info "into: expected (into [] coll) or (into [] xform coll)" {:args args})))))

(defn- transduce-elaborator [est args]
  ;; (transduce xform rf init coll) → reduce rf init over the transformed list.
  (when-not (= 4 (count args))
    (throw (ex-info "transduce: expected (transduce xform rf init coll)" {:args args})))
  (let [[xform rf init coll] args]
    (api/elab est (list 'reduce rf init (xform->form coll (xform-steps xform))))))

(defn- sequence-elaborator [est args]
  ;; (sequence xform coll) → the transformed list.
  (when-not (= 2 (count args))
    (throw (ex-info "sequence: expected (sequence xform coll)" {:args args})))
  (api/elab est (xform->form (second args) (xform-steps (first args)))))

(defn- eduction-elaborator [est args]
  ;; (eduction xf1 xf2 … coll) → the transformed list (eduction takes MULTIPLE
  ;; xforms before the data; values agree with the lazy view over finite data).
  (when (< (count args) 2)
    (throw (ex-info "eduction: expected (eduction xform+ coll)" {:args args})))
  (api/elab est (xform->form (last args) (vec (mapcat xform-steps (butlast args))))))

;; ── more clojure.core vocabulary: prefix/suffix + head/tail ──────────────────
;; Each maps to the corresponding Lean List op (the verified DENOTATION) and lowers to
;; the Clojure runtime op. take/take-while/drop are LAZY in Clojure, so a bounded terminal
;; like `(take n …)` makes an INFINITE lazy pipeline fully consumable (streams n elements).

(defn- take-elaborator [est args]
  ;; (take n coll) → List.take α n coll
  (let [[n-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        n (api/elab est n-form)]
    (e/app* (e/const' (nm "List.take") [(univ (:env est) a)]) a n coll)))

(defn- nth-elaborator [est args]
  ;; (nth coll i default) → List.getD α coll i default : α  (index with a default; α inferred).
  ;; The 3-arg form — 2-arg nth (throw on OOB) would need List.get with a bounds proof.
  (let [[coll-form i-form d-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        i (api/elab est i-form)
        d (api/elab est d-form)]
    (e/app* (e/const' (nm "List.getD") [(univ (:env est) a)]) a coll i d)))

(defn- range-elaborator [est args]
  ;; (range n) → List.range n : List Nat  — [0, 1, …, n-1]
  (e/app* (e/const' (nm "List.range") []) (api/elab est (first args))))

(defn- drop-elaborator [est args]
  (let [[n-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        n (api/elab est n-form)]
    (e/app* (e/const' (nm "List.drop") [(univ (:env est) a)]) a n coll)))

(defn- reverse-elaborator [est args]
  ;; (reverse coll) → List.reverse α coll
  (let [coll (api/elab est (first args))
        a (list-elem est coll)]
    (e/app* (e/const' (nm "List.reverse") [(univ (:env est) a)]) a coll)))

;; ── `for` list comprehension (surface form rewrite, intercepted before Clojure's `for` macro) ──
;; Clojure's `for` macroexpands to lazy-seq/chunk machinery with untyped gensym binders the kernel
;; can't elaborate. We grab it as a surface form FIRST (the elaborator-registry takes precedence over
;; macroexpansion, like `->`) and rewrite to the verified SOACs: innermost generator → `map`, outer
;; generators → `mapcat` (cartesian product), `:when` → `filter` on that generator's collection,
;; `:let` → `let` wrapping the body. (`:while`/`:when`-after-`:let`-referencing-the-let-var are not
;; modelled — `:when` filters the source collection, so it must reference only the generator var.)
(defn- for-clauses
  "Parse a `for` binding vector into generator groups {:sym :coll :whens :lets} in source order."
  [bindings]
  (loop [bs (seq bindings), out []]
    (if (empty? bs)
      out
      (let [sym (first bs), coll (second bs)
            [mods rest'] (loop [bs (drop 2 bs), mods []]
                           (if (and (seq bs) (keyword? (first bs)))
                             (recur (drop 2 bs) (conj mods [(first bs) (second bs)]))
                             [mods bs]))
            bad (seq (remove (comp #{:when :let} first) mods))]
        (when bad
          (throw (ex-info (str "for: only :when and :let modifiers are supported in verified "
                               "pipelines; got " (pr-str (map first bad))) {:mods bad})))
        (recur rest'
               (conj out {:sym sym :coll coll
                          :whens (keep (fn [[k v]] (when (= :when k) v)) mods)
                          :lets  (keep (fn [[k v]] (when (= :let k) v)) mods)}))))))

(defn- for-rewrite [args]
  (let [bindings (first args), body (last args)
        groups (for-clauses bindings)]
    (when (empty? groups) (throw (ex-info "for: needs at least one generator" {})))
    (reduce
     (fn [inner {:keys [sym coll whens lets]}]
       (let [coll' (reduce (fn [c p] (list 'filter (list 'fn [sym] p) c)) coll whens)
             body' (reduce (fn [b bv] (list 'let bv b)) inner lets)
             op    (if (identical? inner body) 'map 'mapcat)]   ; innermost = map, outer = mapcat
         (list op (list 'fn [sym] body') coll')))
     body
     (reverse groups))))

(defn- take-nth-elaborator [est args]
  ;; (take-nth k coll) : List α — every k-th element (indices 0, k, 2k, …). No Init primitive, so we
  ;; INLINE a verified non-recursive encoding: a left fold over a (counter, kept-reversed) Prod
  ;; accumulator — keep the element when the counter hits 0 (resetting it to k−1), else decrement;
  ;; a final `reverse` restores order. Built from Init foldl/reverse + Prod + Nat.sub (no recursion).
  (let [[k-form coll-form] args
        coll (api/elab est coll-form)
        a    (list-elem est coll)
        k    (api/elab est k-form)
        La   (list 'List a)
        P    (list 'Prod 'Nat La)
        fstA (fn [acc] (list 'Prod.fst 'Nat La acc))
        sndA (fn [acc] (list 'Prod.snd 'Nat La acc))
        step (list 'fn [(with-meta 'acc {:- P}) (with-meta 'x {:- a})]
                   (list 'if (list '== (fstA 'acc) 0)
                         (list 'Prod.mk 'Nat La (list 'Nat.sub k 1)
                               (list 'List.cons a 'x (sndA 'acc)))
                         (list 'Prod.mk 'Nat La (list 'Nat.sub (fstA 'acc) 1) (sndA 'acc))))
        init (list 'Prod.mk 'Nat La 0 (list 'List.nil a))
        form (list 'List.reverse a (sndA (list 'List.foldl P a step init coll)))]
    (api/elab est form)))

(defn- zip-elaborator [est args]
  ;; (zip a b) → List.zip α β a b : List (Prod α β).
  (let [[a-form b-form] args
        a (api/elab est a-form) b (api/elab est b-form)
        ea (list-elem est a) eb (list-elem est b)]
    (e/app* (e/const' (nm "List.zip") [(univ (:env est) ea) (univ (:env est) eb)]) ea eb a b)))

(defn- drop-last-elaborator [est args]
  ;; (drop-last coll) → List.dropLast α coll  (drops the final element; α implicit in the sig but
  ;; supplied positionally to the raw const, as with reverse). The n-ary `(drop-last n coll)` is a
  ;; separate spelling (take (count-n)); only the common 1-arg form is the verb.
  (let [coll (api/elab est (first args))
        a (list-elem est coll)]
    (e/app* (e/const' (nm "List.dropLast") [(univ (:env est) a)]) a coll)))

(defn- partition-all-elaborator [est args]
  ;; (partition-all n coll) : List (List α) — Clojure `partition-all` (keeps the short final chunk;
  ;; n=0 → one chunk, matching batteries `List.toChunks`). NO Init `chunk` primitive exists, so we
  ;; INLINE a verified non-recursive encoding: a left fold that prepends each element to the current
  ;; chunk (head of the accumulator), starting a fresh chunk once the current one reaches length n;
  ;; chunks and their elements are built reversed, so a final `reverse ∘ map reverse` restores order.
  ;; Built entirely from Init List ops (foldl/map/reverse/cons/nil/isEmpty/headD/tail/length) with the
  ;; element type α spliced in — so it kernel-verifies and the SOAC lowerings carry it (no recursion,
  ;; no WF). `partition` (below) drops the incomplete tail by filtering full-length chunks.
  (let [[n-form coll-form] args
        coll (api/elab est coll-form)
        a    (list-elem est coll)
        n    (api/elab est n-form)
        La   (list 'List a)
        LLa  (list 'List La)
        nilA (list 'List.nil a)
        nilLa (list 'List.nil La)
        sing (fn [x] (list 'List.cons a x nilA))          ; (x :: []) : List α
        step (list 'fn [(with-meta 'acc {:- LLa}) (with-meta 'x {:- a})]
                   (list 'if (list 'List.isEmpty La 'acc)
                         (list 'List.cons La (sing 'x) nilLa)
                         (list 'let ['c (list 'List.headD La 'acc nilA) 'cs (list 'List.tail La 'acc)]
                               (list 'if (list '== (list 'List.length a 'c) n)
                                     (list 'List.cons La (sing 'x) 'acc)
                                     (list 'List.cons La (list 'List.cons a 'x 'c) 'cs)))))
        folded (list 'List.foldl LLa a step nilLa coll)
        form   (list 'List.map La La
                     (list 'fn [(with-meta 'c {:- La})] (list 'List.reverse a 'c))
                     (list 'List.reverse La folded))]
    (api/elab est form)))

(defn- concat-elaborator [est args]
  ;; (concat a b) → List.append α a b  (2-ary; nested for more)
  (let [colls (map #(api/elab est %) args)
        a (list-elem est (first colls))
        u (univ (:env est) a)]
    (reduce (fn [acc c] (e/app* (e/const' (nm "List.append") [u]) a acc c)) colls)))

(defn- interpose-elaborator [est args]
  ;; (interpose sep coll) → List.intersperse α sep coll
  (let [[sep-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        sep (api/elab est sep-form)]
    (e/app* (e/const' (nm "List.intersperse") [(univ (:env est) a)]) a sep coll)))

(defn- take-while-elaborator [est args]
  ;; (take-while p coll) → List.takeWhile α p coll   (p : α → Bool)
  (let [[p-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        p (compile-fn est p-form [a])]
    (e/app* (e/const' (nm "List.takeWhile") [(univ (:env est) a)]) a p coll)))

(defn- drop-while-elaborator [est args]
  (let [[p-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        p (compile-fn est p-form [a])]
    (e/app* (e/const' (nm "List.dropWhile") [(univ (:env est) a)]) a p coll)))

(defn- prod-elems
  "The component types [α β] of a `p` of inferred type `Prod α β`, or nil."
  [est p]
  (let [t (api/arg-type est p)
        [h args] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h) (= "Prod" (name/->string (e/const-name h))) (>= (count args) 2))
      [(first args) (second args)])))

(defn- first-elaborator [est args]
  ;; (first x) — Clojure-style, dispatching on the receiver: a List → List.head? α x : Option α
  ;; (none/nil for empty); a Prod (a pair, sequential in Clojure) → Prod.fst α β x : α.
  (let [env (:env est)
        coll (api/elab est (first args))]
    (if-let [[a b] (prod-elems est coll)]
      (e/app* (e/const' (nm "Prod.fst") [(univ env a) (univ env b)]) a b coll)
      (let [a (list-elem est coll)]
        (e/app* (e/const' (nm "List.head?") [(univ env a)]) a coll)))))

(defn- second-elaborator [est args]
  ;; (second x) — a List → its 2nd element (head? of the tail) : Option α; a Prod → Prod.snd : β.
  (let [env (:env est)
        coll (api/elab est (first args))]
    (if-let [[a b] (prod-elems est coll)]
      (e/app* (e/const' (nm "Prod.snd") [(univ env a) (univ env b)]) a b coll)
      (let [a (list-elem est coll) u (univ env a)]
        (e/app* (e/const' (nm "List.head?") [u]) a
                (e/app* (e/const' (nm "List.tail") [u]) a coll))))))

(defn- rest-elaborator [est args]
  ;; (rest xs) → List.tail α xs : List α  (Clojure's rest — empty list for empty/singleton).
  (let [coll (api/elab est (first args))
        a (list-elem est coll)]
    (e/app* (e/const' (nm "List.tail") [(univ (:env est) a)]) a coll)))

(defn- last-elaborator [est args]
  (let [coll (api/elab est (first args))
        a (list-elem est coll)]
    (e/app* (e/const' (nm "List.getLast?") [(univ (:env est) a)]) a coll)))

(defn- map-indexed-elaborator [est args]
  ;; (map-indexed f coll) → List.mapIdx α β f coll   (f : Nat → α → β, f index elem)
  (let [env (:env est)
        [f-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        nat (e/const' (nm "Nat") [])
        f (compile-fn est f-form [nat a])
        ftype (api/arg-type est f)                       ; Nat → α → β
        b (api/whnf est (e/forall-body (e/forall-body ftype)))]            ; β
    (e/app* (e/const' (nm "List.mapIdx") [(univ env a) (univ env b)]) a b f coll)))

(defn- mapcat-elaborator [est args]
  ;; (mapcat f coll) → List.flatMap α β f coll   (f : α → List β)
  (let [env (:env est)
        [f-form coll-form] args
        coll (api/elab est coll-form)
        a (list-elem est coll)
        f (compile-fn est f-form [a])
        cod (api/whnf est (e/forall-body (api/arg-type est f)))      ; codomain: List β
        [_ ca] (e/get-app-fn-args cod)
        b (first ca)]                                    ; β
    (e/app* (e/const' (nm "List.flatMap") [(univ env a) (univ env b)]) a b f coll)))

;; NOTE: `keep` is intentionally UNsupported. Clojurians use it with a nil-punning predicate
;; (#(when (even? %) %)) — i.e. PRODUCE an Option via nil — which the Option layer doesn't model
;; (it CONSUMES Option via narrowing, not produces). Unregistered, it fails transparently
;; ("Unknown: keep"). The List.filterMap codegen exists for when an Option-producing form lands.

;; ── threading: ->/->> are GENERAL surface forms (not record-specific), so they live in the
;; base collection ns — pure form→form rewriting, so they stay macro_rules-shaped.
(defn- thread-first [x forms]
  (reduce (fn [acc form] (if (seq? form) (list* (first form) acc (rest form)) (list form acc))) x forms))
(defn- thread-last [x forms]
  (reduce (fn [acc form] (if (seq? form) (concat form [acc]) (list form acc))) x forms))

(defn- not-elaborator [est args]
  ;; (not x) → Bool.not x (Bool is the runtime truth carrier in verified bodies)
  (e/app (e/const' (nm "Bool.not") []) (api/elab est (first args))))

(defn- inc-elaborator [est args]
  ;; (inc x) → Nat.succ x  (Int via type dispatch when Int ops land in Init)
  (e/app (e/const' (nm "Nat.succ") []) (api/elab est (first args))))

(defn- dec-elaborator [est args]
  ;; (dec x) → Nat.sub x 1 (truncated Nat subtraction, the kernel denotation)
  (e/app* (e/const' (nm "Nat.sub") []) (api/elab est (first args)) (e/lit-nat 1)))

(defn- nat2-elaborator
  "A 2-arg Nat op (Nat.div / Nat.max / Nat.min …) as a surface verb."
  [const-name]
  (fn [est args]
    (e/app* (e/const' (nm const-name) []) (api/elab est (first args)) (api/elab est (second args)))))

(defn- mod-elaborator [est args]
  ;; (mod a b) → Nat.mod a b. Nat only: Clojure's floored mod and Lean's Nat.mod
  ;; agree on naturals (incl. Nat.mod n 0 = n at the lowering); Int needs the
  ;; emod story and stays unsupported for now.
  (e/app* (e/const' (nm "Nat.mod") []) (api/elab est (first args)) (api/elab est (second args))))

(defn install!
  "Register the collection-op elaborators (idempotent). Type-directed verbs are TERM
   elaborators (elab_rules); pure form rewrites (threading) are macro elaborators."
  []
  (api/register-elaborator! '-> (fn [args] (thread-first (first args) (rest args))))
  (api/register-elaborator! '->> (fn [args] (thread-last (first args) (rest args))))
  (api/register-term-elaborator! 'not not-elaborator)
  (api/register-term-elaborator! 'inc inc-elaborator)
  (api/register-term-elaborator! 'dec dec-elaborator)
  (api/register-term-elaborator! 'count count-elaborator)
  (api/register-term-elaborator! 'reduce reduce-elaborator)
  (api/register-term-elaborator! 'reductions reductions-elaborator)
  (api/register-term-elaborator! 'mapv mapv-elaborator)
  (api/register-term-elaborator! 'filterv filterv-elaborator)
  ;; bare `map`/`filter` aliases — verified pipelines are eager (no laziness), so over a single
  ;; collection these mean the same as mapv/filterv. (Variadic `map` = zip is not modeled.)
  (api/register-term-elaborator! 'map mapv-elaborator)
  (api/register-term-elaborator! 'filter filterv-elaborator)
  (api/register-term-elaborator! 'take take-elaborator)
  (api/register-term-elaborator! 'nth nth-elaborator)
  (api/register-term-elaborator! 'range range-elaborator)
  (api/register-term-elaborator! 'drop drop-elaborator)
  (api/register-term-elaborator! 'reverse reverse-elaborator)
  (api/register-term-elaborator! 'drop-last drop-last-elaborator)
  (api/register-term-elaborator! 'partition-all partition-all-elaborator)
  (api/register-term-elaborator! 'take-nth take-nth-elaborator)
  ;; (partition n coll) ≡ (filter (full-length n) (partition-all n coll)) — Clojure `partition` DROPS
  ;; the incomplete final chunk. Pure form rewrite onto the inlined partition-all + filter + count.
  (api/register-elaborator! 'partition
    (fn [args]
      (let [[n coll] args, c (gensym "pc__")]
        (list 'filter (list 'fn [c] (list '== (list 'count c) n)) (list 'partition-all n coll)))))
  (api/register-term-elaborator! 'zip zip-elaborator)
  ;; (interleave a b) ≡ (mapcat (fn [p] [(first p) (second p)]) (zip a b)) — zip to pairs, then
  ;; flat-map each Prod to its two elements (mapcat flattens). Pure form rewrite onto zip + mapcat +
  ;; Prod.fst/snd, all Init. Same-typed lists (a,b : List α) → List α, as Clojure's interleave.
  (api/register-elaborator! 'interleave
    (fn [args]
      (let [[a b] args, p (gensym "il__")]
        (list 'mapcat (list 'fn [p] [(list 'first p) (list 'second p)]) (list 'zip a b)))))
  ;; (apply ⊕ coll) ≡ (reduce ⊕ id⊕ coll) for a monoid ⊕ with a known identity. The verified-pipeline
  ;; meaning of `apply` over one collection is a fold; +→0, *→1, max→0 (0 is ⊥ for Nat.max). (min has
  ;; no Nat identity — no ⊤ — so `apply min` is unsupported; spell it `(reduce min …)` with an explicit
  ;; seed.) Pure form rewrite onto reduce (which now eta-expands the bare op step, see compile-fn).
  (api/register-elaborator! 'apply
    (fn [args]
      (let [[op coll] args, id ('{+ 0, * 1, max 0} op)]
        (if (and (= 2 (count args)) id)
          (list 'reduce op id coll)
          (throw (ex-info (str "apply: only (apply ⊕ coll) for ⊕∈{+,*,max} with a known identity is "
                               "supported in verified pipelines; got " (pr-str (cons 'apply args)))
                          {:args args}))))))
  (api/register-term-elaborator! 'concat concat-elaborator)
  (api/register-term-elaborator! 'interpose interpose-elaborator)
  (api/register-term-elaborator! 'take-while take-while-elaborator)
  (api/register-term-elaborator! 'drop-while drop-while-elaborator)
  (api/register-term-elaborator! 'first first-elaborator)
  (api/register-term-elaborator! 'second second-elaborator)
  (api/register-term-elaborator! 'rest rest-elaborator)
  (api/register-term-elaborator! 'last last-elaborator)
  (api/register-term-elaborator! 'mapcat mapcat-elaborator)  ; keep: see note above (unsupported)
  (api/register-term-elaborator! 'map-indexed map-indexed-elaborator)
  ;; transducer surface (desugars to the nested SOAC form above)
  (api/register-term-elaborator! 'into into-elaborator)
  (api/register-term-elaborator! 'transduce transduce-elaborator)
  (api/register-term-elaborator! 'sequence sequence-elaborator)
  (api/register-term-elaborator! 'eduction eduction-elaborator)
  (api/register-term-elaborator! 'mod mod-elaborator)
  (api/register-term-elaborator! 'quot (nat2-elaborator "Nat.div"))
  (api/register-term-elaborator! 'max (nat2-elaborator "Nat.max"))
  (api/register-term-elaborator! 'min (nat2-elaborator "Nat.min"))
  ;; parity predicates: pure form rewrites onto mod + the type-directed ==
  (api/register-elaborator! 'for for-rewrite)
  (api/register-elaborator! 'even? (fn [args] (list '== (list 'mod (first args) 2) 0)))
  (api/register-elaborator! 'odd?  (fn [args] (list '== (list 'mod (first args) 2) 1)))
  ;; (remove p coll) ≡ (filter (complement p) coll) — a pure form rewrite onto the verified `filterv`
  ;; + `not`, so the result fuses + kernel-certifies like any filter. For an inline `(fn [x] body)` we
  ;; negate the BODY in place (reusing the binder, so its type is inferred from the filter element —
  ;; same trick the transducer-stack `remove` uses); for a named predicate verb (even?/odd?/…) we
  ;; eta-expand. An unknown bare symbol fails transparently when `(p x)` doesn't elaborate.
  (api/register-elaborator! 'remove
    (fn [args]
      (let [[p coll] args]
        (if (and (seq? p) (#{'fn 'fn*} (first p)) (vector? (second p)) (= 3 (count p)))
          (list 'filterv (list 'fn (second p) (list 'not (nth p 2))) coll)
          (let [g (gensym "rx__")]
            (list 'filterv (list 'fn [g] (list 'not (list p g))) coll)))))))

(install!)
