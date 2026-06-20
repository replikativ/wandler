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

(ns wandler.clean.surface.collections
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [wandler.clean.surface.common :refer [nm head-name univ]]
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
    ;; a bare REGISTERED VERB as a function value ((join first first …), (map rest xss)):
    ;; eta-expand so the verb's own (type-directed) elaborator handles the application
    (and (symbol? f-form)
         (or (get @ansatz.surface.ingest/term-elaborator-registry f-form)
             (get @ansatz.surface.ingest/elaborator-registry f-form)))
    (let [g (gensym "eta")]
      (compile-fn est (list 'fn [g] (list f-form g)) param-types))
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
      (api/elab est (list 'lam
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
                                  "verb — see (wandler.core/vocabulary) / docs/SURFACE.md; or "
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
      ;; `(count v)` over a dynamic EDN Value → vsize (top-level element count)
      (= "Value" tnm) (e/app (e/const' (nm "vsize") []) coll)
      ;; `(count m)` over a Map (e.g. the result of group-by) → number of entries
      (and (= "Map" tnm) (>= (count targs) 2))
      (let [K (first targs) V (second targs)
            KV (e/app* (e/const' (nm "Prod") [(univ env K) (univ env V)]) K V)
            entries (e/app* (e/const' (nm "Map.entries") []) K V coll)]
        (e/app* (e/const' (nm "List.length") [(univ env KV)]) KV entries))
      :else (let [a (list-elem est coll)]
              (e/app* (e/const' (nm "List.length") [(univ env a)]) a coll)))))

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

(defn- reduce-elaborator [est args]
  ;; (reduce f init coll) → List.foldl acc elem f init coll  (f : acc → elem → acc).
  ;; Infer the accumulator type from the STEP (so e.g. (Int.add acc …) makes acc Int) and
  ;; coerce the init literal to it — not the reverse, which forced the init's Nat default
  ;; onto the accumulator and broke Int/Float folds.
  (let [env (:env est)
        [f-form init-form coll-form] args
        coll (api/elab est coll-form)
        elem (list-elem est coll)
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
        coll (api/elab est coll-form)
        elem (list-elem est coll)
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
  (api/register-elaborator! 'even? (fn [args] (list '== (list 'mod (first args) 2) 0)))
  (api/register-elaborator! 'odd?  (fn [args] (list '== (list 'mod (first args) 2) 1))))

(install!)
