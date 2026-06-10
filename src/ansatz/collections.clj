;; Everyday Clojure collection operations in verified bodies.
;;
;; `count`, `reduce`, `mapv`, `filterv` over `List` compile to the kernel `List.*`
;; ops, with element / accumulator types and universe levels inferred (fvar-first
;; elaboration makes the inference robust). So idiomatic list code verifies:
;;
;;   (a/defn total [xs :- (List Nat)] Nat (reduce Nat.add 0 xs))
;;   (a/defn n     [xs :- (List Nat)] Nat (count xs))
;;
;; Registered via `register-elaborator!` (no core change). `install!` runs on load.

(ns ansatz.collections
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl])
  (:import [ansatz.kernel TypeChecker]))

(defn nm [s] (name/from-string s))

(defn univ
  "The universe level `u` of a type `t : Sort(u+1)` (e.g. 0 for `Nat`)."
  [env t]
  (lvl/succ-pred (e/sort-level (.inferType (TypeChecker. env) t))))

(defn list-elem
  "The element type α of a `coll` of inferred type `List α`, or nil."
  [env coll]
  (let [t (a/get-arg-type env nil coll)
        [h args] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h) (= "List" (name/->string (e/const-name h))) (seq args))
      (first args))))

;; operator sugar: a bare `+`/`*`/… function argument → its kernel constant
(def ^:private op->const
  {'+ "Nat.add" '* "Nat.mul" '- "Nat.sub" 'inc "Nat.succ"})

(defn inline-fn?
  "An inline anonymous fn: `(fn …)`, `(lam …)`, or a reader `#(…)` (which the reader
   expands to `(fn* …)`)."
  [form]
  (and (seq? form) (#{'fn 'fn* 'lam} (first form)) (vector? (second form))))

(defn- head-name'
  "Head constant name of a kernel type expr, or nil. (local copy; head-name appears later)"
  [t]
  (let [[h _] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h)) (name/->string (e/const-name h)))))

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
  [env scope depth f-form param-types lctx]
  (cond
    ;; keyword-as-function: (map :k xs) ≡ (map (fn [x] (:k x)) xs) — the ubiquitous projection idiom.
    ;; Rewrite to an inline untyped fn; the records/Value `(:k x)` elaborator does the field access,
    ;; and the param type is injected from param-types like any anonymous fn.
    (keyword? f-form)
    (let [g (gensym "kw")]
      (compile-fn env scope depth (list 'fn [g] (list f-form g)) param-types lctx))
    (op->const f-form)
    (e/const' (nm (or (bare-op-const f-form (head-name' (first param-types)))
                      (op->const f-form))) [])
    (and (inline-fn? f-form) (not (some #{:-} (second f-form))))
    ;; untyped params: inject the expected types via build-telescope (expr ptypes)
    (a/build-telescope env scope depth
                       (mapv vector (second f-form) param-types)
                       (nth f-form 2) e/lam)
    :else (a/sexp->ansatz env scope depth f-form lctx)))

(defn- count-elaborator [env scope depth args lctx]
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        ctype (a/get-arg-type env nil coll)
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
      :else (let [a (list-elem env coll)]
              (e/app* (e/const' (nm "List.length") [(univ env a)]) a coll)))))

(defn- head-name
  "Head constant name of a kernel type expr (e.g. \"Int\" for `Int`), or nil."
  [t]
  (let [[h _] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h)) (name/->string (e/const-name h)))))

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
  [env scope depth f-form elem lctx]
  (if (and (seq? f-form) (#{'fn 'fn*} (first f-form)) (vector? (second f-form)) (>= (count f-form) 3))
    (let [body (nth f-form 2)]
      (when (seq? body)
        (let [hd (first body)]
          (cond
            (fold-op-result-type hd) (e/const' (nm (fold-op-result-type hd)) [])
            (#{'add 'mul 'sub 'div} hd) (a/sexp->ansatz env scope depth (second body) lctx)
            :else nil))))
    (try (let [op (compile-fn env scope depth f-form [elem elem] lctx)
               t (a/get-arg-type env nil op)]
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

(defn- reduce-elaborator [env scope depth args lctx]
  ;; (reduce f init coll) → List.foldl acc elem f init coll  (f : acc → elem → acc).
  ;; Infer the accumulator type from the STEP (so e.g. (Int.add acc …) makes acc Int) and
  ;; coerce the init literal to it — not the reverse, which forced the init's Nat default
  ;; onto the accumulator and broke Int/Float folds.
  (let [[f-form init-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        elem (list-elem env coll)
        init0 (a/sexp->ansatz env scope depth init-form lctx)
        acc (or (step-acc-type env scope depth f-form elem lctx)
                (a/get-arg-type env nil init0))
        init (coerce-init env init0 acc)
        f (compile-fn env scope depth f-form [acc elem] lctx)]
    (e/app* (e/const' (nm "List.foldl") [(univ env acc) (univ env elem)])
            acc elem f init coll)))

(defn- reductions-elaborator [env scope depth args lctx]
  ;; (reductions f init coll) → List.scanl acc elem f init coll : List acc (the cumulative
  ;; folds, [init, f init x0, f (f init x0) x1, …]). Same acc-type/init handling as reduce.
  (let [[f-form init-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        elem (list-elem env coll)
        init0 (a/sexp->ansatz env scope depth init-form lctx)
        acc (or (step-acc-type env scope depth f-form elem lctx)
                (a/get-arg-type env nil init0))
        init (coerce-init env init0 acc)
        f (compile-fn env scope depth f-form [acc elem] lctx)]
    (e/app* (e/const' (nm "List.scanl") [(univ env acc) (univ env elem)])
            acc elem f init coll)))

(defn- mapv-elaborator [env scope depth args lctx]
  ;; (mapv f coll) → List.map α β f coll  (f : α → β)
  (let [[f-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        f (compile-fn env scope depth f-form [a] lctx)
        b (a/whnf-ty env (e/forall-body (a/get-arg-type env nil f)))]   ; β (reduced; #56)
    (e/app* (e/const' (nm "List.map") [(univ env a) (univ env b)]) a b f coll)))

(defn- filterv-elaborator [env scope depth args lctx]
  ;; (filterv p coll) → List.filter α p coll   (p : α → Bool)
  (let [[p-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        p (compile-fn env scope depth p-form [a] lctx)]
    (e/app* (e/const' (nm "List.filter") [(univ env a)]) a p coll)))

;; ── Transducer ingestion ────────────────────────────────────────────────────
;; A Clojurian writes idiomatic transducer code — `(into [] (comp (map f)
;; (filter p)) xs)`, `(transduce xf + 0 xs)`, `(sequence xf xs)`. A transducer
;; stack is just a DIFFERENT SURFACE for the same nested SOAC IR we already fuse
;; and certify: `(comp (map f) (filter p))` applied to data is `filter p ∘ map f`,
;; i.e. the naive `(filterv p (mapv f xs))`. So we desugar the stack to that
;; nested FORM and hand it back to `sexp->ansatz` — it re-dispatches through the
;; existing mapv/filterv/reduce elaborators (type inference included) and the
;; existing optimizer fuses + kernel-certifies it. No new IR code, no new proofs.

(defn- xform-steps
  "Flatten a transducer expression to an ordered vector of single stages. Each
   stage is `(map f)`, `(filter p)`, or `(remove p)` (arity-1 — the transducer
   form, NOT the eager `(map f coll)`); `comp` nests left-to-right (the leftmost
   stage sees each element first)."
  [form]
  (cond
    (and (seq? form) (= 'comp (first form)))
    (vec (mapcat xform-steps (rest form)))
    (and (seq? form) (#{'map 'filter 'remove} (first form)) (= 2 (count form)))
    [form]
    :else
    (throw (ex-info (str "Unsupported transducer: " (pr-str form)
                         " — supported stages are (map f), (filter p), (remove p), composed with comp")
                    {:form form}))))

(defn- xform->form
  "Build the nested collection FORM a transducer stack denotes when run over
   `coll-form`: fold the stages left-to-right, each wrapping the accumulator
   (leftmost = innermost data transform = first applied)."
  [coll-form steps]
  (reduce (fn [acc st]
            (case (first st)
              map    (list 'mapv (second st) acc)
              filter (list 'filterv (second st) acc)
              ;; remove p = filter (Bool.not ∘ p). Negate an inline predicate's
              ;; body directly (sexp->ansatz has no surface beta-redex, so we
              ;; can't wrap-and-apply an arbitrary p); require an inline fn.
              remove (let [p (second st)]
                       (if (and (seq? p) (#{'fn 'fn*} (first p)) (vector? (second p)) (= 3 (count p)))
                         (list 'filterv (list 'fn (second p) (list 'Bool.not (nth p 2))) acc)
                         (throw (ex-info "remove currently requires an inline (fn [x] …) predicate"
                                         {:pred p}))))))
          coll-form steps))

(defn- into-elaborator [env scope depth args lctx]
  ;; (into [] xform coll)  or  (into [] coll). Only the vector target [] (eager
  ;; realization into a fresh vector) is supported — the result IS the transformed list.
  (let [target (first args)]
    (when-not (and (vector? target) (empty? target))
      (throw (ex-info "Only (into [] xform? coll) is supported in a verified body"
                      {:target target})))
    (case (count args)
      2 (a/sexp->ansatz env scope depth (nth args 1) lctx)
      3 (a/sexp->ansatz env scope depth
                        (xform->form (nth args 2) (xform-steps (nth args 1))) lctx)
      (throw (ex-info "into: expected (into [] coll) or (into [] xform coll)" {:args args})))))

(defn- transduce-elaborator [env scope depth args lctx]
  ;; (transduce xform rf init coll) → reduce rf init over the transformed list.
  (when-not (= 4 (count args))
    (throw (ex-info "transduce: expected (transduce xform rf init coll)" {:args args})))
  (let [[xform rf init coll] args]
    (a/sexp->ansatz env scope depth
                    (list 'reduce rf init (xform->form coll (xform-steps xform))) lctx)))

(defn- sequence-elaborator [env scope depth args lctx]
  ;; (sequence xform coll) → the transformed list.
  (when-not (= 2 (count args))
    (throw (ex-info "sequence: expected (sequence xform coll)" {:args args})))
  (a/sexp->ansatz env scope depth
                  (xform->form (second args) (xform-steps (first args))) lctx))

;; ── more clojure.core vocabulary: prefix/suffix + head/tail ──────────────────
;; Each maps to the corresponding Lean List op (the verified DENOTATION) and lowers to
;; the Clojure runtime op. take/take-while/drop are LAZY in Clojure, so a bounded terminal
;; like `(take n …)` makes an INFINITE lazy pipeline fully consumable (streams n elements).

(defn- take-elaborator [env scope depth args lctx]
  ;; (take n coll) → List.take α n coll
  (let [[n-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        n (a/sexp->ansatz env scope depth n-form lctx)]
    (e/app* (e/const' (nm "List.take") [(univ env a)]) a n coll)))

(defn- nth-elaborator [env scope depth args lctx]
  ;; (nth coll i default) → List.getD α coll i default : α  (index with a default; α inferred).
  ;; The 3-arg form — 2-arg nth (throw on OOB) would need List.get with a bounds proof.
  (let [[coll-form i-form d-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        i (a/sexp->ansatz env scope depth i-form lctx)
        d (a/sexp->ansatz env scope depth d-form lctx)]
    (e/app* (e/const' (nm "List.getD") [(univ env a)]) a coll i d)))

(defn- range-elaborator [env scope depth args lctx]
  ;; (range n) → List.range n : List Nat  — [0, 1, …, n-1]
  (e/app* (e/const' (nm "List.range") []) (a/sexp->ansatz env scope depth (first args) lctx)))

(defn- drop-elaborator [env scope depth args lctx]
  (let [[n-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        n (a/sexp->ansatz env scope depth n-form lctx)]
    (e/app* (e/const' (nm "List.drop") [(univ env a)]) a n coll)))

(defn- reverse-elaborator [env scope depth args lctx]
  ;; (reverse coll) → List.reverse α coll
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (list-elem env coll)]
    (e/app* (e/const' (nm "List.reverse") [(univ env a)]) a coll)))

(defn- concat-elaborator [env scope depth args lctx]
  ;; (concat a b) → List.append α a b  (2-ary; nested for more)
  (let [colls (map #(a/sexp->ansatz env scope depth % lctx) args)
        a (list-elem env (first colls))
        u (univ env a)]
    (reduce (fn [acc c] (e/app* (e/const' (nm "List.append") [u]) a acc c)) colls)))

(defn- interpose-elaborator [env scope depth args lctx]
  ;; (interpose sep coll) → List.intersperse α sep coll
  (let [[sep-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        sep (a/sexp->ansatz env scope depth sep-form lctx)]
    (e/app* (e/const' (nm "List.intersperse") [(univ env a)]) a sep coll)))

(defn- take-while-elaborator [env scope depth args lctx]
  ;; (take-while p coll) → List.takeWhile α p coll   (p : α → Bool)
  (let [[p-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        p (compile-fn env scope depth p-form [a] lctx)]
    (e/app* (e/const' (nm "List.takeWhile") [(univ env a)]) a p coll)))

(defn- drop-while-elaborator [env scope depth args lctx]
  (let [[p-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        p (compile-fn env scope depth p-form [a] lctx)]
    (e/app* (e/const' (nm "List.dropWhile") [(univ env a)]) a p coll)))

(defn- prod-elems
  "The component types [α β] of a `p` of inferred type `Prod α β`, or nil."
  [env p]
  (let [t (a/get-arg-type env nil p)
        [h args] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h) (= "Prod" (name/->string (e/const-name h))) (>= (count args) 2))
      [(first args) (second args)])))

(defn- first-elaborator [env scope depth args lctx]
  ;; (first x) — Clojure-style, dispatching on the receiver: a List → List.head? α x : Option α
  ;; (none/nil for empty); a Prod (a pair, sequential in Clojure) → Prod.fst α β x : α.
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)]
    (if-let [[a b] (prod-elems env coll)]
      (e/app* (e/const' (nm "Prod.fst") [(univ env a) (univ env b)]) a b coll)
      (let [a (list-elem env coll)]
        (e/app* (e/const' (nm "List.head?") [(univ env a)]) a coll)))))

(defn- second-elaborator [env scope depth args lctx]
  ;; (second x) — a List → its 2nd element (head? of the tail) : Option α; a Prod → Prod.snd : β.
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)]
    (if-let [[a b] (prod-elems env coll)]
      (e/app* (e/const' (nm "Prod.snd") [(univ env a) (univ env b)]) a b coll)
      (let [a (list-elem env coll) u (univ env a)]
        (e/app* (e/const' (nm "List.head?") [u]) a
                (e/app* (e/const' (nm "List.tail") [u]) a coll))))))

(defn- rest-elaborator [env scope depth args lctx]
  ;; (rest xs) → List.tail α xs : List α  (Clojure's rest — empty list for empty/singleton).
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (list-elem env coll)]
    (e/app* (e/const' (nm "List.tail") [(univ env a)]) a coll)))

(defn- last-elaborator [env scope depth args lctx]
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (list-elem env coll)]
    (e/app* (e/const' (nm "List.getLast?") [(univ env a)]) a coll)))

(defn- rest-elaborator [env scope depth args lctx]
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (list-elem env coll)]
    (e/app* (e/const' (nm "List.tail") [(univ env a)]) a coll)))

(defn- map-indexed-elaborator [env scope depth args lctx]
  ;; (map-indexed f coll) → List.mapIdx α β f coll   (f : Nat → α → β, f index elem)
  (let [[f-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        nat (e/const' (nm "Nat") [])
        f (compile-fn env scope depth f-form [nat a] lctx)
        ftype (a/get-arg-type env nil f)                    ; Nat → α → β
        b (a/whnf-ty env (e/forall-body (e/forall-body ftype)))]            ; β
    (e/app* (e/const' (nm "List.mapIdx") [(univ env a) (univ env b)]) a b f coll)))

(defn- mapcat-elaborator [env scope depth args lctx]
  ;; (mapcat f coll) → List.flatMap α β f coll   (f : α → List β)
  (let [[f-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (list-elem env coll)
        f (compile-fn env scope depth f-form [a] lctx)
        cod (a/whnf-ty env (e/forall-body (a/get-arg-type env nil f)))      ; codomain: List β
        [_ ca] (e/get-app-fn-args cod)
        b (first ca)]                                       ; β
    (e/app* (e/const' (nm "List.flatMap") [(univ env a) (univ env b)]) a b f coll)))

;; NOTE: `keep` is intentionally UNsupported. Clojurians use it with a nil-punning predicate
;; (#(when (even? %) %)) — i.e. PRODUCE an Option via nil — which the Option layer doesn't model
;; (it CONSUMES Option via narrowing, not produces). Unregistered, it fails transparently
;; ("Unknown: keep"). The List.filterMap codegen exists for when an Option-producing form lands.

;; ── threading: ->/->> are GENERAL surface forms (not record-specific), so they live in the
;; base collection ns — keeps `->` from silently degrading to the type-arrow when records
;; isn't loaded. (Type arrows use the `arrow` keyword.)
(defn- thread-first [x forms]
  (reduce (fn [acc form] (if (seq? form) (list* (first form) acc (rest form)) (list form acc))) x forms))
(defn- thread-last [x forms]
  (reduce (fn [acc form] (if (seq? form) (concat form [acc]) (list form acc))) x forms))
(defn- arrow-elaborator [thread-fn]
  (fn [env scope depth args lctx]
    (a/sexp->ansatz env scope depth (thread-fn (first args) (rest args)) lctx)))

(defn install!
  "Register the collection-op elaborators (idempotent)."
  []
  (a/register-elaborator! '-> (arrow-elaborator thread-first))
  (a/register-elaborator! '->> (arrow-elaborator thread-last))
  (a/register-elaborator! 'count count-elaborator)
  (a/register-elaborator! 'reduce reduce-elaborator)
  (a/register-elaborator! 'reductions reductions-elaborator)
  (a/register-elaborator! 'mapv mapv-elaborator)
  (a/register-elaborator! 'filterv filterv-elaborator)
  ;; bare `map`/`filter` aliases — verified pipelines are eager (no laziness), so over a single
  ;; collection these mean the same as mapv/filterv. (Variadic `map` = zip is not modeled.)
  (a/register-elaborator! 'map mapv-elaborator)
  (a/register-elaborator! 'filter filterv-elaborator)
  (a/register-elaborator! 'take take-elaborator)
  (a/register-elaborator! 'nth nth-elaborator)
  (a/register-elaborator! 'range range-elaborator)
  (a/register-elaborator! 'drop drop-elaborator)
  (a/register-elaborator! 'reverse reverse-elaborator)
  (a/register-elaborator! 'concat concat-elaborator)
  (a/register-elaborator! 'interpose interpose-elaborator)
  (a/register-elaborator! 'take-while take-while-elaborator)
  (a/register-elaborator! 'drop-while drop-while-elaborator)
  (a/register-elaborator! 'first first-elaborator)
  (a/register-elaborator! 'second second-elaborator)
  (a/register-elaborator! 'rest rest-elaborator)
  (a/register-elaborator! 'last last-elaborator)
  (a/register-elaborator! 'rest rest-elaborator)
  (a/register-elaborator! 'mapcat mapcat-elaborator)        ; keep: see note above (unsupported)
  (a/register-elaborator! 'map-indexed map-indexed-elaborator)
  ;; transducer surface (desugars to the nested SOAC form above)
  (a/register-elaborator! 'into into-elaborator)
  (a/register-elaborator! 'transduce transduce-elaborator)
  (a/register-elaborator! 'sequence sequence-elaborator))

(install!)
