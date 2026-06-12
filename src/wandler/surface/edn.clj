;; A native formalization of the EDN / Clojure value universe in Ansatz.
;;
;; Clojure's data is essentially EDN: nil, booleans, numbers, strings, keywords,
;; symbols, lists/vectors, maps, sets. We model the whole universe as a single
;; inductive `Value` (cons-cell style, since Ansatz's `a/inductive` supports
;; direct recursion but not nesting under `List`). Every Clojure value is a
;; `Value`; every core operation is a total function over `Value`s.
;;
;; This is the foundation for verified optimization of real Clojure data
;; pipelines: the runtime↔kernel bridge is just an ENCODING (the kernel `Value`
;; IS the EDN AST), the tightest possible link.
;;
;; Map representation: an entry-chain (`ventry k v rest` … `vnil`) tagged by
;; `vmap`. `vassoc` prepends (shadowing); `vget1` reads the head. Canonical
;; (sorted, deduped) maps with scanning `get`/`dissoc` and decidable key equality
;; are the next layer.
;;
;; Requires the env seeded with Lean `Init` (Nat, Bool, Int, String). Call
;; `install-core!` after `(a/init! …)` or after replaying an Init export.

(ns wandler.surface.edn
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]))

(def ^:private core-forms
  '[;; The EDN value universe. (vfloat/vset appended last to keep ctor indices stable.)
    (ansatz.core/inductive Value []
                           (vnil)
                           (vbool [b Bool])
                           (vint  [i Int])
                           (vstr  [s String])
                           (vkw   [s String])
                           (vcons [head Value] [tail Value])        ;; list/vector payload
                           (vvec  [items Value])
                           (vmap  [entries Value])                  ;; tag an entry-chain as a map
                           (ventry [k Value] [v Value] [rest Value])
                           (vfloat [f Float])                       ;; EDN double
                           (vset  [items Value]))                   ;; tag a cons-chain as a set

    ;; assoc = prepend an entry (shadowing semantics).
    (ansatz.core/defn vassoc [m :- Value, k :- Value, v :- Value] Value
      (Value.ventry k v m))

    ;; map-level put — `(assoc mapValue k v)`: prepend into the vmap's entry-chain (shadowing),
    ;; re-tagging as a vmap. A non-map receiver becomes a fresh single-entry map (assoc nil → {}).
    (ansatz.core/defn vput [m :- Value, k :- Value, val :- Value] Value
      (match m Value Value
        (vnil (Value.vmap (Value.ventry k val (Value.vnil))))
        (vbool [b] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vint [i] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vstr [s] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vkw [s] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vcons [h t] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vvec [it] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vmap [e] (Value.vmap (Value.ventry k val e)))
        (ventry [ek ev r] (Value.vmap (Value.ventry k val m)))
        (vfloat [f] (Value.vmap (Value.ventry k val (Value.vnil))))
        (vset [it] (Value.vmap (Value.ventry k val (Value.vnil))))))

    ;; get-head: the value of the first entry (vnil if not a map-entry).
    (ansatz.core/defn vget1 [m :- Value] Value
      (match m Value Value
             (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil))
             (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil)) (vcons [h t] (Value.vnil))
             (vvec [it] (Value.vnil)) (vmap [en] (Value.vnil)) (ventry [k v r] v)
             (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))

    ;; Structural node count — recursive (compiles via the auto-sizeOf measure).
    (ansatz.core/defn vcount [m :- Value] Nat
      :termination-by m
      (match m Value Nat
             (vnil 0) (vbool [b] 0) (vint [i] 0) (vstr [s] 0) (vkw [s] 0)
             (vcons [h t] (Nat.succ (Nat.add (vcount h) (vcount t))))
             (vvec [it] (Nat.succ (vcount it)))
             (vmap [en] (Nat.succ (vcount en)))
             (ventry [k v r] (Nat.succ (Nat.add (vcount k) (Nat.add (vcount v) (vcount r)))))
             (vfloat [f] 0) (vset [it] (Nat.succ (vcount it)))))

    ;; First law: get-after-assoc holds definitionally (assoc prepends, get reads
    ;; the head), discharged by rfl.
    (ansatz.core/theorem vget-vassoc [m :- Value, k :- Value, v :- Value]
                         (= Value (vget1 (vassoc m k v)) v)
                         (rfl))

    ;; ── SCHEMA-AS-REFINEMENT layer: a malli schema is a conformance PREDICATE over Value.
    ;; Type predicates (match on the constructor).
    (ansatz.core/defn vint?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] true)  (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vstr?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] true)  (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vbool?  [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] true)  (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vmap?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] true)  (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vnil?   [v :- Value] Bool (match v Value Bool (vnil true)  (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vkw?    [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] true)  (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vvec?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] true)  (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn vfloat? [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] true)  (vset [it] false)))
    (ansatz.core/defn vset?   [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] true)))
    ;; :any (always true) and :some (non-nil).
    (ansatz.core/defn vany?  [v :- Value] Bool true)
    (ansatz.core/defn vsome? [v :- Value] Bool (match v Value Bool (vnil false) (vbool [b] true)  (vint [i] true)  (vstr [s] true)  (vkw [s] true)  (vcons [h t] true)  (vvec [it] true)  (vmap [e] true)  (ventry [k w r] true) (vfloat [f] true) (vset [it] true)))

    ;; Decidable structural equality over the whole Value universe (for :enum / := / :not=).
    ;; Scalars compared by ==/Bool-iff; compounds by structural recursion. Total (fuel on x).
    ;; ^:partial: veq IS structurally terminating (every recursive call is on a field
    ;; of x), but the kernel-enforced WF encoder currently can't afford the 11x11
    ;; nested-match refinement (121 branches x embedded decrease proofs) — encoder
    ;; scaling is a filed follow-up. The TYPE is still kernel-checked.
    (ansatz.core/defn ^:partial veq [x :- Value, y :- Value] Bool
      (match x Value Bool
        (vnil (match y Value Bool (vnil true) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vbool [b1] (match y Value Bool (vnil false) (vbool [b2] (if b1 b2 (not b2))) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vint [i1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i2] (== i1 i2)) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vstr [s1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s2] (== s1 s2)) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vkw [s1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s2] (== s1 s2)) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vcons [h1 t1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h2 t2] (and (veq h1 h2) (veq t1 t2))) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vvec [it1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it2] (veq it1 it2)) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vmap [e1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e2] (veq e1 e2)) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (ventry [k1 v1 r1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k2 v2 r2] (and (veq k1 k2) (and (veq v1 v2) (veq r1 r2)))) (vfloat [f] false) (vset [it] false)))
        (vfloat [f1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f2] (== f1 f2)) (vset [it] false)))
        (vset [it1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it2] (veq it1 it2))))))

    ;; Scalar extractors — pull a primitive out of a Value (default for the wrong ctor; under a
    ;; conforms refinement the default is unreachable). Let native arithmetic/compare on EDN
    ;; fields work: `(< 18 (:age r))` elaborates the Value field via `vint-val`.
    (ansatz.core/defn vint-val [v :- Value] Int
      (match v Value Int (vnil (Int.ofNat 0)) (vbool [b] (Int.ofNat 0)) (vint [i] i) (vstr [s] (Int.ofNat 0)) (vkw [s] (Int.ofNat 0)) (vcons [h t] (Int.ofNat 0)) (vvec [it] (Int.ofNat 0)) (vmap [e] (Int.ofNat 0)) (ventry [k w r] (Int.ofNat 0)) (vfloat [f] (Int.ofNat 0)) (vset [it] (Int.ofNat 0))))
    (ansatz.core/defn vfloat-val [v :- Value] Float
      (match v Value Float (vnil 0.0) (vbool [b] 0.0) (vint [i] 0.0) (vstr [s] 0.0) (vkw [s] 0.0) (vcons [h t] 0.0) (vvec [it] 0.0) (vmap [e] 0.0) (ventry [k w r] 0.0) (vfloat [f] f) (vset [it] 0.0)))
    (ansatz.core/defn vstr-val [v :- Value] String
      (match v Value String (vnil "") (vbool [b] "") (vint [i] "") (vstr [s] s) (vkw [s] s) (vcons [h t] "") (vvec [it] "") (vmap [e] "") (ventry [k w r] "") (vfloat [f] "") (vset [it] "")))
    (ansatz.core/defn vbool-val [v :- Value] Bool
      (match v Value Bool (vnil false) (vbool [b] b) (vint [i] false) (vstr [s] false) (vkw [s] false) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))

    ;; Element count — `(count v)` over a Value. vchain-len walks a vcons/ventry chain; vsize
    ;; gives the top-level element count (vstr → its String.length, like Clojure `count`).
    (ansatz.core/defn vchain-len [c :- Value] Nat
      :termination-by c (match c Value Nat (vnil 0) (vbool [b] 0) (vint [i] 0) (vstr [s] 0) (vkw [s] 0)
        (vcons [h t] (Nat.succ (vchain-len t))) (vvec [it] 0) (vmap [e] 0)
        (ventry [k v r] (Nat.succ (vchain-len r))) (vfloat [f] 0) (vset [it] 0)))
    (ansatz.core/defn vsize [v :- Value] Nat
      (match v Value Nat (vnil 0) (vbool [b] 0) (vint [i] 0) (vstr [s] (String.length s)) (vkw [s] 0)
        (vcons [h t] (Nat.succ (vchain-len t))) (vvec [it] (vchain-len it)) (vmap [e] (vchain-len e))
        (ventry [k v r] 0) (vfloat [f] 0) (vset [it] (vchain-len it))))

    ;; Key equality (keyword keys via String ==).
    (ansatz.core/defn vkeq [x :- Value, y :- Value] Bool
      (match x Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false)
        (vkw [s1] (match y Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false)
                    (vkw [s2] (== s1 s2)) (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))
        (vcons [h t] false) (vvec [it] false) (vmap [e] false) (ventry [k w r] false) (vfloat [f] false) (vset [it] false)))

    ;; Per-type key checkers — "key k of map m holds a value of type T". Bool-returning
    ;; RECURSION over the entry-chain (Value-returning vget hits the custom-recursion gap, so
    ;; we inline the type-check instead). One per scalar malli type.
    (ansatz.core/defn key-int? [k :- Value, m :- Value] Bool
      :termination-by m (match m Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false)
        (vcons [h t] false) (vvec [it] false) (vmap [en] (key-int? k en))
        (ventry [ek ev rest] (if (vkeq k ek) (vint? ev) (key-int? k rest))) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn key-str? [k :- Value, m :- Value] Bool
      :termination-by m (match m Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false)
        (vcons [h t] false) (vvec [it] false) (vmap [en] (key-str? k en))
        (ventry [ek ev rest] (if (vkeq k ek) (vstr? ev) (key-str? k rest))) (vfloat [f] false) (vset [it] false)))
    (ansatz.core/defn key-bool? [k :- Value, m :- Value] Bool
      :termination-by m (match m Value Bool (vnil false) (vbool [b] false) (vint [i] false) (vstr [s] false) (vkw [s] false)
        (vcons [h t] false) (vvec [it] false) (vmap [en] (key-bool? k en))
        (ventry [ek ev rest] (if (vkeq k ek) (vbool? ev) (key-bool? k rest))) (vfloat [f] false) (vset [it] false)))

    ;; vget — lookup key `k` in map `m`, returning the VALUE (vnil if absent). A general
    ;; Value-RETURNING recursion (works since the #58 fuel-base-case fix).
    (ansatz.core/defn vget [k :- Value, m :- Value] Value
      :termination-by m (match m Value Value (vnil (Value.vnil)) (vbool [b] (Value.vnil)) (vint [i] (Value.vnil))
        (vstr [s] (Value.vnil)) (vkw [s] (Value.vnil)) (vcons [h t] (Value.vnil)) (vvec [it] (Value.vnil))
        (vmap [en] (vget k en))
        (ventry [ek ev rest] (if (vkeq k ek) ev (vget k rest))) (vfloat [f] (Value.vnil)) (vset [it] (Value.vnil))))])

;; ── malli schema → Value conformance predicate ────────────────────────────────
;; A malli schema becomes a REFINEMENT over the Value universe: a kernel-verifiable
;; `Value → Bool` conformance predicate. The compiler is recursive over the schema —
;; scalars reuse the hand-written value-predicates / key-checkers, while nested maps,
;; homogeneous vectors, and optional fields generate fresh helper predicates (each a
;; fuel-recursive `a/defn` over Value that BOTH kernel-verifies and runs, post-#59).

(def ^:private scalar-pred
  "Malli scalar KEYWORD schema → the kernel value-predicate name (Value → Bool)."
  {:int 'vint? :string 'vstr? :boolean 'vbool? :keyword 'vkw? :nil 'vnil?
   :any 'vany? :some 'vsome? :map 'vmap? :double 'vfloat? :float 'vfloat?})

(def ^:private predicate-pred
  "Malli predicate-SYMBOL schema → kernel value-predicate name. Note `:int`/`int?`/`integer?`
   all map to `vint?`: `Value.vint` models an EDN integer *value* (arbitrary precision), so the
   host numeric-tower distinction (Long vs BigInt) is erased by design — faithful on the EDN
   value domain, which is what `Value` models. `double?`/`float?` → `vfloat?` (EDN double)."
  {'int? 'vint? 'integer? 'vint? 'string? 'vstr? 'boolean? 'vbool? 'keyword? 'vkw? 'nil? 'vnil?
   'any? 'vany? 'some? 'vsome? 'map? 'vmap? 'vector? 'vvec? 'set? 'vset?
   'double? 'vfloat? 'float? 'vfloat?})

(def ^:private predicate-range
  "Predicate symbols that mean `:int` + an integer range."
  {'pos-int? {:min 1} 'neg-int? {:max -1} 'nat-int? {:min 0}})

(def ^:private fn->sym
  "Known clojure.core predicate FUNCTIONS → their schema symbol, so an UNQUOTED predicate in a
   malli schema written as data (e.g. `[:tuple pos-int? …]`, where `pos-int?` evals to the fn
   object) is resolved like the symbol form. Unknown fns fall through to a trusted `:fn` leaf."
  {int? 'int? integer? 'integer? string? 'string? boolean? 'boolean? keyword? 'keyword?
   nil? 'nil? any? 'any? some? 'some? map? 'map? vector? 'vector? set? 'set?
   double? 'double? float? 'float? pos-int? 'pos-int? nat-int? 'nat-int? neg-int? 'neg-int?})

(def ^:private scalar-key-checker
  "Malli scalar schema → the hand-written `key-<T>?` checker (keeps flat output identical)."
  {:int 'key-int? :string 'key-str? :boolean 'key-bool?})

(defn- kw-str [k] (subs (str k) 1))   ;; full keyword incl. namespace, matching edn->value

(defn- flit
  "Surface Float literal expr for `x`. The frontend has no negative Float literal, so emit
   negatives as `(sub Float 0.0 |x|)`."
  [x]
  (if (and (number? x) (neg? x)) (list 'sub 'Float 0.0 (double (- x))) x))

(defn- edn->value-form
  "Compile-time Clojure literal → a SURFACE `Value` constructor expr (for :enum / := literals).
   Mirrors `edn->value` but emits `(Value.vint 3)`-style forms instead of the runtime rep."
  [x]
  (cond
    (nil? x)        '(Value.vnil)
    (boolean? x)    (list 'Value.vbool x)
    (integer? x)    (list 'Value.vint x)
    (string? x)     (list 'Value.vstr x)
    (keyword? x)    (list 'Value.vkw (kw-str x))
    (double? x)     (list 'Value.vfloat (flit x))
    (map? x)        (list 'Value.vmap (reduce (fn [acc [k v]]
                                                (list 'Value.ventry (edn->value-form k)
                                                      (edn->value-form v) acc))
                                              '(Value.vnil) (reverse (seq x))))
    (set? x)        (list 'Value.vset (reduce (fn [acc e] (list 'Value.vcons (edn->value-form e) acc))
                                              '(Value.vnil) (reverse (seq x))))
    (sequential? x) (list 'Value.vvec (reduce (fn [acc e] (list 'Value.vcons (edn->value-form e) acc))
                                              '(Value.vnil) (reverse (seq x))))
    :else (throw (ex-info "edn->value-form: unsupported literal" {:x x}))))

(defn- parse-schema
  "Malli node → {:type :props :args}. `[type ?props & children]`, bare keyword/symbol, or a
   raw value (treated as a `:=` literal — malli allows literal schemas)."
  [node]
  (cond
    (keyword? node) {:type node :props nil :args []}
    (symbol? node)  {:type node :props nil :args []}
    (fn? node)      (if-let [s (fn->sym node)] {:type s :props nil :args []}
                            {:type :fn :props nil :args [node]})   ;; unknown fn → trusted leaf
    (and (vector? node) (or (keyword? (first node)) (symbol? (first node))))
    (let [[props args] (if (map? (second node)) [(second node) (drop 2 node)] [nil (rest node)])]
      {:type (first node) :props props :args (vec args)})
    :else {:type := :props nil :args [node]}))   ;; literal value schema

(def ^:private value-ctors
  [['vnil 0] ['vbool 1] ['vint 1] ['vstr 1] ['vkw 1] ['vcons 2] ['vvec 1] ['vmap 1] ['ventry 3]
   ['vfloat 1] ['vset 1]])

(defn- vmatch
  "A `(match disc Value Bool …)` returning `dflt` for every ctor except those in `overrides`
   (ctor-sym → tail: `(body)` for nullary, `([binders] body)` otherwise)."
  [disc dflt overrides]
  (list* 'match disc 'Value 'Bool
         (map (fn [[c ar]]
                (cons c (or (get overrides c)
                            (if (zero? ar) (list dflt)
                                (list (vec (repeatedly ar #(gensym "_g"))) dflt)))))
              value-ctors)))

(defn- and-chain [calls] (if (empty? calls) true  (reduce (fn [a c] (list 'and a c)) (first calls) (rest calls))))
(defn- or-chain  [calls] (if (empty? calls) false (reduce (fn [a c] (list 'or  a c)) (first calls) (rest calls))))

(defn- closed-checker-form
  "A fuel-recursive checker `nm : (c : Value) → Bool` — every entry key of chain `c` equals one
   of `key-forms` (the declared `(Value.vkw …)` keys). Empty key-forms → only vnil passes."
  [nm key-forms]
  (list 'ansatz.core/defn nm ['c :- 'Value] 'Bool
        :termination-by 'c
        (vmatch 'c false
                {'vnil   (list true)
                 'ventry (list ['k 'v 'rest]
                               (list 'and (or-chain (map (fn [ke] (list 'veq 'k ke)) key-forms))
                                     (list nm 'rest)))})))

(defn- tuple-chain
  "Nested fixed-depth match over the cons-chain `disc`: position i must satisfy `(nth preds i)`
   and the chain must end (vnil) exactly after the last. Empty preds → require vnil."
  [preds disc]
  (if (empty? preds)
    (vmatch disc false {'vnil (list true)})
    (let [h (gensym "h__") t (gensym "t__")]
      (vmatch disc false
              {'vcons (list [h t] (list 'and (list (first preds) h)
                                        (tuple-chain (rest preds) t)))}))))

(defn- mapof-checker-form
  "A fuel-recursive checker `nm : (c : Value) → Bool` — every entry of chain `c` has key ⊢
   kpred and value ⊢ vpred (vnil terminator → true)."
  [nm kpred vpred]
  (list 'ansatz.core/defn nm ['c :- 'Value] 'Bool
        :termination-by 'c
        (vmatch 'c false
                {'vnil   (list true)
                 'ventry (list ['k 'v 'rest]
                               (list 'and (list kpred 'k)
                                     (list 'and (list vpred 'v) (list nm 'rest))))})))

(defn- key-checker-form
  "A fuel-recursive checker `nm : (k m : Value) → Bool` — walk map `m`'s entry-chain; at the
   entry whose key = k, return `(sub-pred ev)`. `absent?` true → key may be absent (optional)."
  [nm sub-pred optional?]
  (let [d (if optional? true false)]
    (list 'ansatz.core/defn nm ['k :- 'Value 'm :- 'Value] 'Bool
          :termination-by 'm
          (vmatch 'm d {'vmap   (list ['en] (list nm 'k 'en))
                        'ventry (list ['ek 'ev 'rest]
                                      (list 'if (list 'vkeq 'k 'ek)
                                            (list sub-pred 'ev) (list nm 'k 'rest)))}))))

(defn- all-checker-form
  "A fuel-recursive checker `nm : (c : Value) → Bool` — every element of the cons-chain `c`
   satisfies `sub-pred` (vnil terminator → true)."
  [nm sub-pred]
  (list 'ansatz.core/defn nm ['c :- 'Value] 'Bool
        :termination-by 'c
        (vmatch 'c false {'vnil  (list true)
                          'vcons (list ['h 't] (list 'and (list sub-pred 'h) (list nm 't)))})))

(defn- vec-checker-form
  "A (non-recursive) checker `nm : (v : Value) → Bool` — v is a `vvec` whose elements all
   satisfy the cons-chain checker `all-name`."
  [nm all-name]
  (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool
        (vmatch 'v false {'vvec (list ['it] (list all-name 'it))})))

(defn- set-checker-form
  "A (non-recursive) checker `nm : (v : Value) → Bool` — v is a `vset` whose elements all
   satisfy the cons-chain checker `all-name`."
  [nm all-name]
  (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool
        (vmatch 'v false {'vset (list ['it] (list all-name 'it))})))

(declare compile-schema)

(defn- compile-field
  "[check forms] for one map field `[k (opts?) t]`. `check` is the boolean expr over `v`;
   `forms` are helper a/defns that must be defined first."
  [[k & more]]
  (let [opts      (when (map? (first more)) (first more))
        t         (if opts (second more) (first more))
        optional? (boolean (:optional opts))
        kexpr     (list 'Value.vkw (kw-str k))]
    (if (and (not optional?) (scalar-key-checker t))
      ;; required scalar field → reuse the hand-written key-<T>? (flat output stays identical)
      [(list (scalar-key-checker t) kexpr 'v) []]
      ;; otherwise compile the sub-schema's predicate and wrap it in a key-checker
      (let [[sub sub-forms] (compile-schema t)
            kc (gensym (if optional? "key_opt__" "key_req__"))]
        [(list kc kexpr 'v)
         (conj (vec sub-forms) (key-checker-form kc sub optional?))]))))

(defn- def-pred
  "A `[nm [form]]` pair defining `nm : Value → Bool` with `body` (over the param `v`),
   appended after `dep-forms`."
  [nm dep-forms body]
  [nm (conj (vec dep-forms) (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool body))])

;; The verified `:re` leaf (#63). When the regex matcher is installed in the CURRENT env (ansatz.
;; regex/install! added `reMatchStr`), `[:re p]` compiles to `(and (vstr? target) <p matches>)`
;; via the kernel Brzozowski matcher — PRECISE (agrees with malli's `:re`). Otherwise it stays the
;; trusted-string leaf (`vstr?`, over-approximating). Gated on the ENV (not a global), so it is
;; properly test-isolated: a test that resets the env without installing regex gets `vstr?`.
(defn- re-leaf-fn []
  (when (env/lookup (a/env) (name/from-string "reMatchStr"))
    (resolve 'wandler.regex/re-conforms-leaf)))

;; ── inline (recursion) compiler ───────────────────────────────────────────────
;; For a SELF-recursive schema we cannot route refs through separate predicates (the kernel's
;; `:termination-by` is single-function), so we INLINE the schema body into one recursive
;; `Value → Bool` over `v`, where `[:ref ::self]` becomes `(fname subterm)` — and every such
;; call is on a MATCH-BOUND strict subterm, so `:termination-by v` (structural) accepts it.
;; The inlined target is always a bound variable (we descend only through match bindings), so
;; ranges/tuples can re-match it safely. Refs nested inside :vector/:map/:map-of need mutual
;; recursion (a follow-up) and are rejected here.
(defn- range-body
  "AND-chain of `{:min :max}` bounds applied to the scalar accessor expr `acc` (e.g. `i` or
   `(String.length s)`); `true` if unconstrained. A bound may be a literal or a surface expr."
  [props acc]
  (let [g (cond-> []
            (contains? props :min) (conj (list '<= (:min props) acc))
            (contains? props :max) (conj (list '<= acc (:max props))))]
    (if (seq g) (and-chain g) true)))

(defn- float-props
  "Float `{:min :max}` with negative bounds rewritten to surface exprs (no negative Float lit)."
  [props]
  (cond-> props (contains? props :min) (update :min flit) (contains? props :max) (update :max flit)))

(declare parse-schema)

(defn- compile-recursive
  "Compile a malli `:schema` recursive node — a local `registry` plus a top `[:ref ::name]` —
   into one `fname : Value → Bool` predicate. The kernel's `:termination-by` is single-function,
   so the WHOLE reference graph becomes one `rcheck : (mode : Nat) (v : Value) → Bool`: every
   registry entry and every collection/field iteration context gets an integer MODE; refs and
   iteration steps are `(rcheck m subterm)` (always a match-bound strict subterm of `v`, so
   structural `:termination-by v` accepts them). Non-iterating constructs are inlined on the
   current target. Supports (mutually) recursive maps/vectors/tuples/map-of/multi — trees, JSON."
  [registry top-ref fname]
  (let [rcheck     (gensym "rcheck__")
        modes      (atom [])                 ;; index = mode number, value = body expr over `v`
        name->mode (atom {})
        alloc!     (fn [] (let [m (count @modes)] (swap! modes conj nil) m))
        call       (fn [m target] (list rcheck m target))]
    (letfn [(gen-tuple [child-schemas disc]
              (if (empty? child-schemas)
                (vmatch disc false {'vnil (list true)})
                (let [h (gensym "h__") t (gensym "t__")]
                  (vmatch disc false
                          {'vcons (list [h t] (list 'and (gen (first child-schemas) h)
                                                    (gen-tuple (rest child-schemas) t)))}))))
            (gen [schema target]
              (let [{:keys [type props args]} (parse-schema schema)
                    leaf (when (and (empty? args) (nil? props)) (or (scalar-pred type) (predicate-pred type)))]
                (cond
                  (= type :ref)
                  (call (or (@name->mode (first args))
                            (throw (ex-info "recursion: unknown :ref" {:ref (first args)}))) target)
                  leaf                     (list leaf target)
                  (predicate-range type)   (vmatch target false {'vint (list ['i] (range-body (predicate-range type) 'i))})
                  (= type :int)            (vmatch target false {'vint (list ['i] (range-body props 'i))})
                  (and (= type :string) props) (vmatch target false {'vstr (list ['s] (range-body props (list 'String.length 's)))})
                  (and (#{:double :float} type) props) (vmatch target false {'vfloat (list ['f] (range-body (float-props props) 'f))})
                  (#{:and :or} type)       ((if (= type :and) and-chain or-chain) (map #(gen % target) args))
                  (= type :not)            (list 'not (gen (first args) target))
                  (= type :maybe)          (list 'or (list 'vnil? target) (gen (first args) target))
                  (= type :enum)           (or-chain (map (fn [lit] (list 'veq target (edn->value-form lit))) args))
                  (= type :=)              (list 'veq target (edn->value-form (first args)))
                  (= type :not=)           (list 'not (list 'veq target (edn->value-form (first args))))
                  (= type :fn)             (list 'vany? target)   ;; trusted leaf (gradual Any)
                  (= type :re)             (if-let [f (re-leaf-fn)]   ;; precise once regex installed
                                             (f (first args) target)
                                             (list 'vstr? target))    ;; else string verified, pattern trusted
                  (= type :tuple)          (vmatch target false {'vvec (list ['it] (gen-tuple args 'it))})

                  ;; iterating constructs — allocate a subterm-recursing mode
                  (#{:vector :sequential :set} type)
                  (let [h (alloc!) e (gensym "h__") t (gensym "t__")
                        gate (if (= type :set) 'vset 'vvec)]
                    (swap! modes assoc h
                           (vmatch 'v false {'vnil  (list true)
                                             'vcons (list [e t] (list 'and (gen (first args) e) (call h t)))}))
                    (vmatch target false {gate (list ['it] (call h 'it))}))

                  (= type :map-of)
                  (let [m (alloc!) k (gensym "k__") val (gensym "v__") r (gensym "r__")]
                    (swap! modes assoc m
                           (vmatch 'v false {'vnil   (list true)
                                             'ventry (list [k val r] (list 'and (gen (first args) k)
                                                                          (list 'and (gen (second args) val) (call m r))))}))
                    (vmatch target false {'vmap (list ['ee] (call m 'ee))}))

                  (= type :map)
                  (let [fmodes (mapv (fn [[fk & more]]
                                       (let [opts (when (map? (first more)) (first more))
                                             fs (if opts (second more) (first more))
                                             optional? (boolean (:optional opts))
                                             fm (alloc!) k (gensym "k__") val (gensym "v__") r (gensym "r__")]
                                         (swap! modes assoc fm
                                                (vmatch 'v (if optional? true false)
                                                        {'ventry (list [k val r]
                                                                       (list 'if (list 'veq k (list 'Value.vkw (kw-str fk)))
                                                                             (gen fs val) (call fm r)))}))
                                         fm))
                                     args)
                        cm (when (:closed props)
                             (let [c (alloc!) k (gensym "k__") val (gensym "v__") r (gensym "r__")
                                   keyfs (map (fn [e] (list 'Value.vkw (kw-str (first e)))) args)]
                               (swap! modes assoc c
                                      (vmatch 'v false {'vnil   (list true)
                                                        'ventry (list [k val r] (list 'and (or-chain (map (fn [ke] (list 'veq k ke)) keyfs)) (call c r)))}))
                               c))
                        e (gensym "e__")
                        checks (cond-> (mapv #(call % e) fmodes) cm (conj (call cm e)))]
                    (vmatch target false {'vmap (list [e] (and-chain checks))}))

                  (= type :multi)
                  (let [dispatch (:dispatch props)
                        _ (when-not (keyword? dispatch)
                            (throw (ex-info "multi: only keyword :dispatch supported" {:dispatch dispatch})))
                        dexpr (list 'vget (list 'Value.vkw (kw-str dispatch)) target)
                        parsed (map (fn [[dval & more]] {:dval dval :bs (if (map? (first more)) (second more) (first more))}) args)
                        default (some #(when (= :malli.core/default (:dval %)) %) parsed)
                        regular (remove #(= :malli.core/default (:dval %)) parsed)
                        els (if default (gen (:bs default) target) false)]
                    (reduce (fn [e {:keys [dval bs]}]
                              (list 'if (list 'veq dexpr (edn->value-form dval)) (gen bs target) e))
                            els (reverse regular)))

                  :else (throw (ex-info "recursion: unsupported schema" {:schema schema :type type})))))]
      ;; pre-assign a mode to each registry entry, then generate their bodies (which allocate
      ;; further helper modes), then build the if-chain dispatch.
      (doseq [[rn _] registry] (swap! name->mode assoc rn (alloc!)))
      (doseq [[rn rs] registry] (swap! modes assoc (@name->mode rn) (gen rs 'v)))
      (let [topmode (or (@name->mode (second top-ref))
                        (throw (ex-info "recursion: top ref names no registry entry" {:top top-ref})))
            dispatch (reduce (fn [els i] (list 'if (list '== 'mode i) (nth @modes i) els))
                             false (reverse (range (count @modes))))]
        [fname [(list 'ansatz.core/defn rcheck ['mode :- 'Nat 'v :- 'Value] 'Bool
                      :termination-by 'v dispatch)
                (list 'ansatz.core/defn fname ['v :- 'Value] 'Bool (list rcheck topmode 'v))]]))))

(defn- compile-schema
  "[pred-sym forms] : a kernel `Value → Bool` predicate for malli `schema`, plus helper a/defn
   forms in dependency order. `top-name` (optional) names the outermost generated predicate.
   Covers: scalar keyword/predicate-symbol schemas; `:and`/`:or`/`:not`/`:maybe`; `:enum`/`:=`/
   `:not=` (via structural `veq`); `:int`/`:string` ranges (`{:min :max}`); `:map` (nested,
   optional fields); `:vector`/`:sequential`. Unsupported nodes throw."
  ([schema] (compile-schema schema nil))
  ([schema top-name]
   (let [{:keys [type props args]} (parse-schema schema)
         nm! (fn [p] (or top-name (gensym p)))
         leaf (when (and (empty? args) (nil? props))
                (or (scalar-pred type) (predicate-pred type)))]
     (cond
       ;; scalar keyword / predicate-symbol leaf → reuse a built-in (caller aliases if top)
       leaf [leaf []]

       ;; predicate symbols that imply an int range (pos-int? / nat-int? / neg-int?)
       (predicate-range type)
       (def-pred (nm! "rng__") [] (vmatch 'v false {'vint (list ['i] (range-body (predicate-range type) 'i))}))

       ;; :int (with range props) — bare :int handled by `leaf`
       (= :int type)
       (def-pred (nm! "rng__") [] (vmatch 'v false {'vint (list ['i] (range-body props 'i))}))

       ;; :string with length props — bare :string handled by `leaf`
       (and (= :string type) props)
       (def-pred (nm! "slen__") [] (vmatch 'v false {'vstr (list ['s] (range-body props (list 'String.length 's)))}))

       ;; :double/:float with range props — bare handled by `leaf`
       (and (#{:double :float} type) props)
       (def-pred (nm! "frng__") [] (vmatch 'v false {'vfloat (list ['f] (range-body (float-props props) 'f))}))

       (#{:and :or} type)
       (let [compiled (mapv compile-schema args)
             calls    (map (fn [[p _]] (list p 'v)) compiled)
             op       (if (= :and type) 'and 'or)]
         (def-pred (nm! (str (name type) "__")) (mapcat second compiled)
           (reduce (fn [a c] (list op a c)) (first calls) (rest calls))))

       (= :not type)
       (let [[p f] (compile-schema (first args))]
         (def-pred (nm! "not__") f (list 'not (list p 'v))))

       (= :maybe type)
       (let [[p f] (compile-schema (first args))]
         (def-pred (nm! "maybe__") f (list 'or (list 'vnil? 'v) (list p 'v))))

       (= :enum type)
       (def-pred (nm! "enum__") []
         (let [calls (map (fn [lit] (list 'veq 'v (edn->value-form lit))) args)]
           (reduce (fn [a c] (list 'or a c)) (first calls) (rest calls))))

       (= := type)    (def-pred (nm! "eq__")  [] (list 'veq 'v (edn->value-form (first args))))
       (= :not= type) (def-pred (nm! "neq__") [] (list 'not (list 'veq 'v (edn->value-form (first args)))))

       ;; :fn — an arbitrary host predicate can't be reflected into the kernel. Compile to a
       ;; TRUSTED leaf (gradual-typing `Any`): always-true, UNVERIFIED at this node, so conforms
       ;; OVER-approximates malli here (accepts ⊇). Use sparingly; the structural part stays proven.
       (= :fn type)   ['vany? []]
       ;; :re — PRECISE once wandler.regex/install! has run (the kernel Brzozowski matcher checks the
       ;; pattern); otherwise the trusted-string leaf (`vstr?`, over-approximating). See *re-leaf-fn*.
       (= :re type)   (if-let [f (re-leaf-fn)]
                        (def-pred (nm! "re__") [] (f (first args) 'v))
                        ['vstr? []])

       (= :map type)
       (let [per     (mapv compile-field args)
             forms   (vec (mapcat second per))
             nm      (nm! "conforms__")
             base    (reduce (fn [acc [check _]] (list 'and acc check)) (list 'vmap? 'v) per)
             closed? (:closed props)
             only-go (when closed? (gensym "onlykeys_go__"))
             keyfs   (when closed? (map (fn [e] (list 'Value.vkw (kw-str (first e)))) args))
             forms   (if closed? (conj forms (closed-checker-form only-go keyfs)) forms)
             body    (if closed?
                       (list 'and base (vmatch 'v false {'vmap (list ['e] (list only-go 'e))}))
                       base)]
         [nm (conj forms (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool body))])

       ;; tagged union: dispatch a KEYWORD key, route to the matching branch schema
       (= :multi type)
       (let [dispatch (:dispatch props)
             _ (when-not (keyword? dispatch)
                 (throw (ex-info "multi: only keyword :dispatch supported" {:dispatch dispatch})))
             dexpr (list 'vget (list 'Value.vkw (kw-str dispatch)) 'v)
             parsed (mapv (fn [[dval & more]]
                            (let [bschema (if (map? (first more)) (second more) (first more))
                                  [bp bf] (compile-schema bschema)]
                              {:dval dval :pred bp :forms bf}))
                          args)
             default (some #(when (= :malli.core/default (:dval %)) %) parsed)
             regular (remove #(= :malli.core/default (:dval %)) parsed)
             else    (if default (list (:pred default) 'v) false)
             body    (reduce (fn [e {:keys [dval pred]}]
                               (list 'if (list 'veq dexpr (edn->value-form dval)) (list pred 'v) e))
                             else (reverse regular))]
         (def-pred (nm! "multi__") (mapcat :forms parsed) body))

       (#{:vector :sequential :set} type)
       (let [[sub sub-forms] (compile-schema (first args))
             allf (gensym "all__")
             gatef (nm! (if (= :set type) "set__" "vec__"))
             gate-form (if (= :set type) set-checker-form vec-checker-form)]
         [gatef (into (vec sub-forms) [(all-checker-form allf sub) (gate-form gatef allf)])])

       ;; fixed-length positional vector
       (= :tuple type)
       (let [compiled (mapv compile-schema args)]
         (def-pred (nm! "tuple__") (mapcat second compiled)
           (vmatch 'v false {'vvec (list ['it] (tuple-chain (mapv first compiled) 'it))})))

       ;; homogeneous map: every key ⊢ k-schema, every value ⊢ v-schema
       (= :map-of type)
       (let [[kp kf] (compile-schema (first args))
             [vp vf] (compile-schema (second args))
             go (gensym "mapof_go__")
             nm (nm! "mapof__")]
         [nm (into (vec (concat kf vf))
                   [(mapof-checker-form go kp vp)
                    (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool
                          (vmatch 'v false {'vmap (list ['e] (list go 'e))}))])])

       ;; recursive schema: a local registry + a top `[:ref ::name]`. Compiled by mode
       ;; defunctionalization (handles (mutually) recursive maps/vectors/tuples/map-of — JSON/trees).
       (= :schema type)
       (let [registry (:registry props)
             top      (first args)]
         (when-not (map? registry)
           (throw (ex-info "recursion: :schema needs a :registry" {:props props})))
         (when-not (and (vector? top) (= :ref (first top)))
           (throw (ex-info "recursion: top must be [:ref ::name]" {:top top})))
         (compile-recursive registry top (nm! "rconf__")))

       :else (throw (ex-info "unsupported schema (compile-schema)" {:schema schema :type type}))))))

(defn schema->conforms-forms
  "Compile any supported malli `schema` into the ordered vector of `a/defn` forms defining
   `fn-name : Value → Bool` (the last form) plus any helpers. Each form kernel-verifies AND
   runs on `edn->value`-encoded data. A schema that compiles to a bare built-in predicate
   (e.g. `:int`) gets a thin `fn-name` alias so the public name always exists."
  [fn-name schema]
  (let [[pred forms] (compile-schema schema fn-name)]
    (if (= pred fn-name)
      forms
      (conj (vec forms)
            (list 'ansatz.core/defn fn-name ['v :- 'Value] 'Bool (list pred 'v))))))

(defn schema->conforms-form
  "Compile a FLAT scalar-field `:map` schema to the single `a/defn` form for `fn-name`
   (`λ v. (vmap? v) ∧ ⋀ (key-<T>? :k v)`). Errors if the schema needs helpers — use
   `schema->conforms-forms` for nested/vector/optional schemas."
  [fn-name schema]
  (let [forms (schema->conforms-forms fn-name schema)]
    (assert (= 1 (count forms))
            "schema->conforms-form: schema needs helpers; use schema->conforms-forms")
    (first forms)))

(defn install-conforms!
  "Define `fn-name : Value → Bool` (and any helpers) for malli `schema` on the current env.
   Returns `fn-name`. The predicate is kernel-verified by `a/defn` and runnable on Values."
  [fn-name schema]
  (binding [a/*verbose* false]
    (doseq [form (schema->conforms-forms fn-name schema)]
      (eval form)))
  fn-name)

(defn install-core!
  "Define the `Value` type and core ops/laws on the current `ansatz.core` env.
   Requires the env to already contain Lean `Init`. Returns the updated env."
  []
  (binding [a/*verbose* false]
    (doseq [form core-forms]
      (eval form)))
  (a/env))

;; ── runtime EDN ↔ Value boundary (#59) ────────────────────────────────────────
;; The runtime representation of `Value` is the general TAGGED inductive rep produced by
;; ansatz.core's codegen: `[cidx field…]`, ctor index first. These mirror that encoding so
;; the kernel-verified conformance predicates / `vget` / `vassoc` RUN on real Clojure data —
;; and can be differential-tested against malli (`m/validate`) and Clojure `get`.
;;
;;   0 vnil · 1 vbool b · 2 vint i · 3 vstr s · 4 vkw s
;;   5 vcons h t · 6 vvec items · 7 vmap entries · 8 ventry k v rest
;;
;; Maps/vectors are entry/cons chains terminated by vnil; map keys keep insertion order, and
;; first occurrence shadows (matching `vassoc` prepend semantics).

(defn edn->value
  "Encode a Clojure EDN value into the runtime `Value` tagged rep."
  [x]
  (cond
    (nil? x)        [0]
    (boolean? x)    [1 x]
    (integer? x)    [2 (long x)]
    (string? x)     [3 x]
    ;; keep the FULL keyword (namespace included): (subs (str :a/b) 1) = "a/b". `value->edn`
    ;; round-trips via (keyword "a/b") = :a/b; (name :a/b) would drop the namespace.
    (keyword? x)    [4 (subs (str x) 1)]
    (double? x)     [9 x]
    (map? x)        [7 (reduce (fn [acc [k v]] [8 (edn->value k) (edn->value v) acc])
                               [0] (reverse (seq x)))]
    (set? x)        [10 (reduce (fn [acc e] [5 (edn->value e) acc])
                                [0] (reverse (seq x)))]
    (sequential? x) [6 (reduce (fn [acc e] [5 (edn->value e) acc])
                               [0] (reverse (seq x)))]
    :else (throw (ex-info "edn->value: unsupported EDN" {:x x :class (class x)}))))

(declare value->edn)

(defn- vchain->seq [c]
  (loop [c c, acc []]
    (case (long (nth c 0))
      0 acc
      5 (recur (nth c 2) (conj acc (value->edn (nth c 1))))
      (throw (ex-info "value->edn: malformed cons chain" {:c c})))))

(defn- ventries->map [c]
  (loop [c c, acc {}]
    (case (long (nth c 0))
      0 acc
      8 (let [k (value->edn (nth c 1)), v (value->edn (nth c 2))]
          ;; head shadows: keep the first occurrence of a key
          (recur (nth c 3) (if (contains? acc k) acc (assoc acc k v))))
      (throw (ex-info "value->edn: malformed entry chain" {:c c})))))

(defn value->edn
  "Decode a runtime `Value` tagged rep back into a Clojure EDN value (inverse of edn->value
   on the canonical encoding; map keys keep first-occurrence/shadowing semantics)."
  [v]
  (case (long (nth v 0))
    0 nil
    1 (nth v 1)
    2 (nth v 1)
    3 (nth v 1)
    4 (keyword (nth v 1))
    5 (vchain->seq v)
    6 (vchain->seq (nth v 1))
    7 (ventries->map (nth v 1))
    8 (throw (ex-info "value->edn: bare ventry has no EDN form" {:v v}))
    9 (nth v 1)
    10 (set (vchain->seq (nth v 1)))))

;; ── typed bridge: dynamic Value ↔ typed record (#62) ──────────────────────────
;; Commit to a malli schema → a `def-record` typed structure (O(1) field projection at
;; runtime, vs vget's O(chain) walk) + the richer relational algebra. `conforms` (#57) is the
;; OPTIONAL boundary that upgrades a dynamic Value to the typed record (gradual: the caller
;; chooses whether to check; not forced). These are the runtime coercions across that boundary.

(defn value->record
  "Upgrade a conforming EDN `Value` (a vmap) to a typed defrecord via its `map->X` factory. After
   this, field access is an O(1) struct projection (not vget's chain walk) and the typed
   relational laws apply. The boundary conforms-check is the caller's choice — see [[malli-value-refinement]]."
  [map->factory v]
  (map->factory (value->edn v)))

(defn record->value
  "Demote a typed defrecord back to a dynamic EDN `Value` (for serialization / the dynamic path)."
  [r]
  (edn->value (into {} r)))

;; ── native-Clojure-over-Value surface (#60) ───────────────────────────────────
;; So existing Clojure code is portable onto dynamic EDN `Value`: native ops lower onto the
;; `v*` primitives when the operand is a `Value`. Keyword access `(:k v)` is handled in
;; ansatz.core; the symbol-headed ops below register elaborators (no core change).

(defn- head-name [t]
  (let [[h _] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h)) (name/->string (e/const-name h)))))

(defn- value-typed? [est ex] (= "Value" (head-name (api/arg-type est ex))))

(defn- const0 [s] (e/const' (name/from-string s) []))

(defn- vkey-expr
  "Surface key as a `Value`: a keyword literal → `(Value.vkw \"k\")`; else assume it already
   elaborates to a Value."
  [est kform]
  (if (keyword? kform)
    (e/app (const0 "Value.vkw") (e/lit-str (kw-str kform)))
    (api/elab est kform)))

(def ^:private surface-preds
  "Clojure predicate symbol → the kernel Value predicate it lowers to (when the operand is a Value)."
  {'int? "vint?" 'integer? "vint?" 'string? "vstr?" 'boolean? "vbool?" 'keyword? "vkw?"
   'nil? "vnil?" 'map? "vmap?" 'vector? "vvec?" 'set? "vset?" 'double? "vfloat?" 'float? "vfloat?"
   'some? "vsome?" 'any? "vany?"})

;; For a NON-Value operand, fall back to core's normal handling (so e.g. `(some? opt)` over an
;; Option still becomes Option.isSome, and unknown predicates error exactly as before). This is
;; what keeps these global registrations side-effect-free for non-EDN code.
(defn- vpred-elaborator [sym vpred]
  (fn [est args]
    (let [v (api/elab est (first args))]
      (if (value-typed? est v)
        (e/app (const0 vpred) v)
        (throw (ex-info (str "`" sym "` is only supported over a dynamic EDN Value in a "
                             "verified body (operand type is not Value)") {:pred sym}))))))

(defn- get-elaborator
  "`(get v k)` over a Value → `(vget (Value.vkw k) v)` (returns a Value; 2-arg form). Other
   receivers fall back to core's keyword-projection sugar (get r :k ≡ (:k r))."
  [est args]
  (let [v (api/elab est (first args))]
    (if (value-typed? est v)
      (e/app* (const0 "vget") (vkey-expr est (second args)) v)
      (api/elab est (list (second args) (first args))))))

(defn install-surface!
  "Register native-Clojure-over-Value surface elaborators (get / int?/map?/string?/… ). Idempotent;
   safe to call after `install-core!`. Keyword access `(:k v)` needs no registration (core)."
  []
  (a/register-term-elaborator! 'get get-elaborator)
  (doseq [[sym vpred] surface-preds]
    (a/register-term-elaborator! sym (vpred-elaborator sym vpred)))
  :installed)
