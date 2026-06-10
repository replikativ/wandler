;; Relational / ordering vocabulary in verified bodies.
;;
;; `distinct`, `sort`, `sort-by` over `List`, compiling to the kernel `List.*`
;; ops with the required typeclass instances (BEq / ordering) synthesized from
;; the inferred element type:
;;
;;   (a/defn uniq   [xs :- (List Nat)] (List Nat) (distinct xs))
;;   (a/defn ranked [xs :- (List Nat)] (List Nat) (sort xs))
;;   (a/defn by-key [xs :- (List Nat)] (List Nat) (sort-by #(Nat.sub 100 %) xs))
;;
;; Shares the element-type / universe / inline-fn machinery with
;; `ansatz.collections`. Registered via `register-elaborator!`; `install!` on load.
;;
;; group-by / join (the genuinely relational core needing a key→group model) build
;; on top of this and the collection vocab — added next.

(ns ansatz.relational
  (:require [ansatz.core :as a]
            [ansatz.collections :as coll]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

(defn- nm [s] (name/from-string s))

(defn- type-name
  "Head constant name of a type expr (e.g. \"Nat\" for `Nat`, \"List\" for `List α`)."
  [t]
  (let [[h _] (e/get-app-fn-args t)]
    (when (and h (e/const? h)) (name/->string (e/const-name h)))))

;; ---- instance synthesis ----------------------------------------------------

(defn- resolve-deceq
  "A `DecidableEq α` instance term for element type `elem`, or nil. Prefers the
   named instance `instDecidableEq<T>`, falling back to `<T>.decEq`."
  [^ansatz.kernel.Env env elem]
  (let [tn (type-name elem)]
    (some (fn [n] (when (env/lookup env (nm n)) (e/const' (nm n) [])))
          [(str "instDecidableEq" tn) (str tn ".decEq")])))

(defn- resolve-beq
  "A `BEq α` instance term for `elem`: `instBEqOfDecidableEq α (DecidableEq α)`."
  [^ansatz.kernel.Env env elem]
  (when-let [deceq (resolve-deceq env elem)]
    (e/app* (e/const' (nm "instBEqOfDecidableEq") [(coll/univ env elem)]) elem deceq)))

(defn- le-cmp
  "An ascending Bool comparator `α → α → Bool` for `elem` (`Nat.ble` for Nat, or
   `<T>.ble` when the type provides one), or nil."
  [^ansatz.kernel.Env env elem]
  (let [tn (type-name elem)
        cand (str tn ".ble")]
    (cond
      (= tn "Nat") (e/const' (nm "Nat.ble") [])
      (env/lookup env (nm cand)) (e/const' (nm cand) [])
      :else nil)))

;; ---- elaborators -----------------------------------------------------------

(defn- distinct-elaborator [env scope depth args lctx]
  ;; (distinct coll) → List.eraseDups α (BEq α) coll
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (coll/list-elem env coll)
        beq (or (resolve-beq env a)
                (throw (ex-info "distinct: no BEq/DecidableEq instance for element type"
                                {:elem (when a (type-name a))})))]
    (e/app* (e/const' (nm "List.eraseDups") [(coll/univ env a)]) a beq coll)))

(defn- sort-elaborator [env scope depth args lctx]
  ;; (sort coll) → List.mergeSort α coll cmp   (cmp ascending)
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (coll/list-elem env coll)
        cmp (or (le-cmp env a)
                (throw (ex-info "sort: no ascending ordering for element type"
                                {:elem (when a (type-name a))})))]
    (e/app* (e/const' (nm "List.mergeSort") [(coll/univ env a)]) a coll cmp)))

(defn- sort-by-elaborator [env scope depth args lctx]
  ;; (sort-by keyfn coll) → List.mergeSort α coll (fun a b => kcmp (keyfn a) (keyfn b))
  (let [[key-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        a (coll/list-elem env coll)
        keyfn (coll/compile-fn env scope depth key-form [a] lctx)
        k (a/whnf-ty env (e/forall-body (a/get-arg-type env nil keyfn)))     ; keyfn : α → K
        kcmp (or (le-cmp env k)
                 (throw (ex-info "sort-by: no ascending ordering for key type"
                                 {:key (when k (type-name k))})))
        cmp (e/lam "a" a
                   (e/lam "b" a
                          (e/app* kcmp (e/app keyfn (e/bvar 1)) (e/app keyfn (e/bvar 0)))
                          :default)
                   :default)]
    (e/app* (e/const' (nm "List.mergeSort") [(coll/univ env a)]) a coll cmp)))

;; ---- relational core over the verified Map (ansatz.kmap) --------------------

(defn- map-kv
  "Extract [K V] from a term whose type is `Map K V` (or its unfolded
   `Subtype (List (K×V)) _`)."
  [env m]
  (let [t (a/get-arg-type env nil m)
        [h as] (e/get-app-fn-args t)
        hn (when (and h (e/const? h)) (name/->string (e/const-name h)))]
    (cond
      (= hn "Map") [(nth as 0) (nth as 1)]
      (= hn "Subtype")                                   ; Subtype (List (Prod K V)) _
      (let [[_ la] (e/get-app-fn-args (first as))        ; first as = List (Prod K V)
            [_ pa] (e/get-app-fn-args (first la))]       ; first la = Prod K V
        [(nth pa 0) (nth pa 1)])
      :else (throw (ex-info "expected a Map argument" {:head hn})))))

(defn- map-vals-keys [env scope depth args lctx which]
  ;; (vals m) / (keys m) over a Map K V → List.map (snd|fst) (Map.entries m) : List (V|K). Common over
  ;; (group-by f xs): (vals (group-by f xs)) = the groups.
  (let [m (a/sexp->ansatz env scope depth (first args) lctx)
        [K V] (map-kv env m)
        zz lvl/zero
        PKV (e/app* (e/const' (nm "Prod") [zz zz]) K V)
        entries (e/app* (e/const' (nm "Map.entries") []) K V m)
        out (if (= which :vals) V K)
        proj (e/lam "p" PKV (e/app* (e/const' (nm (if (= which :vals) "Prod.snd" "Prod.fst")) [zz zz]) K V (e/bvar 0)) :default)]
    (e/app* (e/const' (nm "List.map") [zz zz]) PKV out proj entries)))

(defn- vals-elaborator [env scope depth args lctx] (map-vals-keys env scope depth args lctx :vals))
(defn- keys-elaborator [env scope depth args lctx] (map-vals-keys env scope depth args lctx :keys))

(defn- group-by-elaborator [env scope depth args lctx]
  ;; (group-by f coll) → Map.group_by K V deceq f coll : Map K (List V)
  (let [[f-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        V (coll/list-elem env coll)
        f (coll/compile-fn env scope depth f-form [V] lctx)
        K (a/whnf-ty env (e/forall-body (a/get-arg-type env nil f)))      ; f : V → K
        deceq (or (resolve-deceq env K)
                  (throw (ex-info "group-by: no DecidableEq for key type" {:key (type-name K)})))]
    (e/app* (e/const' (nm "Map.group_by") []) K V deceq f coll)))

;; ── extrinsic association-list map surface: aempty / aput / aget ──────────────
;; AList K V = List(K×V); ops compose freely (plain List ops). Runtime = hash-map.
(defn- prod-kv
  "Given an alist value `m : List(K×V)`, return [K V] (the Prod arg types), or nil."
  [env m]
  (let [t (a/get-arg-type env nil m)               ; List (Prod K V)
        [_ la] (when t (e/get-app-fn-args t))      ; → [Prod K V]
        [_ pa] (when (seq la) (e/get-app-fn-args (first la)))]
    (when (= 2 (count pa)) pa)))

(defn- aempty-elaborator [env scope depth args lctx]
  ;; (aempty K V) → AList.empty K V
  (let [K (a/sexp->ansatz env scope depth (first args) lctx)
        V (a/sexp->ansatz env scope depth (second args) lctx)]
    (e/app* (e/const' (nm "AList.empty") []) K V)))

(defn- aput-elaborator [env scope depth args lctx]
  ;; (aput m k v) → AList.put K V deceq k v m
  (let [[m-form k-form v-form] args
        m (a/sexp->ansatz env scope depth m-form lctx)
        [K V] (or (prod-kv env m) (throw (ex-info "aput: cannot infer key/value type from map" {})))
        k (a/sexp->ansatz env scope depth k-form lctx)
        v (a/sexp->ansatz env scope depth v-form lctx)
        deceq (or (resolve-deceq env K) (throw (ex-info "aput: no DecidableEq for key type" {})))]
    (e/app* (e/const' (nm "AList.put") []) K V deceq k v m)))

(defn- aget-elaborator [env scope depth args lctx]
  ;; (aget m k default) → AList.get K V deceq k default m
  (let [[m-form k-form d-form] args
        m (a/sexp->ansatz env scope depth m-form lctx)
        [K V] (or (prod-kv env m) (throw (ex-info "aget: cannot infer key/value type from map" {})))
        k (a/sexp->ansatz env scope depth k-form lctx)
        d (a/sexp->ansatz env scope depth d-form lctx)
        deceq (or (resolve-deceq env K) (throw (ex-info "aget: no DecidableEq for key type" {})))]
    (e/app* (e/const' (nm "AList.get") []) K V deceq k d m)))

(defn- frequencies-elaborator [env scope depth args lctx]
  ;; (frequencies coll) : AList α Nat (= List(α×Nat)) — count each distinct element, as a
  ;; foldl over the EXTRINSIC map (no proof tax):
  ;;   foldl (fun m x => AList.put x (succ (AList.get x 0 m)) m) (AList.empty α Nat) coll
  ;; codegen falls out as (reduce (fn [m x] (assoc m x (inc (get m x 0)))) {} coll).
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (coll/list-elem env coll)                              ; α (must be Type 0)
        z lvl/zero
        nat (e/const' (nm "Nat") [])
        deceq (or (resolve-deceq env a)
                  (throw (ex-info "frequencies: no DecidableEq for element type" {:elem (type-name a)})))
        prodAN (e/app* (e/const' (nm "Prod") [z z]) a nat)       ; α × Nat
        listAN (e/app (e/const' (nm "List") [z]) prodAN)         ; List(α×Nat)
        empty- (e/app* (e/const' (nm "AList.empty") []) a nat)
        ;; step = λ (m : List(α×Nat)) (x : α). put x (succ (get x 0 m)) m   (m=bvar1, x=bvar0)
        mb (e/bvar 1) xb (e/bvar 0)
        getv (e/app* (e/const' (nm "AList.get") []) a nat deceq xb (e/lit-nat 0) mb)
        succv (e/app (e/const' (nm "Nat.succ") []) getv)
        putv (e/app* (e/const' (nm "AList.put") []) a nat deceq xb succv mb)
        step (e/lam "m" listAN (e/lam "x" a putv :default) :default)]
    (e/app* (e/const' (nm "List.foldl") [z z]) listAN a step empty- coll)))

(defn- dedupe-elaborator [env scope depth args lctx]
  ;; (dedupe coll) → List.eraseReps α beq coll — drops CONSECUTIVE duplicates (Clojure's
  ;; dedupe semantics; `distinct` is the global one). Lives here for the BEq synthesis.
  (let [coll (a/sexp->ansatz env scope depth (first args) lctx)
        a (coll/list-elem env coll)
        beq (or (resolve-beq env a)
                (throw (ex-info "dedupe: no BEq/DecidableEq for element type" {:elem (type-name a)})))]
    (e/app* (e/const' (nm "List.eraseReps") [(coll/univ env a)]) a beq coll)))

(defn- ->map-elaborator [env scope depth args lctx]
  ;; (->map m) → Map.entries K V m : List (K×V); runtime materializes to a Clojure map.
  (let [m (a/sexp->ansatz env scope depth (first args) lctx)
        [K V] (map-kv env m)]
    (e/app* (e/const' (nm "Map.entries") []) K V m)))

(defn- join-elaborator [env scope depth args lctx]
  ;; (join kf lf xs ys) → Map.join K X Y deceq kf lf xs ys : List (X×Y)
  ;; inner join: every (x,y) with (kf x) = (lf y).
  (let [[kf-form lf-form xs-form ys-form] args
        xs (a/sexp->ansatz env scope depth xs-form lctx)
        ys (a/sexp->ansatz env scope depth ys-form lctx)
        X (coll/list-elem env xs)
        Y (coll/list-elem env ys)
        kf (coll/compile-fn env scope depth kf-form [X] lctx)
        lf (coll/compile-fn env scope depth lf-form [Y] lctx)
        K (a/whnf-ty env (e/forall-body (a/get-arg-type env nil kf)))     ; kf : X → K
        deceq (or (resolve-deceq env K)
                  (throw (ex-info "join: no DecidableEq for key type" {:key (type-name K)})))]
    (e/app* (e/const' (nm "Map.join") []) K X Y deceq kf lf xs ys)))

(defn- build-elem
  "List.elem K (BEq from DecidableEq) x ys : Bool — x ∈ ys. The canonical membership form the
   SEMIJOIN rewrite (List.elem_filter_eq_index_probe) recognizes. Many surface spellings of
   membership NORMALIZE to this so they all light up the index-probe optimization."
  [env x ys]
  (let [K (coll/list-elem env ys)
        dec (or (resolve-deceq env K)
                (throw (ex-info "membership: no DecidableEq for element type" {:elem (type-name K)})))
        beq (e/app* (e/const' (nm "instBEqOfDecidableEq") [lvl/zero]) K dec)]
    (e/app* (e/const' (nm "List.elem") [lvl/zero]) K beq x ys)))

(defn- member-elaborator [env scope depth args lctx]
  ;; (member x ys) → x ∈ ys. Under a `filterv` the cost optimizer rewrites the O(|ys|) scan to a
  ;; build-once index probe (the verified SEMIJOIN).
  (let [[x-form ys-form] args]
    (build-elem env (a/sexp->ansatz env scope depth x-form lctx)
                (a/sexp->ansatz env scope depth ys-form lctx))))

(defn- unwrap-set-form
  "`(set coll)` → `coll` — the set construction is identity for List membership, so a `(contains?
   (set ys) x)` / `(some (set ys) x)` spelling still normalizes to a List.elem over `ys`."
  [form]
  (if (and (seq? form) (= 'set (first form)) (= 2 (count form))) (second form) form))

(defn- contains-elaborator [env scope depth args lctx]
  ;; (contains? coll x) → x ∈ coll (List membership), normalized to List.elem → same SEMIJOIN.
  ;; (Clojure arg order: collection first.) Unwraps (contains? (set ys) x) too.
  (let [[coll-form x-form] args]
    (build-elem env (a/sexp->ansatz env scope depth x-form lctx)
                (a/sexp->ansatz env scope depth (unwrap-set-form coll-form) lctx))))

(defn- contains-bvar0?
  "Does `e` reference the innermost bound var (bvar 0)? Approximate — assumes no nested binders in
   `e` (true for the simple membership predicates this normalizes). Used by `some`'s normalization."
  [e]
  (cond (e/bvar? e) (= 0 (e/bvar-idx e))
        (e/app? e)  (or (contains-bvar0? (e/app-fn e)) (contains-bvar0? (e/app-arg e)))
        :else false))

(defn- membership-eq-target
  "If a predicate lambda is a membership equality `λe. e == c` (or `c == e`) — body `Nat.beq`/`BEq.beq`
   with one side the bound var and the other free of it — return that other side `c`, lifted out from
   under the binder (loose bvars lowered via instantiate1). The hook that NORMALIZES `(some #(= % x) ys)`
   → `List.elem x ys`, so it fires the SEMIJOIN like `member`/`contains?`."
  [pred]
  (when (e/lam? pred)
    (let [body (e/lam-body pred)
          [h args] (e/get-app-fn-args body)
          hn (when (e/const? h) (name/->string (e/const-name h)))
          [a b] (case hn
                  "Nat.beq" [(nth args 0 nil) (nth args 1 nil)]
                  "BEq.beq" [(nth args 2 nil) (nth args 3 nil)]
                  [nil nil])
          bv0? (fn [t] (and t (e/bvar? t) (= 0 (e/bvar-idx t))))
          free? (fn [t] (and t (not (contains-bvar0? t))))
          lift (fn [t] (e/instantiate1 t (e/sort' lvl/zero)))]   ; t has no bvar0 ⇒ this just lowers it
      (cond (and (bv0? a) (free? b)) (lift b)
            (and (bv0? b) (free? a)) (lift a)
            :else nil))))

(defn- some-elaborator [env scope depth args lctx]
  ;; (some pred coll) as a boolean existence test → List.any pred coll. If `pred` is a membership
  ;; equality `#(= % x)`, NORMALIZE to List.elem x coll so the SEMIJOIN fires (different spelling,
  ;; same optimization).
  (let [[pred-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        K    (coll/list-elem env coll)]
    (cond
      ;; (some #{x} ys) — a single-element set literal IS a membership test → List.elem x ys
      (and (set? pred-form) (= 1 (count pred-form)))
      (build-elem env (a/sexp->ansatz env scope depth (first pred-form) lctx) coll)
      :else
      (let [pred (coll/compile-fn env scope depth pred-form [K] lctx)]  ; binds the predicate's param
        (if-let [x (membership-eq-target pred)]                          ; (some #(== % x) ys) → List.elem
          (build-elem env x coll)
          (e/app* (e/const' (nm "List.any") [lvl/zero]) K coll pred))))))

(defn- every-elaborator [env scope depth args lctx]
  ;; (every? pred coll) → List.all pred coll : Bool
  (let [[pred-form coll-form] args
        coll (a/sexp->ansatz env scope depth coll-form lctx)
        K    (coll/list-elem env coll)
        pred (coll/compile-fn env scope depth pred-form [K] lctx)]
    (e/app* (e/const' (nm "List.all") [lvl/zero]) K coll pred)))

(defn install!
  "Register the relational/ordering elaborators (idempotent). The group-by/->map
   elaborators emit ansatz.kmap constants, so `kmap/install!` must have run first."
  []
  (a/register-elaborator! 'member member-elaborator)
  (a/register-elaborator! 'contains? contains-elaborator)   ; membership — normalizes to List.elem
  (a/register-elaborator! 'some some-elaborator)            ; ∃ / membership-equality → List.elem
  (a/register-elaborator! 'every? every-elaborator)         ; ∀
  (a/register-elaborator! 'distinct distinct-elaborator)
  (a/register-elaborator! 'sort sort-elaborator)
  (a/register-elaborator! 'sort-by sort-by-elaborator)
  (a/register-elaborator! 'group-by group-by-elaborator)
  (a/register-elaborator! 'vals vals-elaborator)
  (a/register-elaborator! 'keys keys-elaborator)
  (a/register-elaborator! 'dedupe dedupe-elaborator)
  (a/register-elaborator! 'aempty aempty-elaborator)
  (a/register-elaborator! 'aput aput-elaborator)
  (a/register-elaborator! 'aget aget-elaborator)
  (a/register-elaborator! 'frequencies frequencies-elaborator)
  (a/register-elaborator! '->map ->map-elaborator)
  (a/register-elaborator! 'join join-elaborator))

(install!)
