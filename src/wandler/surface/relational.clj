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
;; `wandler.surface.collections`. Registered via `register-elaborator!`; `install!` on load.
;;
;; group-by / join (the genuinely relational core needing a key→group model) build
;; on top of this and the collection vocab — added next.

(ns wandler.surface.relational
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [wandler.surface.collections :as coll]
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

(defn- distinct-elaborator [est args]
  ;; (distinct coll) → List.eraseDups α (BEq α) coll
  (let [coll (api/elab est (first args))
        a (coll/list-elem est coll)
        beq (or (resolve-beq (:env est) a)
                (throw (ex-info "distinct: no BEq/DecidableEq instance for element type"
                                {:elem (when a (type-name a))})))]
    (e/app* (e/const' (nm "List.eraseDups") [(coll/univ (:env est) a)]) a beq coll)))

(defn- sort-elaborator [est args]
  ;; (sort coll) → List.mergeSort α coll cmp   (cmp ascending)
  (let [coll (api/elab est (first args))
        a (coll/list-elem est coll)
        cmp (or (le-cmp (:env est) a)
                (throw (ex-info "sort: no ascending ordering for element type"
                                {:elem (when a (type-name a))})))]
    (e/app* (e/const' (nm "List.mergeSort") [(coll/univ (:env est) a)]) a coll cmp)))

(defn- sort-by-elaborator [est args]
  ;; (sort-by keyfn coll) → List.mergeSort α coll (fun a b => kcmp (keyfn a) (keyfn b))
  (let [[key-form coll-form] args
        coll (api/elab est coll-form)
        a (coll/list-elem est coll)
        keyfn (coll/compile-fn est key-form [a])
        k (api/whnf est (e/forall-body (api/arg-type est keyfn)))     ; keyfn : α → K
        kcmp (or (le-cmp (:env est) k)
                 (throw (ex-info "sort-by: no ascending ordering for key type"
                                 {:key (when k (type-name k))})))
        cmp (e/lam "a" a
                   (e/lam "b" a
                          (e/app* kcmp (e/app keyfn (e/bvar 1)) (e/app keyfn (e/bvar 0)))
                          :default)
                   :default)]
    (e/app* (e/const' (nm "List.mergeSort") [(coll/univ (:env est) a)]) a coll cmp)))

;; ---- relational core over the verified Map (wandler.kmap) --------------------

(defn- map-kv
  "Extract [K V] from a term whose type is `Map K V` (or its unfolded
   `Subtype (List (K×V)) _`)."
  [est m]
  (let [t (api/arg-type est m)
        [h as] (e/get-app-fn-args t)
        hn (when (and h (e/const? h)) (name/->string (e/const-name h)))]
    (cond
      (= hn "Map") [(nth as 0) (nth as 1)]
      (= hn "Subtype")                                   ; Subtype (List (Prod K V)) _
      (let [[_ la] (e/get-app-fn-args (first as))        ; first as = List (Prod K V)
            [_ pa] (e/get-app-fn-args (first la))]       ; first la = Prod K V
        [(nth pa 0) (nth pa 1)])
      :else (throw (ex-info "expected a Map argument" {:head hn})))))

(defn- map-vals-keys [est args which]
  ;; (vals m) / (keys m) over a Map K V → List.map (snd|fst) (Map.entries m) : List (V|K). Common over
  ;; (group-by f xs): (vals (group-by f xs)) = the groups.
  (let [m (api/elab est (first args))
        [K V] (map-kv est m)
        zz lvl/zero
        PKV (e/app* (e/const' (nm "Prod") [zz zz]) K V)
        entries (e/app* (e/const' (nm "Map.entries") []) K V m)
        out (if (= which :vals) V K)
        proj (e/lam "p" PKV (e/app* (e/const' (nm (if (= which :vals) "Prod.snd" "Prod.fst")) [zz zz]) K V (e/bvar 0)) :default)]
    (e/app* (e/const' (nm "List.map") [zz zz]) PKV out proj entries)))

(defn- vals-elaborator [est args] (map-vals-keys est args :vals))
(defn- keys-elaborator [est args] (map-vals-keys est args :keys))

(defn- group-by-elaborator [est args]
  ;; (group-by f coll) → Map.group_by K V deceq f coll : Map K (List V)
  (let [[f-form coll-form] args
        coll (api/elab est coll-form)
        V (coll/list-elem est coll)
        f (coll/compile-fn est f-form [V])
        K (api/whnf est (e/forall-body (api/arg-type est f)))      ; f : V → K
        deceq (or (resolve-deceq (:env est) K)
                  (throw (ex-info "group-by: no DecidableEq for key type" {:key (type-name K)})))]
    (e/app* (e/const' (nm "Map.group_by") []) K V deceq f coll)))

;; ── extrinsic association-list map surface: aempty / aput / aget ──────────────
;; AList K V = List(K×V); ops compose freely (plain List ops). Runtime = hash-map.
(defn- prod-kv
  "Given an alist value `m : List(K×V)`, return [K V] (the Prod arg types), or nil."
  [est m]
  (let [t (api/arg-type est m)               ; List (Prod K V)
        [_ la] (when t (e/get-app-fn-args t))      ; → [Prod K V]
        [_ pa] (when (seq la) (e/get-app-fn-args (first la)))]
    (when (= 2 (count pa)) pa)))

(defn- aempty-elaborator [est args]
  ;; (aempty K V) → AList.empty K V
  (let [K (api/elab est (first args))
        V (api/elab est (second args))]
    (e/app* (e/const' (nm "AList.empty") []) K V)))

(defn- aput-elaborator [est args]
  ;; (aput m k v) → AList.put K V deceq k v m
  (let [[m-form k-form v-form] args
        m (api/elab est m-form)
        [K V] (or (prod-kv est m) (throw (ex-info "aput: cannot infer key/value type from map" {})))
        k (api/elab est k-form)
        v (api/elab est v-form)
        deceq (or (resolve-deceq (:env est) K) (throw (ex-info "aput: no DecidableEq for key type" {})))]
    (e/app* (e/const' (nm "AList.put") []) K V deceq k v m)))

(defn- aget-elaborator [est args]
  ;; (aget m k default) → AList.get K V deceq k default m
  (let [[m-form k-form d-form] args
        m (api/elab est m-form)
        [K V] (or (prod-kv est m) (throw (ex-info "aget: cannot infer key/value type from map" {})))
        k (api/elab est k-form)
        d (api/elab est d-form)
        deceq (or (resolve-deceq (:env est) K) (throw (ex-info "aget: no DecidableEq for key type" {})))]
    (e/app* (e/const' (nm "AList.get") []) K V deceq k d m)))

(defn- frequencies-elaborator [est args]
  ;; (frequencies coll) : AList α Nat (= List(α×Nat)) — count each distinct element, as a
  ;; foldl over the EXTRINSIC map (no proof tax):
  ;;   foldl (fun m x => AList.put x (succ (AList.get x 0 m)) m) (AList.empty α Nat) coll
  ;; codegen falls out as (reduce (fn [m x] (assoc m x (inc (get m x 0)))) {} coll).
  (let [coll (api/elab est (first args))
        a (coll/list-elem est coll)                              ; α (must be Type 0)
        z lvl/zero
        nat (e/const' (nm "Nat") [])
        deceq (or (resolve-deceq (:env est) a)
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

(defn- dedupe-elaborator [est args]
  ;; (dedupe coll) → List.eraseReps α beq coll — drops CONSECUTIVE duplicates (Clojure's
  ;; dedupe semantics; `distinct` is the global one). Lives here for the BEq synthesis.
  (let [coll (api/elab est (first args))
        a (coll/list-elem est coll)
        beq (or (resolve-beq (:env est) a)
                (throw (ex-info "dedupe: no BEq/DecidableEq for element type" {:elem (type-name a)})))]
    (e/app* (e/const' (nm "List.eraseReps") [(coll/univ (:env est) a)]) a beq coll)))

(defn- ->map-elaborator [est args]
  ;; (->map m) → Map.entries K V m : List (K×V); runtime materializes to a Clojure map.
  (let [m (api/elab est (first args))
        [K V] (map-kv est m)]
    (e/app* (e/const' (nm "Map.entries") []) K V m)))

(defn- join-elaborator [est args]
  ;; (join kf lf xs ys) → Map.join K X Y deceq kf lf xs ys : List (X×Y)
  ;; inner join: every (x,y) with (kf x) = (lf y).
  (let [[kf-form lf-form xs-form ys-form] args
        xs (api/elab est xs-form)
        ys (api/elab est ys-form)
        X (coll/list-elem est xs)
        Y (coll/list-elem est ys)
        kf (coll/compile-fn est kf-form [X])
        lf (coll/compile-fn est lf-form [Y])
        K (api/whnf est (e/forall-body (api/arg-type est kf)))     ; kf : X → K
        deceq (or (resolve-deceq (:env est) K)
                  (throw (ex-info "join: no DecidableEq for key type" {:key (type-name K)})))]
    (e/app* (e/const' (nm "Map.join") []) K X Y deceq kf lf xs ys)))

(defn- build-elem
  "List.elem K (BEq from DecidableEq) x ys : Bool — x ∈ ys. The canonical membership form the
   SEMIJOIN rewrite (List.elem_filter_eq_index_probe) recognizes. Many surface spellings of
   membership NORMALIZE to this so they all light up the index-probe optimization."
  [est x ys]
  (let [K (coll/list-elem est ys)
        dec (or (resolve-deceq (:env est) K)
                (throw (ex-info "membership: no DecidableEq for element type" {:elem (type-name K)})))
        beq (e/app* (e/const' (nm "instBEqOfDecidableEq") [lvl/zero]) K dec)]
    (e/app* (e/const' (nm "List.elem") [lvl/zero]) K beq x ys)))

(defn- member-elaborator [est args]
  ;; (member x ys) → x ∈ ys. Under a `filterv` the cost optimizer rewrites the O(|ys|) scan to a
  ;; build-once index probe (the verified SEMIJOIN).
  (let [[x-form ys-form] args]
    (build-elem est (api/elab est x-form)
                (api/elab est ys-form))))

(defn- unwrap-set-form
  "`(set coll)` → `coll` — the set construction is identity for List membership, so a `(contains?
   (set ys) x)` / `(some (set ys) x)` spelling still normalizes to a List.elem over `ys`."
  [form]
  (if (and (seq? form) (= 'set (first form)) (= 2 (count form))) (second form) form))

(defn- contains-elaborator [est args]
  ;; (contains? coll x) → x ∈ coll (List membership), normalized to List.elem → same SEMIJOIN.
  ;; (Clojure arg order: collection first.) Unwraps (contains? (set ys) x) too.
  (let [[coll-form x-form] args]
    (build-elem est (api/elab est x-form)
                (api/elab est (unwrap-set-form coll-form)))))

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

(defn- some-elaborator [est args]
  ;; (some pred coll) as a boolean existence test → List.any pred coll. If `pred` is a membership
  ;; equality `#(= % x)`, NORMALIZE to List.elem x coll so the SEMIJOIN fires (different spelling,
  ;; same optimization).
  (let [[pred-form coll-form] args
        coll (api/elab est coll-form)
        K    (coll/list-elem est coll)]
    (cond
      ;; (some #{x} ys) — a single-element set literal IS a membership test → List.elem x ys
      (and (set? pred-form) (= 1 (count pred-form)))
      (build-elem est (api/elab est (first pred-form)) coll)
      :else
      (let [pred (coll/compile-fn est pred-form [K])]  ; binds the predicate's param
        (if-let [x (membership-eq-target pred)]                          ; (some #(== % x) ys) → List.elem
          (build-elem est x coll)
          (e/app* (e/const' (nm "List.any") [lvl/zero]) K coll pred))))))

(defn- every-elaborator [est args]
  ;; (every? pred coll) → List.all pred coll : Bool
  (let [[pred-form coll-form] args
        coll (api/elab est coll-form)
        K    (coll/list-elem est coll)
        pred (coll/compile-fn est pred-form [K])]
    (e/app* (e/const' (nm "List.all") [lvl/zero]) K coll pred)))

(defn install!
  "Register the relational/ordering elaborators (idempotent). The group-by/->map
   elaborators emit wandler.kmap constants, so `kmap/install!` must have run first."
  []
  (a/register-term-elaborator! 'member member-elaborator)
  (a/register-term-elaborator! 'contains? contains-elaborator)   ; membership — normalizes to List.elem
  (a/register-term-elaborator! 'some some-elaborator)            ; ∃ / membership-equality → List.elem
  (a/register-term-elaborator! 'every? every-elaborator)         ; ∀
  (a/register-term-elaborator! 'distinct distinct-elaborator)
  (a/register-term-elaborator! 'sort sort-elaborator)
  (a/register-term-elaborator! 'sort-by sort-by-elaborator)
  (a/register-term-elaborator! 'group-by group-by-elaborator)
  (a/register-term-elaborator! 'vals vals-elaborator)
  (a/register-term-elaborator! 'keys keys-elaborator)
  (a/register-term-elaborator! 'dedupe dedupe-elaborator)
  (a/register-term-elaborator! 'aempty aempty-elaborator)
  (a/register-term-elaborator! 'aput aput-elaborator)
  (a/register-term-elaborator! 'aget aget-elaborator)
  (a/register-term-elaborator! 'frequencies frequencies-elaborator)
  (a/register-term-elaborator! '->map ->map-elaborator)
  (a/register-term-elaborator! 'join join-elaborator))

(install!)
