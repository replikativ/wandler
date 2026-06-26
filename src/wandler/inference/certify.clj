(ns wandler.inference.certify
  "A→B bridge: a semiring factor-graph variable-elimination step compiled to a kernel term that the
   optimizer (`wandler.optimize.faq`) certifies PER RUN (`factored ≡ naive`) — turning
   `wandler.inference.semiring/faq`'s `:algebra`-trust plan into an `:execution` certificate.

   `certified-eliminate` consumes and produces the SAME `{:vars :rel}` factors as
   `wandler.inference.semiring`, so it is a drop-in for `(factor-marginalize sr v (factor-join sr f1 f2))`
   that additionally carries a kernel proof. The certificate IS the variable-elimination certificate:
   `Map.foldl_join_factor` says the per-key bucket fold equals the fold over the materialized join, so
   `Σ over (f1 ⋈ f2)` never builds the product.

   A factor is described by a LAYOUT — `{:row-type :vars :proj :weight :fvar}` — where `:proj` maps each
   variable to a function navigating a row to that variable's value and `:weight` navigates to the weight.
   A base factor's rows are flat (`Prod N (… S)`); an elimination's OUTPUT factor is keyed by a composite
   `Prod KK S` and its layout navigates THAT — so an intermediate factor threads into the next step
   exactly like a base factor (the `chain-certificate` composition is layout-agnostic). All projections
   derive from variable order — no per-factor special-casing.

   Today: the counting carrier (`Nat`) and a single shared elimination variable per step. Other carriers
   and multi-way joins are mechanical extensions — `Map.foldl_join_factor` constrains neither the fold op
   nor the carrier."
  (:require [ansatz.core :as a]
            [wandler.optimize :as opt]
            [wandler.optimize.certify :as cert]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [wandler.inference.semiring :as sr]
            [clojure.set :as set]))

(def ^:private z lvl/zero)
(def ^:private one (lvl/succ lvl/zero))
(defn- c' [s & ls] (e/const' (name/from-string s) (vec ls)))
(def ^:private N (c' "Nat"))
(def ^:private decN (c' "instDecidableEqNat"))

;; ── carriers ──────────────────────────────────────────────────────────────────────────────────────────
;; A carrier bundles the kernel semiring `{:S :add :mul :zero}` (op- and carrier-agnostic — `Map.foldl_join_factor`
;; is monomorphic at `Sort 1`, so it instantiates at any Type-0 carrier) PLUS the WEIGHT codec
;; `{:enc :dec}` mapping a `wandler.inference.semiring` runtime weight ↔ its codegen row representation.
;; Only the WEIGHT is carrier-typed; variable values are always Nat indices regardless of carrier.

;; ENat (tropical ℕ∞) runtime rep (Option-shaped, since `inf` is the only nullary ctor): `inf` → `nil`,
;; `fin n` → `[n]` — matched by wandler.laws.tropical's registered ENat.min/ENat.plus lowerings. The
;; `semiring/tropical` weight is a finite cost (a number) or `##Inf`.
(defn- enc-enat [w] (if (or (= w ##Inf) (nil? w)) nil [(long w)]))
(defn- dec-enat [v] (if (nil? v) ##Inf (long (first v))))

;; the counting carrier (the default semiring): Nat weights, runtime longs.
;; `:zero-val` = the additive identity as a decoded weight — dropped from the result rel so the certified
;; output matches `wandler.inference.semiring`, which prunes `:zero` entries (the kernel join keeps every
;; matching pair regardless of weight, e.g. Bool `true ∧ false = false`).
(def counting   {:S N           :add (c' "Nat.add")  :mul (c' "Nat.mul")  :zero (c' "Nat.zero")
                 :enc long :dec long :zero-val 0})
;; existence/reachability: Bool weights (∨/∧), runtime Clojure booleans.
(def existence  {:S (c' "Bool") :add (c' "Bool.or")  :mul (c' "Bool.and") :zero (c' "Bool.false")
                 :enc boolean :dec boolean :zero-val false})
;; tropical / shortest-path: ℕ∞ = ENat weights (min/+), runtime tagged rep.
(def tropical   {:S (c' "ENat") :add (c' "ENat.min") :mul (c' "ENat.plus") :zero (c' "ENat.inf")
                 :enc enc-enat :dec dec-enat :zero-val ##Inf})
;; probability (unnormalized marginals): Float weights (+/×), runtime doubles. The factorization law
;; `Map.foldl_join_factor` is ORDER-PRESERVING (the join is a `flatMap`; the factored fold visits the same
;; elements in the same order), so it certifies at S=Float WITHOUT needing Float to be a lawful semiring —
;; `factored ≡ naive` holds because the two folds are bit-identical, not by any reorder. The `:zero` must
;; codegen to `0.0`; `OfNat.ofNat Float 0` lowers to an unresolved instance, so use the `OfScientific`
;; literal `0×10⁰` (codegen erases the type/inst and emits the double). Normalizing a marginal to a
;; probability is the trusted L2 numeric step (a division), as for counts.
(def ^:private float-zero
  (e/app* (c' "OfScientific.ofScientific" z) (c' "Float") (c' "instOfScientificFloat")
          (e/lit-nat 0) (c' "Bool.false") (e/lit-nat 0)))
(def probability {:S (c' "Float") :add (c' "Float.add") :mul (c' "Float.mul") :zero float-zero
                  :enc double :dec double :zero-val 0.0})

;; ── right-nested Prod layout: a row over component types [T0 T1 … Tn] is  Prod T0 (Prod T1 (… Tn)) ────
(defn- nest [ts]
  (reduce (fn [acc t] (e/app* (c' "Prod" z z) t acc)) (last ts) (reverse (butlast ts))))

(defn- prj
  "Project component `idx` out of a right-nested-Prod `row` whose component types are `ts`."
  [ts idx row]
  (loop [i 0 cur row tail ts]
    (let [hd (first tail) rest (nest (vec (next tail)))]
      (if (= i idx)
        (if (next tail) (e/app* (c' "Prod.fst" z z) hd rest cur) cur)
        (recur (inc i) (e/app* (c' "Prod.snd" z z) hd rest cur) (vec (next tail)))))))

(defn- dec-eq
  "`DecidableEq` for a key type that is a right-nested Prod of `Nat`s (component types `ts`)."
  [ts]
  (if (= 1 (count ts))
    decN
    (e/app* (c' "instDecidableEqProd" z z) (first ts) (nest (vec (next ts))) decN (dec-eq (vec (next ts))))))

(defn- nat-key
  "Right-nested `Prod.mk` over the value exprs `vals` (each `: N`), of type `nest (repeat (count vals) N)`."
  [vals]
  (let [parts (vec vals)]
    (loop [i (- (count parts) 2) acc (peek parts)]
      (if (< i 0) acc
          (recur (dec i) (e/app* (c' "Prod.mk" z z) N (nest (vec (repeat (- (count parts) (inc i)) N)))
                                 (nth parts i) acc))))))

;; ── left-nested join tuples: a k-way `Map.join` chain produces `Prod (… (Prod R0 R1) …) R_{k-1}` ──────
(defn- nest-left
  "Left-nested Prod over component types `[T0 T1 … Tn]` → `Prod (… (Prod T0 T1) …) Tn`."
  [ts] (reduce (fn [acc t] (e/app* (c' "Prod" z z) acc t)) (first ts) (next ts)))

(defn- row-of
  "Navigate a left-nested join tuple `pj` (whose `k` leaves have types `Rts`) down to original row `i`:
   `R0 = fst^{k-1}`, `R_i = snd (fst^{k-1-i})`."
  [Rts i pj]
  (let [k (count Rts)
        tup (fn [m] (nest-left (subvec Rts 0 m)))          ; T_m = left-nest of the first m rows
        node (loop [m k cur pj]                            ; peel `fst` from T_k down to T_{i+1}
               (if (= m (inc i)) cur
                   (recur (dec m) (e/app* (c' "Prod.fst" z z) (tup (dec m)) (nth Rts (dec m)) cur))))]
    (if (zero? i) node (e/app* (c' "Prod.snd" z z) (tup i) (nth Rts i) node))))

;; ── factor LAYOUTs ──────────────────────────────────────────────────────────────────────────────────
(def ^:private F1-ID 9001)
(def ^:private F2-ID 9002)

(defn base-layout
  "Layout for a base factor over `vars` (Nat-valued), carrier weight `S`, bound to source fvar `fid`. Rows
   are the flat right-nested Prod `Prod N (… S)`."
  [{:keys [S]} vars fid]
  (let [ts (vec (concat (repeat (count vars) N) [S]))]
    {:row-type (nest ts) :vars (vec vars) :fvar fid
     :proj   (into {} (map-indexed (fn [i v] [v (fn [row] (prj ts i row))]) vars))
     :weight (fn [row] (prj ts (count vars) row))}))

(defn eliminate*
  "Eliminate the variable `v` from a VECTOR of `layouts` (k ≥ 2), keeping every other variable. Builds a
   left-nested k-way `Map.join` chain — each join keys on ALL variables shared between the accumulated
   tuple and the next factor (a NATURAL join, so a loop's repeated variable is equated, not cross-producted)
   — and folds it INTO A Map keyed by the kept (deduplicated) vars (`⊕`-summing `⊗`-products), plus the
   OUTPUT layout (rows `Prod KK S`, bound to `out-fid`). `Map.join`/`Map.foldl_join_factor` are key-agnostic,
   so a composite Nat join key factors join-by-join via `try-fold-factor*`. For factors sharing only `v`
   (chains/trees/stars) this is the single-key join as before; for k = 2 the term is unchanged. Returns
   `{:term :lctx :map-type :kk-type :kept-vars :row-types :row1-type :row2-type :fids :out-layout}`."
  [{:keys [S add mul zero]} layouts v out-fid]
  (let [k (count layouts)
        Rts (mapv :row-type layouts)
        l0 (first layouts)
        ordered-vars (vec (distinct (mapcat :vars layouts)))   ; stable kept ordering across the union
        ;; left-nested NATURAL-join chain; `accessors` maps each known var → a fn navigating the current
        ;; tuple to its value (one representative; the join equates duplicates).
        [join _accT accessors]
        (loop [i 1, lst (e/fvar (:fvar l0)), accT (first Rts), acc-vars (vec (:vars l0))
               accessors (into {} (map (fn [var] [var (fn [t] ((get-in l0 [:proj var]) t))]) (:vars l0)))]
          (if (>= i k) [lst accT accessors]
              (let [li (nth layouts i) Ri (nth Rts i) fvars (:vars li)
                    shared (filterv (set acc-vars) fvars)        ; vars f_i shares with the acc (f_i order)
                    Kts (vec (repeat (count shared) N)) Ki (nest Kts) deci (dec-eq Kts)
                    kf-acc (e/lam "p" accT (nat-key (mapv (fn [sv] ((accessors sv) (e/bvar 0))) shared)) :default)
                    kf-i   (e/lam "r" Ri  (nat-key (mapv (fn [sv] ((get-in li [:proj sv]) (e/bvar 0))) shared)) :default)
                    lst'   (e/app* (c' "Map.join") Ki accT Ri deci kf-acc kf-i lst (e/fvar (:fvar li)))
                    accT'  (e/app* (c' "Prod" z z) accT Ri)
                    ;; rewrap existing accessors through `fst`; add f_i's NEW vars through `snd`
                    re     (into {} (map (fn [[var f]] [var (fn [t] (f (e/app* (c' "Prod.fst" z z) accT Ri t)))]) accessors))
                    acc'   (reduce (fn [m var] (assoc m var (fn [t] ((get-in li [:proj var]) (e/app* (c' "Prod.snd" z z) accT Ri t)))))
                                   re (remove (set acc-vars) fvars))]
                (recur (inc i) lst' accT' (vec (distinct (concat acc-vars fvars))) acc'))))
        PJ (nest-left Rts)
        kept (vec (remove #{v} ordered-vars))                  ; deduplicated kept vars
        KKts (vec (repeat (count kept) N)) KK (nest KKts) decKK (dec-eq KKts)
        mapKK (e/app* (c' "Map" z z) KK S)
        ;; op : (Map KK S) → PJ → (Map KK S)   (bvar1 = acc, bvar0 = the k-way join tuple p)
        p* (e/bvar 0)
        kk (nat-key (mapv (fn [kv] ((accessors kv) p*)) kept))
        wval (reduce (fn [acc i] (e/app* mul acc ((:weight (nth layouts i)) (row-of Rts i p*))))
                     ((:weight l0) (row-of Rts 0 p*)) (range 1 k))
        cur (e/app* (c' "Option.getD" z) S (e/app* (c' "Map.lookup") KK S decKK kk (e/bvar 1)) zero)
        op (e/lam "acc" mapKK
             (e/lam "p" PJ
               (e/app* (c' "Map.insert") KK S decKK kk (e/app* add cur wval) (e/bvar 1)) :default)
             :default)
        e0 (e/app* (c' "Map.empty") KK S)
        term (e/app* (c' "List.foldl" z z) mapKK PJ op e0 join)
        ;; OUTPUT layout over the entries element type Prod KK S
        outR (e/app* (c' "Prod" z z) KK S)
        out-proj (into {} (map-indexed
                            (fn [i kv] [kv (fn [row] (prj KKts i (e/app* (c' "Prod.fst" z z) KK S row)))])
                            kept))]
    {:term term
     :lctx (into {} (map (fn [l] [(:fvar l) {:type (e/app (c' "List" z) (:row-type l))}]) layouts))
     :map-type mapKK :kk-type KK :kept-vars kept :row-types Rts
     :row1-type (first Rts) :row2-type (second Rts) :fids (mapv :fvar layouts)
     :out-layout {:row-type outR :vars kept :fvar out-fid :proj out-proj
                  :weight (fn [row] (e/app* (c' "Prod.snd" z z) KK S row))}}))

(defn eliminate
  "Two-factor case of `eliminate*` (the public 2-arg entry; `eliminate*` is the k-way generalization)."
  [carrier l1 l2 v out-fid] (eliminate* carrier [l1 l2] v out-fid))

(defn- run-fn
  "Compile the term to a curried Clojure fn `(f rows1) rows2`, over the layouts' source fvars."
  [{:keys [term row1-type row2-type fids]}]
  (let [[fid1 fid2] fids
        t1 (e/abstract1 term fid2) l2 (e/lam "f2" (e/app (c' "List" z) row2-type) t1 :default)
        t2 (e/abstract1 l2 fid1)   l1 (e/lam "f1" (e/app (c' "List" z) row1-type) t2 :default)]
    (eval (a/ansatz->clj (a/env) l1 []))))

;; ── the drop-in: certified `(factor-marginalize sr v (factor-join sr f1 f2))` ─────────────────────────
(defn- domain
  "Map each variable's distinct values (across both factors' assignments) to a 0-based Nat index."
  [v rels]
  (let [vals (distinct (keep #(get % v) (mapcat keys rels)))]
    (zipmap vals (range))))

(defn certified-eliminate
  "Eliminate the single shared variable `v` from factors `f1` `f2` (each `{:vars :rel}`, as in
   `wandler.inference.semiring`), keeping every other variable. Compiles the join-and-marginalize to a
   kernel term, certifies it with `optimize-cost`, runs it, and decodes the result back into a
   `{:vars :rel}` factor. Returns `{:factor <result> :verified? <bool> :rewrites <vec> :proof <expr>}`.
   The `:factor` equals `(factor-marginalize sr v (factor-join sr f1 f2))` — now with a kernel proof.
   `carrier` defaults to `counting` (Nat weights)."
  ([v f1 f2] (certified-eliminate v f1 f2 counting))
  ([v f1 f2 carrier]
   (let [encw (:enc carrier) decw (:dec carrier)
         v1 (vec (:vars f1)) v2 (vec (:vars f2))
         _ (when (or (neg? (.indexOf v1 v)) (neg? (.indexOf v2 v)))
             (throw (ex-info "v must be a variable of both factors" {:v v :f1 v1 :f2 v2})))
         doms (into {} (for [var (distinct (concat v1 v2))]
                         [var (domain var [(:rel f1) (:rel f2)])]))
         enc  (fn [vars rel] (mapv (fn [[asn w]] (conj (mapv #(get (doms %) (get asn %)) vars) (encw w))) rel))
         ->nested (fn [row] (reduce (fn [acc x] [x acc]) (last row) (reverse (butlast row))))
         rows1 (mapv ->nested (enc v1 (:rel f1)))
         rows2 (mapv ->nested (enc v2 (:rel f2)))
         l1 (base-layout carrier v1 F1-ID) l2 (base-layout carrier v2 F2-ID)
         built (eliminate carrier l1 l2 v 9003)
         res   (opt/optimize-cost (a/env) (:term built) :lctx (:lctx built) :sizes {F1-ID 1000 F2-ID 1000})
         f     (run-fn (assoc built :term (:term res)))
         out   ((f rows1) rows2)                            ; runtime Map {composite-key → weight}
         kept-vars (:kept-vars built)
         inv   (into {} (for [[var d] doms] [var (set/map-invert d)]))
         decode-key (fn [k] (let [flat (loop [x k acc []] (if (vector? x) (recur (second x) (conj acc (first x))) (conj acc x)))]
                              (zipmap kept-vars (map-indexed (fn [i idx] (get (inv (nth kept-vars i)) idx)) flat))))
         zv    (:zero-val carrier)
         rel   (into {} (comp (map (fn [[k w]] [(decode-key k) (decw w)]))
                              (remove (fn [[_ w]] (= w zv)))) out)]
     {:factor {:vars (set kept-vars) :rel rel}
      :verified? (boolean (:verified? res))
      :rewrites (:rewrites res)
      :proof (:proof res)})))

;; ══════════════════════════════════════════════════════════════════════════════════════════════════
;; Multi-step CHAIN certificate (Option C): compose per-step elimination proofs into ONE kernel theorem
;; `∀ sources, whole-naive ≡ whole-factored`, threading each step's output factor into the next as a
;; KERNEL TERM (`Map.entries`) — no trusted runtime hand-off. The composition is `Eq.trans` of
;; `congrArg (the next step's naive fn) (congrArg Map.entries prev-proof)` with the previous factored
;; term substituted in; the whole ∀-closed proof is `check-constant`'d. The intermediate factor threads
;; via its OUTPUT layout, so composite-key (multi-variable) intermediates compose like flat ones.

(defn certify-step*
  "Build + certify one elimination of `v` from a VECTOR of `layouts` (k ≥ 2), output bound to `out-fid`.
   `optimize-cost` factors every join in the k-way chain. Returns the raw kernel terms
   `{:naive :factored :proof :map-type :kk-type :row-types :fids :kept-vars :out-layout :verified?}`."
  [carrier layouts v out-fid]
  (let [built (eliminate* carrier layouts v out-fid)
        res   (opt/optimize-cost (a/env) (:term built) :lctx (:lctx built)
                                 :sizes (zipmap (:fids built) (repeat 1000)))]
    (assoc built :naive (:term built) :factored (:term res) :proof (:proof res)
           :verified? (boolean (:verified? res)))))

(defn certify-step
  "Two-factor case of `certify-step*` (the public 2-arg entry)."
  [carrier l1 l2 v out-fid] (certify-step* carrier [l1 l2] v out-fid))

(defn- compose-step
  "Fold one more elimination `sk` into the running composed proof `run`
   `{:naive :factored :proof :map-type :kk-type :sources :source-types}`. Threads the running output's
   `entries` into `sk`'s first fvar (`tau`); `sk`'s second fvar is a fresh source. The new proof is
   `Eq.trans (congrArg g (congrArg Map.entries run-proof)) (sk-proof[tau := entries run-factored])`."
  [run sk]
  (let [rk (:kk-type run) rmap (:map-type run)
        S (second (second (e/get-app-fn-args rmap)))      ; carrier weight type = the Map's value arg
        PkS (e/app* (c' "Prod" z z) rk S)
        entries-app (e/lam "m" rmap (e/app* (c' "Map.entries") rk S (e/bvar 0)) :default)
        ent (fn [m] (e/app entries-app m))
        [tau c] (:fids sk)
        Pe (e/app* (c' "congrArg" one one) rmap (e/app (c' "List" z) PkS)
                   (:naive run) (:factored run) entries-app (:proof run))
        g  (e/lam "x" (e/app (c' "List" z) PkS) (e/abstract1 (:naive sk) tau) :default)
        Cg (e/app* (c' "congrArg" one one) (e/app (c' "List" z) PkS) (:map-type sk)
                   (ent (:naive run)) (ent (:factored run)) g Pe)
        Pk' (e/instantiate1 (e/abstract1 (:proof sk) tau) (ent (:factored run)))
        new-naive (e/instantiate1 (e/abstract1 (:naive sk) tau) (ent (:naive run)))
        new-fact  (e/instantiate1 (e/abstract1 (:factored sk) tau) (ent (:factored run)))
        proof (e/app* (c' "Eq.trans" one) (:map-type sk)
                      (e/app g (ent (:naive run))) (e/app g (ent (:factored run))) new-fact Cg Pk')]
    {:naive new-naive :factored new-fact :proof proof
     :map-type (:map-type sk) :kk-type (:kk-type sk)
     :sources (conj (:sources run) c)
     :source-types (assoc (:source-types run) c (e/app (c' "List" z) (:row2-type sk)))}))

(defn chain-certificate
  "Compose an N-step elimination chain into ONE `check-constant`-verified theorem. `steps` = `[s1 … sn]`
   from `certify-step`; each `sk` (k>1) is built with `l1 = (:out-layout s(k-1))`, so it consumes the
   previous step's factor `entries` at its first fvar plus a fresh source fvar at its second. Returns
   `{:verified? :name :type :proof}` (or `{:verified? false :error}`) — the kernel theorem
   `∀ sources, whole-naive ≡ whole-factored`, with every intermediate factor threaded purely as a kernel
   term (no trusted runtime hand-off)."
  [steps thm-name]
  (let [s1 (first steps) [a b] (:fids s1)
        run0 {:naive (:naive s1) :factored (:factored s1) :proof (:proof s1)
              :map-type (:map-type s1) :kk-type (:kk-type s1) :sources [a b]
              :source-types {a (e/app (c' "List" z) (:row1-type s1))
                             b (e/app (c' "List" z) (:row2-type s1))}}
        run (reduce compose-step run0 (rest steps))
        env (a/env)
        lctx-all (into {} (map (fn [[fid t]] [fid {:type t}]) (:source-types run)))
        base-type (tc/infer-type (cert/mk-st env lctx-all) (:proof run))
        [proof typ] (reduce (fn [[p t] fid]
                              (let [ft (get-in lctx-all [fid :type])]
                                [(e/lam "f" ft (e/abstract1 p fid) :default)
                                 (e/forall "f" ft (e/abstract1 t fid) :default)]))
                            [(:proof run) base-type] (reverse (:sources run)))  ; first source outermost
        ci (kenv/mk-thm (name/from-string thm-name) [] typ proof)]
    (try
      (swap! a/ansatz-env kenv/check-constant ci)
      {:verified? true :name thm-name :type typ :proof proof
       :whole-factored (:factored run) :whole-naive (:naive run)
       :sources (:sources run) :source-types (:source-types run)
       :map-type (:map-type run) :kk-type (:kk-type run)
       :kept-vars (:kept-vars (last steps))}
      (catch Throwable t {:verified? false :name thm-name :error (.getMessage t)}))))

;; ══════════════════════════════════════════════════════════════════════════════════════════════════
;; General LIVE-FACTOR fold: certified VE over ANY factor graph (chain / tree / forest), min-degree
;; ordered — the generalization of the linear chain above. A LIVE FACTOR carries a provider TRIPLE
;; `{:nv :fv :proof}`: a "naive provider" term, a "factored provider" term, and a kernel proof `nv ≡ fv`
;; (nil = identical ⇒ refl). A base source's providers are its fvar (nv = fv, proof nil); an elimination's
;; output is `Map.entries` of its naive / factored fold, with proof `congrArg Map.entries (step proof)`.
;; So each elimination is certified IN ISOLATION over fresh fvars (certify-step / marginalize-one) and the
;; results compose by substituting providers under congruence — no trusted runtime hand-off, exactly as
;; the chain does, but now any input may itself be a prior intermediate, so trees and forests compose too.

(defn- subst
  "Substitute each `[fid val]` into `term` (the fids pairwise distinct, the vals independent of the fids)."
  [term pairs] (reduce (fn [t [fid val]] (e/instantiate1 (e/abstract1 t fid) val)) term pairs))

(defn marginalize-one
  "Arity-1 elimination: sum the variable `v` out of the SINGLE factor `l1` (no join), keeping every other
   variable. Same shape as `certify-step` but `:naive = :factored` and `:proof` = refl — there is no join
   to factor, so the per-key fold IS the only form (the min-degree planner hits this for a degree-1 var)."
  [{:keys [S add zero]} l1 v out-fid]
  (let [R1 (:row-type l1)
        kept (vec (remove #{v} (:vars l1)))
        KKts (vec (repeat (count kept) N)) KK (nest KKts) decKK (dec-eq KKts)
        mapKK (e/app* (c' "Map" z z) KK S)
        kvals (map (fn [kv] ((get-in l1 [:proj kv]) (e/bvar 0))) kept)
        kk (nat-key kvals)
        w  ((:weight l1) (e/bvar 0))
        cur (e/app* (c' "Option.getD" z) S (e/app* (c' "Map.lookup") KK S decKK kk (e/bvar 1)) zero)
        op (e/lam "acc" mapKK
             (e/lam "row" R1
               (e/app* (c' "Map.insert") KK S decKK kk (e/app* add cur w) (e/bvar 1)) :default) :default)
        e0 (e/app* (c' "Map.empty") KK S)
        term (e/app* (c' "List.foldl" z z) mapKK R1 op e0 (e/fvar (:fvar l1)))
        outR (e/app* (c' "Prod" z z) KK S)
        out-proj (into {} (map-indexed
                            (fn [i kv] [kv (fn [row] (prj KKts i (e/app* (c' "Prod.fst" z z) KK S row)))]) kept))]
    {:naive term :factored term :proof (e/app* (c' "Eq.refl" one) mapKK term)
     :map-type mapKK :kk-type KK :row1-type R1 :fids [(:fvar l1)] :kept-vars kept :verified? true
     :out-layout {:row-type outR :vars kept :fvar out-fid :proj out-proj
                  :weight (fn [row] (e/app* (c' "Prod.snd" z z) KK S row))}}))

(defn- combine
  "Plug provider triples `providers` (aligned to `step`'s `:fids`) into a certified `step`, returning a new
   LIVE FACTOR. `:nv`/`:fv` are `Map.entries` of the naive/factored fold (a List of rows — consumable as a
   downstream provider) and `:unwrapped-*` are the Map-level terms + proof (the final answer if this is the
   last factor). The proof composes (A) `gN(nv…) ≡ gN(fv…)` by congruence over each provider's own proof
   (one input at a time, skipping refl/nil), then (B) the step's own `gN(fv…) ≡ gF(fv…)`."
  [{:keys [S]} step providers]
  (let [fids (:fids step) mapT (:map-type step) KK (:kk-type step) gN (:naive step)
        n (count fids)
        nv-pairs (mapv (fn [fid p] [fid (:nv p)]) fids providers)
        fv-pairs (mapv (fn [fid p] [fid (:fv p)]) fids providers)
        new-nv (subst gN nv-pairs)
        new-fv (subst (:factored step) fv-pairs)
        ;; cur(i) = gN with fids ≤ i bound to fv, fids > i to nv
        cur (fn [i] (subst gN (vec (concat (map #(vector (nth fids %) (:fv (nth providers %))) (range 0 (inc i)))
                                           (map #(vector (nth fids %) (:nv (nth providers %))) (range (inc i) n))))))
        [A-proof] (loop [i 0, prev new-nv, proof nil]
                    (if (>= i n) [proof prev]
                        (let [p (nth providers i) pf (:proof p)]
                          (if (nil? pf) (recur (inc i) prev proof)
                              (let [fid (nth fids i) ptype (:type p)
                                    others (vec (concat (map #(vector (nth fids %) (:fv (nth providers %))) (range 0 i))
                                                        (map #(vector (nth fids %) (:nv (nth providers %))) (range (inc i) n))))
                                    body0 (subst gN others)
                                    fn-i (e/lam "x" ptype (e/abstract1 body0 fid) :default)
                                    curi (cur i)
                                    ;; congrArg @α β a₁ a₂ f h : f a₁ = f a₂ — a₁/a₂ are the ARGUMENTS
                                    ;; (this input's nv/fv), not the results (prev/curi = f a₁ / f a₂).
                                    cong (e/app* (c' "congrArg" one one) ptype mapT (:nv p) (:fv p) fn-i pf)
                                    proof' (if (nil? proof) cong
                                               (e/app* (c' "Eq.trans" one) mapT new-nv prev curi proof cong))]
                                (recur (inc i) curi proof'))))))
        B (subst (:proof step) fv-pairs)                       ; gN(fv…) ≡ gF(fv…), i.e. (cur n-1) ≡ new-fv
        full (if (nil? A-proof) B
                 (e/app* (c' "Eq.trans" one) mapT new-nv (cur (dec n)) new-fv A-proof B))
        PkS (e/app* (c' "Prod" z z) KK S)
        ent (fn [m] (e/app* (c' "Map.entries") KK S m))
        ent-app (e/lam "m" mapT (e/app* (c' "Map.entries") KK S (e/bvar 0)) :default)
        ent-proof (e/app* (c' "congrArg" one one) mapT (e/app (c' "List" z) PkS) new-nv new-fv ent-app full)]
    {:layout (:out-layout step) :map-type mapT :kk-type KK :type (e/app (c' "List" z) PkS)
     :nv (ent new-nv) :fv (ent new-fv) :proof ent-proof
     :unwrapped-nv new-nv :unwrapped-fv new-fv :unwrapped-proof full}))

(defn certify-graph
  "Certified variable elimination over an ARBITRARY factor graph `factors` (each `{:vars :rel}` →
   pre-built layouts), eliminating the vars in `order` (min-degree, least-mentioned-first) and keeping the
   rest. Each elimination combines the LIVE factors mentioning the var — arity 1 (`marginalize-one`, no
   join, refl) or arity 2 (`certify-step`, the certified aggregation-through-join) — and threads its output
   as a kernel-term provider into the next. Composes ONE `check-constant`-verified theorem
   `∀ sources, whole-naive ≡ whole-factored`. Returns `{:verified? :name :type :proof :whole-factored
   :sources :source-types :kept-vars}` (or `{:verified? false :error}`). Each elimination combines the LIVE
   factors mentioning the var — arity 1 (`marginalize-one`), arity 2, or arity ≥3 (a left-nested multi-way
   `Map.join` chain, every join factored by `try-fold-factor*`). The factor graph must reduce to a single
   final factor (connected)."
  [carrier factors order thm-name]
  (try
    (let [fid0 9200
          srcs (mapv (fn [i f] [(+ fid0 i) (base-layout carrier (vec (:vars f)) (+ fid0 i))]) (range) factors)
          source-types (into {} (map (fn [[fid l]] [fid (e/app (c' "List" z) (:row-type l))]) srcs))
          init (mapv (fn [[fid l]] {:layout l :nv (e/fvar fid) :fv (e/fvar fid) :proof nil
                                    :type (e/app (c' "List" z) (:row-type l))}) srcs)
          mentions? (fn [lf v] (contains? (set (:vars (:layout lf))) v))
          final (loop [live init, ord order, ofid (+ fid0 1000)]
                  (if-let [v (first ord)]
                    (let [involved (filterv #(mentions? % v) live)
                          rest* (filterv #(not (mentions? % v)) live)
                          step (if (= 1 (count involved))
                                 (marginalize-one carrier (:layout (first involved)) v ofid)
                                 (certify-step* carrier (mapv :layout involved) v ofid))   ; arity ≥2 incl. multi-way
                          newlf (combine carrier step involved)]
                      (recur (conj rest* newlf) (next ord) (inc ofid)))
                    live))
          _ (when-not (= 1 (count final))
              (throw (ex-info (str "elimination left " (count final) " factors (disconnected graph / keep spans components)")
                              {:remaining (count final)})))
          L (first final)
          env (a/env)
          lctx-all (into {} (map (fn [[fid t]] [fid {:type t}]) source-types))
          base-type (tc/infer-type (cert/mk-st env lctx-all) (:unwrapped-proof L))
          [proof typ] (reduce (fn [[p t] fid]
                                (let [ft (get source-types fid)]
                                  [(e/lam "f" ft (e/abstract1 p fid) :default)
                                   (e/forall "f" ft (e/abstract1 t fid) :default)]))
                              [(:unwrapped-proof L) base-type] (reverse (mapv first srcs)))  ; first source outermost
          ci (kenv/mk-thm (name/from-string thm-name) [] typ proof)]
      (swap! a/ansatz-env kenv/check-constant ci)
      {:verified? true :name thm-name :type typ :proof proof
       :whole-factored (:unwrapped-fv L) :whole-naive (:unwrapped-nv L)
       :sources (mapv first srcs) :source-types source-types
       :map-type (:map-type L) :kk-type (:kk-type L) :kept-vars (:vars (:layout L))})
    (catch Throwable t {:verified? false :name thm-name :error (.getMessage t)})))

;; ── the engine front-end: certified FAQ over a factor CHAIN ───────────────────────────────────────────
(defn- decode-key
  "Decode a runtime composite key `k` (nested `[i0 [i1 …]]` of Nat indices, or a bare index) into a
   `{var value}` assignment over `kept-vars`, inverting each variable's domain via `inv`."
  [kept-vars inv k]
  (let [flat (loop [x k acc []] (if (vector? x) (recur (second x) (conj acc (first x))) (conj acc x)))]
    (zipmap kept-vars (map-indexed (fn [i idx] (get (inv (nth kept-vars i)) idx)) flat))))

(defn certify-faq
  "Certified inference over a factor GRAPH `factors` (each `{:vars :rel}` as in `wandler.inference.semiring`),
   eliminating every variable not in `keep`. Returns
     `{:factor <result {:vars :rel}> :order <elim vars> :verified? <cert admitted?> :certificate <map>}`.
   `:factor` equals `(semiring/faq carrier keep order factors)`, and `:certificate` is the ONE
   `check-constant`-verified theorem `∀ sources, whole-naive ≡ whole-factored` for the whole graph (built by
   `certify-graph`'s live-factor fold). The elimination `:order` defaults to the min-degree plan
   (`semiring/elimination-order`); pass `:order` to override. Today: chain/tree/forest graphs (each
   elimination combines ≤2 live factors); a variable shared by ≥3 factors (multi-way join) is the frontier.
   The graph is run by codegen of the composed factored plan over the encoded sources."
  [carrier factors keep thm-name & {:keys [order]}]
  (let [encw (:enc carrier) decw (:dec carrier)
        rels (mapv :rel factors)
        allvars (distinct (mapcat :vars factors))
        doms (into {} (for [v allvars] [v (domain v rels)]))
        inv  (into {} (for [[v d] doms] [v (set/map-invert d)]))
        ->nested (fn [row] (reduce (fn [acc x] [x acc]) (last row) (reverse (butlast row))))
        enc-rows (fn [{:keys [vars rel]}]
                   (mapv (fn [[asn w]] (->nested (conj (mapv #(get (doms %) (get asn %)) vars) (encw w)))) rel))
        rows (mapv enc-rows factors)
        order (or order (sr/elimination-order keep factors))   ; #175 min-degree plan
        cert (certify-graph carrier factors order thm-name)
        kept-vars (:kept-vars cert)
        ;; codegen the composed factored plan as a curried fn over the source relations (in factor order)
        srcs (:sources cert) styp (:source-types cert)
        lam (reduce (fn [body fid] (e/lam "f" (get styp fid) (e/abstract1 body fid) :default))
                    (:whole-factored cert) (reverse srcs))
        f   (when (:verified? cert) (eval (a/ansatz->clj (a/env) lam [])))
        out (when f (reduce (fn [g rws] (g rws)) f (map #(nth rows %) (range (count rows)))))  ; sources f0,f1,…
        zv  (:zero-val carrier)
        rel (into {} (comp (map (fn [[k w]] [(decode-key kept-vars inv k) (decw w)]))
                           (remove (fn [[_ w]] (= w zv)))) out)]
    {:factor {:vars (set kept-vars) :rel rel}
     :order order
     :verified? (:verified? cert)
     :certificate cert}))
