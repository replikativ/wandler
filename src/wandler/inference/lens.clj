(ns wandler.inference.lens
  "The BACKWARD direction — lenses / optics (PROGRAMMING_MODEL.md §12, structure 3). A lens between a
   source `S` and a view `V` is a `get : S → V` + `put : V → S → S` obeying the round-trip laws

     PutGet:  get (put v s) = v          (you read back what you wrote)
     GetPut:  put (get s) s = s          (writing back what you read changes nothing)

   This is the certified, *single-valued* corner of inversion (the well-behaved case; the multi-valued /
   measurable cases are relational/inference, behind a trusted engine — see §12). The audit found the IR
   is direction-neutral (a kernel `Eq`) and `records`' get/assoc are *already* a product lens — so the
   only gap was the laws. Here they are, kernel-proven for the canonical **first-projection lens** on a
   product (`get = Prod.fst`, `put = λ v p. Prod.mk v (Prod.snd p)`):

     `Lens.fst_PutGet`  — `fst (mk v (snd p)) = v`     (projection computes; rfl)        ★
     `Lens.fst_GetPut`  — `mk (fst p) (snd p) = p`     (structure eta in the kernel)     ★

   Lenses **compose hierarchically** (`lens-comp`) — that is the 'hierarchical inversion' shape. Records'
   `(:k r)` / `(assoc r :k v)` are the field-lens instance of this; the recent Para(Lens) result frames
   the gradient/backprop backward as a lens too. See filter-elimination-dependent."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

;; ── the certified product lens laws (kernel-proven) ──────────────────────────────────────────────
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- nm [s] (name/from-string s))
(defn- prodT [A B] (e/app* (e/const' (nm "Prod") [z z]) A B))
(defn- mkP [A B a b] (e/app* (e/const' (nm "Prod.mk") [z z]) A B a b))
(defn- fstP [A B p] (e/app* (e/const' (nm "Prod.fst") [z z]) A B p))
(defn- sndP [A B p] (e/app* (e/const' (nm "Prod.snd") [z z]) A B p))
(defn- eqT [T x y] (e/app* (e/const' (nm "Eq") [L1]) T x y))
(defn- reflT [T x] (e/app* (e/const' (nm "Eq.refl") [L1]) T x))

(defn- prove-put-get []
  ;; ∀ A B (v:A) (p:A×B), fst (mk v (snd p)) = v
  (let [A (e/fvar 1) B (e/fvar 2) v (e/fvar 3) p (e/fvar 4) AB (prodT A B)]
    [(-> (eqT A (fstP A B (mkP A B v (sndP A B p))) v)
         (#(e/forall' "p" AB (e/abstract1 % 4) :default)) (#(e/forall' "v" A (e/abstract1 % 3) :default))
         (#(e/forall' "B" type0 (e/abstract1 % 2) :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
     (-> (reflT A v)
         (#(e/lam "p" AB (e/abstract1 % 4) :default)) (#(e/lam "v" A (e/abstract1 % 3) :default))
         (#(e/lam "B" type0 (e/abstract1 % 2) :default)) (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]))

(defn- prove-get-put []
  ;; ∀ A B (p:A×B), mk (fst p) (snd p) = p   (structure eta)
  (let [A (e/fvar 1) B (e/fvar 2) p (e/fvar 4) AB (prodT A B)]
    [(-> (eqT AB (mkP A B (fstP A B p) (sndP A B p)) p)
         (#(e/forall' "p" AB (e/abstract1 % 4) :default))
         (#(e/forall' "B" type0 (e/abstract1 % 2) :default)) (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
     (-> (reflT AB p)
         (#(e/lam "p" AB (e/abstract1 % 4) :default))
         (#(e/lam "B" type0 (e/abstract1 % 2) :default)) (#(e/lam "A" type0 (e/abstract1 % 1) :default)))]))

(defonce ^:private cache (atom nil))

(defn install!
  "Admit the certified product-lens round-trip laws (idempotent): `Lens.fst_PutGet`, `Lens.fst_GetPut`."
  []
  (when-not (kenv/lookup (a/env) (nm "Lens.fst_GetPut"))
    (if-let [c @cache]
      (doseq [ci c] (swap! a/ansatz-env kenv/check-constant ci))
      (let [cis (mapv (fn [[nme [ty pf]]] (let [ci (kenv/mk-thm (nm nme) [] ty pf)]
                                            (swap! a/ansatz-env kenv/check-constant ci) ci))
                      [["Lens.fst_PutGet" (prove-put-get)] ["Lens.fst_GetPut" (prove-get-put)]])]
        (reset! cache cis))))
  (a/env))

;; ── runtime lenses — get/put, the well-behaved backward; compose hierarchically ──────────────────
(defrecord Lens [get put])

(def fst-lens "The certified first-projection lens on a pair `[a b]`." (->Lens first  (fn [a [_ b]] [a b])))
(def snd-lens "The second-projection lens on a pair `[a b]`."         (->Lens second (fn [b [a _]] [a b])))

(defn key-lens
  "The field lens for map key `k` — `(:k m)` / `(assoc m k v)`. Records' `(:k r)`/`(assoc r :k v)` are
   exactly this; the get/put laws hold for maps (GetPut needs `k` present)."
  [k] (->Lens #(get % k) (fn [v m] (assoc m k v))))

(defn lens-comp
  "Compose lenses HIERARCHICALLY: `(lens-comp outer inner)` focuses `inner` inside `outer`'s view — the
   'hierarchical inversion' shape. `get = inner.get ∘ outer.get`; `put` rebuilds through both."
  [outer inner]
  (->Lens (comp (:get inner) (:get outer))
          (fn [v s] ((:put outer) ((:put inner) v ((:get outer) s)) s))))

(defn round-trips?
  "Check the two lens laws at RUNTIME for a lens over sample `(s, v)` — GetPut and PutGet. (The kernel
   proves them for the product lens; this is the runtime witness for arbitrary instances.)"
  [{:keys [get put]} s v]
  {:get-put (= s (put (get s) s))
   :put-get (= v (get (put v s)))})

;; ── B5: delta-lenses — the INVERSE of the incremental ∂ (edit the view → propagate to the source) ─
;; A delta-lens propagates CHANGES: `get : S→V`, `put-Δ : ΔV → S → ΔS`. This is the bidirectional twin
;; of the DBSP ∂ (forward `ΔS→ΔV`); together they make an incremental view EDITABLE. The Para(Lens)
;; result frames the gradient/backward pass as exactly this shape. (The deeper comonad generalization —
;; ∂ over an abstract abelian group / a guarded `Strm` — is the remaining debt; PROGRAMMING_MODEL.md §13 B5.)
(defrecord DeltaLens [get put-delta])

(defn field-dlens
  "A delta-lens on a map field `k`: `get` reads it; a view-change `Δv` propagates to the source-change
   `(assoc s k Δv)`. Delta-PutGet: the new source's view is `Δv`."
  [k] (->DeltaLens #(get % k) (fn [dv s] (assoc s k dv))))

(defn zfilter-dlens
  "A delta-lens on a Z-set FILTER — the INVERSE of the linear ∂ filter. `get` keeps rows matching `pred`;
   a view-change `Δview` (a Z-set of matching insertions/retractions) propagates UNCHANGED to the source
   (the rows pass `pred` by construction). Forward ∂ + this backward Δ = a bidirectional incremental view."
  [pred]
  (->DeltaLens (fn [m] (into {} (filter (fn [[e _]] (pred e))) m))
               (fn [dview _s] (into {} (filter (fn [[e _]] (pred e))) dview))))

(defn dround-trip?
  "Witness the delta-lens law for a FIELD delta-lens: applying the source-Δ yields a source whose view
   equals the view-Δ (Diskin's delta-PutGet)."
  [{:keys [get put-delta]} s dv]
  (= dv (get (put-delta dv s))))
