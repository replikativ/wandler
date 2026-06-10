;; Verified affine-map fusion for Clojure reducer pipelines.
;;
;; A chain of affine maps over `Nat` — each `x ↦ a*x + b` — composes to a SINGLE
;; affine map `x ↦ A*x + B`.  Ordinary Clojure transducers cannot perform this
;; collapse: they keep every per-element multiply/add, because they cannot assume
;; a closure is affine.  Ansatz can, because it emits a kernel-checked proof that
;; the composition equals the collapsed map.
;;
;; The proof uses only Lean-core (`Init`) declarations — `Nat.left_distrib`,
;; `Nat.mul_assoc`, `Nat.add_assoc`, `funext`, `congrArg`, `Eq.trans`/`Eq.symm`.
;; No Mathlib.
;;
;; The collapsed runtime function does 1 multiply + 1 add per element instead of
;; the chain's 2K operations, so the verified pipeline is both provably equal and
;; faster than the transducer it replaces.

(ns ansatz.reducers.affine
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.reducers :as r])
  (:import [ansatz.kernel Env Expr TypeChecker]))

;; ============================================================
;; Kernel term builders (Nat arithmetic)
;; ============================================================

(defn- nm [s] (name/from-string s))
(def ^:private nat (e/const' (nm "Nat") []))
(def ^:private u1 (lvl/succ lvl/zero))

(defn- nlit [k]
  (e/app* (e/const' (nm "OfNat.ofNat") [lvl/zero]) nat (e/lit-nat k)
          (e/app (e/const' (nm "instOfNatNat") []) (e/lit-nat k))))

(defn- nmul [x y]
  (e/app* (e/const' (nm "HMul.hMul") [lvl/zero lvl/zero lvl/zero]) nat nat nat
          (e/app* (e/const' (nm "instHMul") [lvl/zero]) nat (e/const' (nm "instMulNat") []))
          x y))

(defn- nadd [x y]
  (e/app* (e/const' (nm "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero]) nat nat nat
          (e/app* (e/const' (nm "instHAdd") [lvl/zero]) nat (e/const' (nm "instAddNat") []))
          x y))

;; Lean-core lemma applications
(defn- distrib [a b c] (e/app* (e/const' (nm "Nat.left_distrib") []) a b c)) ; a*(b+c) = a*b + a*c
(defn- massoc [a b c] (e/app* (e/const' (nm "Nat.mul_assoc") []) a b c))     ; (a*b)*c = a*(b*c)
(defn- aassoc [a b c] (e/app* (e/const' (nm "Nat.add_assoc") []) a b c))     ; (a+b)+c = a+(b+c)
(defn- esym [ty a b h] (e/app* (e/const' (nm "Eq.symm") [u1]) ty a b h))
(defn- etr [ty a b c h1 h2] (e/app* (e/const' (nm "Eq.trans") [u1]) ty a b c h1 h2))
(defn- carg [f a1 a2 h] (e/app* (e/const' (nm "congrArg") [u1 u1]) nat nat a1 a2 f h))

(defn- affine-term
  "Kernel term `λx. a*x + b`."
  [a b]
  (e/lam "x" nat (nadd (nmul (nlit a) (e/bvar 0)) (nlit b)) :default))

;; ============================================================
;; affine_comp:  a2*(a1*x + b1) + b2  =  (a2*a1)*x + (a2*b1 + b2)
;; ============================================================

(defn- affine-comp-proof
  "Proof term for `a2*(a1*x + b1) + b2 = (a2*a1)*x + (a2*b1 + b2)`.
   Arguments are kernel Nat terms; `x` is the (bound) variable term."
  [a1 b1 a2 b2 x]
  (let [e1 (distrib a2 (nmul a1 x) b1)
        e2 (esym nat (nmul (nmul a2 a1) x) (nmul a2 (nmul a1 x)) (massoc a2 a1 x))
        e2' (carg (e/lam "t" nat (nadd (e/bvar 0) (nmul a2 b1)) :default)
                  (nmul a2 (nmul a1 x)) (nmul (nmul a2 a1) x) e2)
        e3 (etr nat (nmul a2 (nadd (nmul a1 x) b1))
                (nadd (nmul a2 (nmul a1 x)) (nmul a2 b1))
                (nadd (nmul (nmul a2 a1) x) (nmul a2 b1)) e1 e2')
        e4 (carg (e/lam "t" nat (nadd (e/bvar 0) b2) :default)
                 (nmul a2 (nadd (nmul a1 x) b1)) (nadd (nmul (nmul a2 a1) x) (nmul a2 b1)) e3)
        e5 (aassoc (nmul (nmul a2 a1) x) (nmul a2 b1) b2)]
    (etr nat (nadd (nmul a2 (nadd (nmul a1 x) b1)) b2)
         (nadd (nadd (nmul (nmul a2 a1) x) (nmul a2 b1)) b2)
         (nadd (nmul (nmul a2 a1) x) (nadd (nmul a2 b1) b2)) e4 e5)))

(defn- comp-term [g f]
  (e/app* (e/const' (nm "Function.comp") [u1 u1 u1]) nat nat nat g f))

;; ============================================================
;; Affine collapse
;; ============================================================

(defn collapse-coeffs
  "Fold affine coefficient pairs (in pipeline / application order) into the single
   `[A B]` of the composite `x ↦ A*x + B`."
  [coeffs]
  (reduce (fn [[A B] [a b]] [(* a A) (+ (* a B) b)])
          (first coeffs)
          (rest coeffs)))

(defn collapse-proof
  "Build the function-level certificate that a chain of affine maps collapses.

   `coeffs` is a vector of `[a b]` integer pairs, in pipeline order (the first
   pair is applied first).  Returns
     {:a A :b B :funext <Expr> :collapsed <Expr> :comp <Expr>}
   where `:funext` is a proof term of type `(f_K ∘ … ∘ f_1) = (λx. A*x + B)`.
   The caller type-checks it with a kernel `TypeChecker`."
  [coeffs]
  (let [x (e/bvar 0)
        [a1 b1] (first coeffs)
        init-nest (nadd (nmul (nlit a1) x) (nlit b1))
        [A B proof _nest]
        (reduce
         (fn [[A B proof nest] [a2 b2]]
           (let [A' (* a2 A) B' (+ (* a2 B) b2)
                 new-nest (nadd (nmul (nlit a2) nest) (nlit b2))
                 liftf (e/lam "t" nat (nadd (nmul (nlit a2) (e/bvar 0)) (nlit b2)) :default)
                 cong (carg liftf nest (nadd (nmul (nlit A) x) (nlit B)) proof)
                 comp (affine-comp-proof (nlit A) (nlit B) (nlit a2) (nlit b2) x)
                 new-proof (etr nat new-nest
                                (nadd (nmul (nlit a2) (nadd (nmul (nlit A) x) (nlit B))) (nlit b2))
                                (nadd (nmul (nlit A') x) (nlit B')) cong comp)]
             [A' B' new-proof new-nest]))
         [a1 b1 (e/app* (e/const' (nm "Eq.refl") [u1]) nat init-nest) init-nest]
         (rest coeffs))
        affs (mapv (fn [[a b]] (affine-term a b)) coeffs)
        ;; f_K ∘ (f_{K-1} ∘ ( … f_1)) : first-applied is innermost
        comp-chain (reduce comp-term (reverse affs))
        collapsed (affine-term A B)
        h (e/lam "x" nat proof :default)
        beta (e/lam "_" nat nat :default)
        funext (e/app* (e/const' (nm "funext") [u1 u1]) nat beta comp-chain collapsed h)]
    {:a A :b B :funext funext :collapsed collapsed :comp comp-chain}))

(defn collapse
  "Kernel-check the affine collapse and return a verified collapsed map.

   `coeffs` is a vector of `[a b]` integer pairs in pipeline order.  Returns
     {:a A :b B
      :fn      <runtime Clojure fn x ↦ A*x + B>
      :proof   <Expr : (f_K ∘ … ∘ f_1) = (λx. A*x + B)>
      :theorem-type <Expr, the kernel-checked equality type>
      :ops-before (* 2 K)   ; multiply/add ops the transducer chain runs per element
      :ops-after  2}        ; ops the collapsed map runs per element

   Throws if the proof does not type-check against `kernel-env`."
  ([^Env kernel-env coeffs] (collapse kernel-env coeffs {}))
  ([^Env kernel-env coeffs {:keys [fuel] :or {fuel 50000000}}]
   (let [{:keys [a b funext]} (collapse-proof coeffs)
         tc (doto (TypeChecker. kernel-env) (.setFuel (long fuel)))
         thm (.check tc funext)]          ; STRICT: re-checks every app arg (matches the
                                          ; docstring's "throws if the proof does not type-check")
     {:a a :b b
      :fn (fn ^long [^long x] (+ (* a x) b))
      :proof funext
      :theorem-type thm
      :ops-before (* 2 (count coeffs))
      :ops-after 2})))

(defn affine-fn
  "A plain runtime Clojure affine map `x ↦ a*x + b`."
  [a b]
  (fn ^long [^long x] (+ (* a x) b)))
