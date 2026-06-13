;; Option NARROWING: an `if` whose condition is a nil-check on an Option-typed VARIABLE
;; compiles to `Option.elim`, with the variable NARROWED (rebound at the element type)
;; in the present branch — exactly what if-let / if-some / when-let / some-> macroexpand
;; into, so those idioms verify without special forms. Non-nilable ifs DELEGATE to the
;; built-in `if` via api/elab-base (the one-shot registry bypass), and `nil?`/`some?` on
;; Option values lower to Option.isNone/isSome.
;;
;; (At runtime Option is value-or-nil, so the narrowed variable is the same value — the
;; rebind is a type-level unwrap.)
(ns wandler.surface.option
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [wandler.surface.common :refer [nm]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [wandler.surface.vocabulary :as vocab]))


(defn- option-elem
  "If `expr` has type `Option α`, return α; else nil."
  [est expr]
  (let [t (api/arg-type est expr)
        [h aa] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h) (= "Option" (name/->string (e/const-name h))) (seq aa))
      (first aa))))

(defn- nilable-cond
  "Parse an `if` condition into [var-sym present-branch] (:then/:else = which branch runs
   when the value is PRESENT). nil if it isn't a nil-check on a variable. Covers what
   if-let/if-some/when-let/some-> expand to."
  [cform]
  (cond
    (symbol? cform) [cform :then]
    (and (seq? cform) ('#{nil? clojure.core/nil?} (first cform)) (symbol? (second cform)))   [(second cform) :else]
    (and (seq? cform) ('#{some? clojure.core/some?} (first cform)) (symbol? (second cform))) [(second cform) :then]
    :else nil))

(defn- ulvl [est ty]
  (lvl/succ-pred (e/sort-level (tc/infer-type (:tc est) ty))))

(defn- narrow-if
  "The Option-elim compilation of a nilable if, or nil to delegate."
  [est args]
  (let [n (inc (count args))]
    (when (and (>= n 3) (<= n 4))
      (when-let [[vsym present-key] (nilable-cond (first args))]
        (let [v-expr (try (api/elab est vsym) (catch Throwable _ nil))
              alpha (when v-expr (option-elem est v-expr))]
          (when alpha
            (let [then-form (nth args 1)
                  else-form (when (= n 4) (nth args 2))
                  present-form (if (= present-key :then) then-form else-form)
                  absent-form  (if (= present-key :then) else-form then-form)
                  ;; Option-MODE: the absent branch is nil/missing ⇒ the result is itself
                  ;; Option (present → some, absent → none). Else PLAIN: both branches : γ.
                  opt-mode? (or (= n 3) (nil? absent-form))
                  u1 (ulvl est alpha)
                  [present-expr fid]
                  (api/with-local est vsym alpha
                    (fn [est' fid] [(api/elab est' present-form) fid]))
                  plain-lam (e/lam (str vsym) alpha (e/abstract1 present-expr fid) :default)
                  lt (api/arg-type est plain-lam)
                  gamma (or (when (e/forall? lt) (e/forall-body lt))
                            (throw (ex-info "if (nilable): cannot infer the present-branch type"
                                            {:form (cons 'if args)})))]
              (if opt-mode?
                (let [ug (ulvl est gamma)
                      opt-g (e/app (e/const' (nm "Option") [ug]) gamma)
                      some-lam (e/lam (str vsym) alpha
                                      (e/abstract1 (e/app* (e/const' (nm "Option.some") [ug])
                                                           gamma present-expr) fid)
                                      :default)
                      none-e (e/app (e/const' (nm "Option.none") [ug]) gamma)
                      u2 (e/sort-level (tc/infer-type (:tc est) opt-g))]
                  (e/app* (e/const' (nm "Option.elim") [u1 u2])
                          alpha opt-g v-expr none-e some-lam))
                (let [absent-expr (api/elab est absent-form)
                      u2 (e/sort-level (tc/infer-type (:tc est) gamma))]
                  (e/app* (e/const' (nm "Option.elim") [u1 u2])
                          alpha gamma v-expr absent-expr plain-lam))))))))))

(defn- if-elaborator [est args]
  (or (narrow-if est args)
      ;; not a nilable condition — the built-in `if` (comparisons → dite, Bool → ite)
      (api/elab-base est (cons 'if args))))

(defn- isopt-elaborator
  "nil?/some? STANDALONE over an Option value → Option.isNone/isSome : Bool.
   (Inside an if condition the narrowing intercepts the FORM first.) Non-Option
   operands delegate to whatever else handles the symbol (e.g. the edn Value preds)."
  [pred-sym kernel-name]
  (fn [est args]
    (let [v (api/elab est (first args))
          a (option-elem est v)]
      (if a
        (e/app* (e/const' (nm kernel-name) [lvl/zero]) a v)
        (api/elab-base est (cons pred-sym args))))))

(defn install!
  "Register the narrowing `if` + Option-aware nil?/some? (idempotent)."
  []
  (api/register-term-elaborator! 'if if-elaborator)
  (api/register-term-elaborator! 'nil? (isopt-elaborator 'nil? "Option.isNone"))
  (api/register-term-elaborator! 'some? (isopt-elaborator 'some? "Option.isSome")))

(install!)

(vocab/declare-verbs! 'wandler.surface.option
 '[[if    {:sig "(if v then else) | (if (nil? v) … ) | (if (some? v) …)" :dispatch "Option-typed VARIABLE condition → Option.elim with v NARROWED to α in the present branch (what if-let/if-some/when-let/some-> expand to); anything else delegates to the built-in if" :denotation "Option.elim / dite / ite" :lowering "if (Option = value-or-nil)" :tier :core}]
   [nil?  {:sig "(nil? v)" :dispatch "Option → isNone; otherwise delegates (e.g. the EDN Value preds)" :denotation "Option.isNone" :lowering "nil?" :tier :core}]
   [some? {:sig "(some? v)" :dispatch "Option → isSome; otherwise delegates" :denotation "Option.isSome" :lowering "some?" :tier :core}]])
