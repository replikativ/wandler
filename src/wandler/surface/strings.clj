;; String surface: `str` (concat) + the common clojure.string fns → kernel String ops,
;; so idiomatic Clojure strings verify (not just explicit String.append). The element
;; pipelines ride collection fusion for free; the concat monoid laws are Init-only.
(ns wandler.surface.strings
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [wandler.surface.vocabulary :as vocab]))

(defn- nm [s] (name/from-string s))

(defn- str-elaborator [est args]
  ;; (str a b c …) folds String.append; each arg must already be a String.
  (when (empty? args)
    (throw (ex-info "str: at least one String argument required in a verified body" {})))
  (reduce (fn [acc x] (e/app* (e/const' (nm "String.append") []) acc (api/elab est x)))
          (api/elab est (first args))
          (rest args)))

(defn- unop [const]
  (fn [est args] (e/app (e/const' (nm const) []) (api/elab est (first args)))))

(defn- starts-with-elaborator [est args]
  ;; (starts-with? s prefix) → String.isPrefixOf prefix s
  (e/app* (e/const' (nm "String.isPrefixOf") [])
          (api/elab est (second args))
          (api/elab est (first args))))

(defn install!
  "Register the string verbs (idempotent). clojure.string/* spellings and bare names both work."
  []
  (api/register-term-elaborator! 'str str-elaborator)
  (api/register-term-elaborator! 'clojure.core/str str-elaborator)
  (doseq [[sym const] [['upper-case "String.toUpper"] ['clojure.string/upper-case "String.toUpper"]
                       ['lower-case "String.toLower"] ['clojure.string/lower-case "String.toLower"]]]
    (api/register-term-elaborator! sym (unop const)))
  (api/register-term-elaborator! 'starts-with? starts-with-elaborator)
  (api/register-term-elaborator! 'clojure.string/starts-with? starts-with-elaborator))

(install!)

(vocab/declare-verbs! 'wandler.surface.strings
 '[[str          {:sig "(str a b …)" :dispatch "String args (folds the concat monoid)" :denotation "String.append fold" :lowering "str" :tier :core}]
   [upper-case   {:sig "(clojure.string/upper-case s)" :dispatch "String" :denotation "String.toUpper" :lowering "clojure.string/upper-case" :tier :core}]
   [lower-case   {:sig "(clojure.string/lower-case s)" :dispatch "String" :denotation "String.toLower" :lowering "clojure.string/lower-case" :tier :core}]
   [starts-with? {:sig "(clojure.string/starts-with? s prefix)" :dispatch "String" :denotation "String.isPrefixOf prefix s" :lowering "clojure.string/starts-with?" :tier :core}]])
