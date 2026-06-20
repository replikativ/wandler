;; String surface (clean tree): `str` (concat) + the common clojure.string fns → kernel String ops,
;; so idiomatic Clojure strings verify (not just explicit String.append). Element pipelines ride
;; collection fusion for free; the concat monoid laws are Init-only. Clean-tree port of
;; wandler.surface.strings (IR-agnostic copy-clean; the docs-only vocabulary metadata is dropped to
;; keep the clean tree self-contained).
(ns wandler.clean.surface.strings
  (:require [ansatz.surface.api :as api]
            [wandler.clean.surface.common :refer [nm]]
            [ansatz.kernel.expr :as e]))

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
