(ns wandler.backend-registry-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [wandler.exec.physical :as physical]))

(use-fixtures :each
  (fn [f]
    (let [saved (physical/cost-backends*)]
      (physical/clear-cost-backends!)
      (try (f)
           (finally
             (physical/clear-cost-backends!)
             (doseq [backend saved] (physical/register-cost-backend! backend)))))))

(deftest registration-preserves-other-backends
  (let [backend (fn [name form]
                  {:name name :lower (fn [& _] form) :cost (fn [& _] 1)})]
    (physical/register-cost-backend! (backend :columnar :old))
    (physical/register-cost-backend! (backend :raster :raster))
    (physical/register-cost-backend! (backend :columnar :new))
    (is (= #{:columnar :raster} (set (map :name (physical/cost-backends*)))))
    (is (= 2 (count (physical/cost-backends*))))
    (is (= :new ((:lower (last (physical/cost-backends*))))))))

(deftest lowering-only-compiles-affordable-candidates-until-one-recognizes
  (let [calls (atom [])
        register (fn [name cost form]
                   (physical/register-cost-backend!
                    {:name name :cost (fn [& _] cost)
                     :lower (fn [& _] (swap! calls conj name) form)}))]
    (register :expensive 100 :expensive)
    (register :second 6 :second)
    (register :unsupported 1 nil)
    (register :winner 4 :winner)
    (is (= {:backend :winner :cost 4.0 :form :winner}
           (physical/choose-cost-form nil {} [] 10)))
    (is (= [:unsupported :winner] @calls))
    (reset! calls [])
    (is (nil? (physical/choose-cost-form nil {} [] 1)))
    (is (empty? @calls))))
