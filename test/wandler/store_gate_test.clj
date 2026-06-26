(ns wandler.store-gate-test
  "CI honesty gate for the integration suite.

   Most of wandler's tests are integration tests that need the full Lean `Init`
   store (`test-data/init-store`, a gitignored ~173M PSS store — see
   `wandler.test-env`). Without it, `@test-env/init-full-env` is nil and those
   tests guard on `(ready?)` and skip — so a STORELESS run passes green while
   exercising almost nothing.

   This namespace makes that visible and, in CI, fatal:
   - Locally (no env var): prints a loud banner when the store is absent, so the
     green is never mistaken for integration coverage. Does NOT fail — a dev
     without the 173M store can still run the unit-level tests.
   - In CI: set `WANDLER_REQUIRE_STORE=1`. Then a missing store FAILS this test,
     so a storeless CI run can never be reported as a passing integration run.

   See docs/REPO_HARDENING_PLAN.md Phase 2."
  (:require [clojure.test :refer [deftest is]]
            [wandler.test-env :as test-env]))

(deftest store-present-when-required
  (let [require? (= "1" (System/getenv "WANDLER_REQUIRE_STORE"))
        present? (some? @test-env/init-full-env)]
    (when-not present?
      (println (str "\n"
                    "════════════════════════════════════════════════════════════════════\n"
                    " ⚠  wandler: Init store ABSENT (test-data/init-store).\n"
                    "    The integration suite (~104 of ~118 test namespaces) is SKIPPING.\n"
                    "    A green result here does NOT mean the integration tests passed.\n"
                    "    Build the store (see wandler.test-env) or, in CI, set\n"
                    "    WANDLER_REQUIRE_STORE=1 to turn this into a hard failure.\n"
                    "════════════════════════════════════════════════════════════════════\n")))
    (if require?
      (is present?
          "WANDLER_REQUIRE_STORE=1 but no Init store at test-data/init-store — the integration suite would silently skip. Mount/build the store before running CI integration.")
      ;; Local mode: assert nothing about presence; the banner above is the signal.
      (is true))))
