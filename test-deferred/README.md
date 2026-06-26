# Deferred test namespaces

## The precise blocker (diagnosed during the v0.2 Phase-3 revival)

Most of these suites now PASS STANDALONE (fresh JVM, e.g.
`clj -Sdeps '{:aliases {:probe {:extra-paths ["test" "test-deferred"]}}}' -M:probe \
   -e "(require '[clojure.test :as t] '[wandler.edn-runtime-test]) (t/run-tests 'wandler.edn-runtime-test)"`)
but fail IN COMBINATION: the test runner is one JVM, the surface/codegen registries are
global atoms, and tests `reset!` the kernel env independently — so one namespace's
installs (stream verb routing, EDN get/predicates, structure-registry entries against a
since-replaced env) leak into the next. The fix is a shared isolation fixture
(snapshot/restore the registries + env around each ns), which is its own work item —
not per-test bugs.

## Genuinely-open items (beyond isolation)

- `wandler.exec.mode` runtime lowering of WF-fix functions over custom inductives emits
  an "unsupported rec pattern" throw (verification is fine; the RUNTIME lowering of
  WellFounded.fix over non-Nat domains is unfinished).
- `veq` (EDN structural equality) is `^:partial`: the WF encoder can't yet afford the
  11×11 nested-match refinement (121 branches × embedded decrease proofs) — encoder
  scaling follow-up. The TYPE is still kernel-checked.
- The unboxed double[]/Float tier (collections double-array, defrecord primitive
  fields): the primitive `emit-hinted-fn` path needs finishing for Float folds/filters.
- reducers `prove-pipeline` certification (3 assertions) — the reducers tier's own
  certification plumbing predates the seams; rebase on wandler.algebra at tier revival.
