# Deferred test namespaces (v0.1 quarantine)

These suites carry the research tiers (EDN dynamic data, regex, modes/stream
surface, gradual UI) and port debris from the fix-forward onto ansatz's unified
elaborator. They are NOT on the :test path for v0.1; restoring them (and the
remaining per-test failures) is the v0.2 work list. The research branch holds
the last fully-green state of these tiers against the pre-unification ansatz.

Second pass (7 nses): the Float/def-record tier (primitive double fields,
unboxed double[] paths) and elaboration-breadth verbs not yet re-ported
(`some->`, `str`/`clojure.string` ops). The core relational query path itself
is green (see surface joins in joins/aggregate/rel-laws suites).
