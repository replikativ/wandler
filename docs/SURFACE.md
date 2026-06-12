# The wandler surface vocabulary

> GENERATED from `wandler.surface.vocabulary` — edit there, then `clj -M -e '(load-file "dev/gen_surface_md.clj")'`.

The wandler surface is a **type-directed staged elaborator over a closed verb
vocabulary** (lean4's `elab_rules`, not abstract interpretation): every verb below
elaborates to a kernel denotation, optimizes under certified rewriting, and lowers
to the listed runtime form. It is compositional *inside* this vocabulary — verbs
nest arbitrarily — and explicit about its edge: anything outside it is an honest
named error, never silent miscompilation. `:tier` other than `core` is pre-release
surface.

## `wandler.surface.collections`

| verb | signature | dispatch | kernel denotation | runtime lowering | tier |
|---|---|---|---|---|---|
| `->` | `(-> x f1 (f2 a) …)` | pure form rewrite (macro_rules-shaped) | `the threaded form` | — | core |
| `->>` | `(->> x f1 (f2 a) …)` | pure form rewrite | `the threaded form` | — | core |
| `concat` | `(concat a b …)` | List (n-ary as nested append) | `List.append` | concat | core |
| `count` | `(count coll)` | List → length · Map → entry count · Value → vsize | `List.length / List.length∘Map.entries / vsize` | count | core |
| `drop` | `(drop n coll)` | List | `List.drop` | drop | core |
| `drop-while` | `(drop-while p coll)` | List | `List.dropWhile` | drop-while | core |
| `filter` | `(filter p coll)` | List only (raw streams are rejected: window first) | `List.filter α p coll` | afilter | core |
| `filterv` | `(filterv p coll)` | as filter | `List.filter` | afilter | core |
| `first` | `(first x)` | Prod → fst · List → head? (Option) | `Prod.fst / List.head?` | nth 0 / first | core |
| `interpose` | `(interpose sep coll)` | List | `List.intersperse` | interpose | core |
| `into` | `(into [] xform? coll)` | vector target only; the xform desugars to the nested SOAC form | `the desugared pipeline` | as the pipeline | core |
| `last` | `(last xs)` | List → Option | `List.getLast?` | last | core |
| `map` | `(map f coll)` | List → List.map · Strm/LSeq → smap (streams routing) | `List.map α β f coll` | amapl (unboxed long[]/double[] aware) | core |
| `map-indexed` | `(map-indexed f coll)` | List; f : Nat → α → β | `List.mapIdx` | map-indexed | core |
| `mapcat` | `(mapcat f coll)` | List; f : α → List β | `List.flatMap` | mapcat | core |
| `mapv` | `(mapv f coll)` | as map (verified pipelines are eager) | `List.map` | amapl | core |
| `nth` | `(nth coll i default)` | 3-arg form only (2-arg needs a bounds proof) | `List.getD` | nth | core |
| `range` | `(range n) | (range)` | (range n) → List.range · (range) → Strm.range (infinite source) | `List.range n / Strm.range` | range / identity-as-stream | core |
| `reduce` | `(reduce f init coll)` | List; accumulator type inferred from the STEP | `List.foldl acc elem f init coll` | afoldl; apfoldl (parallel fork-join) when the op holds a wandler.algebra monoid licence | core |
| `reductions` | `(reductions f init coll)` | List → scanl · Strm → Strm.scan (incremental running aggregate) | `List.scanl / Strm.scan` | reductions / lazy scan | core |
| `rest` | `(rest xs)` | List | `List.tail` | rest | core |
| `reverse` | `(reverse coll)` | List | `List.reverse` | reverse | core |
| `second` | `(second x)` | Prod → snd · List → 2nd element (Option) | `Prod.snd / head?∘tail` | nth 1 / second | core |
| `sequence` | `(sequence xform coll)` | as into | `the desugared pipeline` | as the pipeline | core |
| `take` | `(take n coll)` | List → List.take · Strm/LSeq → the WINDOW (stream → List) | `List.take / Strm.take / LSeq.take` | take (lazy; windows infinite sources) | core |
| `take-while` | `(take-while p coll)` | List | `List.takeWhile` | take-while | core |
| `transduce` | `(transduce xform rf init coll)` | xform = (comp (map f) (filter p) (remove p)…) | `reduce over the desugared pipeline` | as the pipeline (fuses + certifies) | core |

## `wandler.surface.edn`

| verb | signature | dispatch | kernel denotation | runtime lowering | tier |
|---|---|---|---|---|---|
| `get` | `(get v k)` | Value → vget · records fall back to keyword projection | `vget (Value.vkw k) v` | get | edn |
| `int?` | `(int? v) — and string? boolean? keyword? nil? map? vector? set? double? float? some? any?` | Value receivers only (named error otherwise) | `vint? / vstr? / …` | predicate | edn |

## `wandler.surface.records`

| verb | signature | dispatch | kernel denotation | runtime lowering | tier |
|---|---|---|---|---|---|
| `assoc` | `(assoc r :k v …)` | record → fused rebuild (overwrite-eliminated) · Value → vput chain | `<T>.mk with the field replaced / vput` | plain map / record ctor | core |
| `assoc-in` | `(assoc-in r [path…] v)` | record → nested rebuilds · Value | `nested <T>.mk / vput` | as assoc | core |
| `get-in` | `(get-in r [path…])` | record → nested projections · Value → vget chain | `nested e/proj / vget` | keyword access chain | core |
| `select-keys` | `(select-keys r [:a :b])` | record → a SYNTHESIZED projection record <T>__a_b | `<T>__a_b.mk of the kept projections` | defrecord | core |
| `update` | `(update r :k f args…)` | record (refined fields re-prove their refinement) · Value | `<T>.mk with f applied / vput∘vget` | as assoc | core |
| `update-in` | `(update-in r [path…] f args…)` | record · Value | `nested rebuild with f at the leaf` | as assoc | core |

## `wandler.surface.relational`

| verb | signature | dispatch | kernel denotation | runtime lowering | tier |
|---|---|---|---|---|---|
| `->map` | `(->map m)` | Map boundary: entries as a Clojure map | `Map.entries` | identity (runtime Map IS a hash-map) | core |
| `aempty` | `(aempty K V)` | extrinsic assoc-list map | `AList.empty` | {} | core |
| `aget` | `(aget m k default)` | extrinsic assoc-list map | `AList.get` | get | core |
| `aput` | `(aput m k v)` | extrinsic assoc-list map | `AList.put` | assoc | core |
| `contains?` | `(contains? ys x) | (contains? (set ys) x)` | normalizes to List.elem (same semijoin) | `List.elem` | as member | core |
| `dedupe` | `(dedupe xs)` | consecutive duplicates | `List.eraseReps` | dedupe | core |
| `distinct` | `(distinct xs)` | needs DecidableEq on the element type | `List.eraseDups` | distinct | core |
| `every?` | `(every? pred ys)` | ∀ | `List.all` | every? | core |
| `frequencies` | `(frequencies xs)` | extrinsic AList accumulation | `foldl + AList.put-bump` | frequencies | core |
| `group-by` | `(group-by f coll)` | key type from f's codomain; needs DecidableEq | `Map.group_by` | clojure.core/group-by | core |
| `join` | `(join kf lf xs ys)` | key fns compiled with element types injected | `Map.join K X Y dec kf lf xs ys` | group-by + hash probe (O(n)); optimizer may reorder/factor/spill, certified | core |
| `keys` | `(keys m)` | Map K V | `List.map fst (Map.entries m)` | keys | core |
| `member` | `(member x ys)` | the canonical membership; optimizer rewrites filter∘member to the certified hash-index SEMIJOIN | `List.elem` | index probe after the rewrite | core |
| `some` | `(some pred ys) | (some #{x} ys)` | ∃ via List.any; membership spellings normalize to List.elem | `List.any / List.elem` | some / index probe | core |
| `sort` | `(sort xs)` | ascending; needs a Bool comparator (Nat.ble / <T>.ble) | `List.mergeSort` | sort | core |
| `sort-by` | `(sort-by keyfn xs)` | key type from keyfn's codomain | `List.mergeSort with key comparator` | sort-by | core |
| `vals` | `(vals m)` | Map K V (e.g. a group-by result) | `List.map snd (Map.entries m)` | vals | core |

## `wandler.surface.streams`

| verb | signature | dispatch | kernel denotation | runtime lowering | tier |
|---|---|---|---|---|---|
| `smap` | `(map f strm)` | via the routed map: Strm/LSeq receivers | `Strm.smap / LSeq.smap` | compose / lazy map | streams |
| `window` | `(take n strm)` | via the routed take: the BOUNDED window of an infinite source | `Strm.take / Stream.unfoldTake` | mapv over indices / unfold-take | streams |

