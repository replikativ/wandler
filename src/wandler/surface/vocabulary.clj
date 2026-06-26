;; The surface VOCABULARY, as data (cohesion audit item 3).
;;
;; The wandler surface is a TYPE-DIRECTED STAGED ELABORATOR over a CLOSED verb
;; vocabulary (lean4's elab_rules, not abstract interpretation): compositional
;; inside the vocabulary, explicit about its edge. This namespace is the single
;; source of truth for that edge — every registered verb declares its signature,
;; its dispatch rule, and its kernel denotation + runtime lowering here, so:
;;   - (vocabulary-table) answers "what can I write?" at the REPL,
;;   - docs/REFERENCE.md is GENERATED from it (dev/gen_surface_md.clj),
;;   - boundary errors can cite it.
(ns wandler.surface.vocabulary)

(defonce ^{:doc "verb symbol → {:sig :dispatch :denotation :lowering :ns :tier}"}
  vocabulary (atom (sorted-map)))

(defn declare-verbs!
  "Bulk-declare verb metadata for a surface namespace (idempotent)."
  [ns-sym entries]
  (swap! vocabulary
         (fn [v] (reduce (fn [acc [sym m]] (assoc acc sym (assoc m :ns ns-sym)))
                         v entries))))

(defn vocabulary-table
  "The full verb table (sorted map). `:tier` other than :core marks pre-release surface."
  [] @vocabulary)

(defn describe
  "The metadata for one verb, or nil — useful in boundary errors."
  [sym] (get @vocabulary sym))

;; ── the core vocabulary (SEAM-1 namespaces declare on load, below) ───────────────────────

(declare-verbs! 'wandler.surface.collections
 '[[map         {:sig "(map f coll)" :dispatch "List → List.map · Strm/LSeq → smap (streams routing)" :denotation "List.map α β f coll" :lowering "amapl (unboxed long[]/double[] aware)" :tier :core}]
   [mapv        {:sig "(mapv f coll)" :dispatch "as map (verified pipelines are eager)" :denotation "List.map" :lowering "amapl" :tier :core}]
   [filter      {:sig "(filter p coll)" :dispatch "List only (raw streams are rejected: window first)" :denotation "List.filter α p coll" :lowering "afilter" :tier :core}]
   [filterv     {:sig "(filterv p coll)" :dispatch "as filter" :denotation "List.filter" :lowering "afilter" :tier :core}]
   [remove      {:sig "(remove p coll)" :dispatch "List; (remove p) ≡ (filter (complement p)) — inline-fn body negated in place, named-pred eta-expanded" :denotation "List.filter α (Bool.not ∘ p) coll" :lowering "afilter" :tier :core}]
   [drop-last   {:sig "(drop-last coll)" :dispatch "List (1-arg; drops the final element)" :denotation "List.dropLast α coll" :lowering "drop-last" :tier :core}]
   [partition-all {:sig "(partition-all n coll)" :dispatch "List → List of n-chunks (keeps short tail; n=0→one chunk)" :denotation "inlined foldl chunk (reverse∘map reverse∘foldl)" :lowering "the SOAC pipeline" :tier :core}]
   [partition   {:sig "(partition n coll)" :dispatch "as partition-all but DROPS the incomplete final chunk" :denotation "filter (length≡n) ∘ partition-all" :lowering "as the pipeline" :tier :core}]
   [take-nth    {:sig "(take-nth k coll)" :dispatch "List → every k-th element (0,k,2k,…)" :denotation "inlined foldl over a (counter,kept) Prod" :lowering "the SOAC pipeline" :tier :core}]
   [zip         {:sig "(zip a b)" :dispatch "two Lists → List of Prod pairs" :denotation "List.zip α β a b" :lowering "(map vector a b)" :tier :core}]
   [interleave  {:sig "(interleave a b)" :dispatch "two Lists → mapcat over (zip a b)" :denotation "List.flatMap (Prod→[fst,snd]) (List.zip a b)" :lowering "mapcat over zip" :tier :core}]
   [apply       {:sig "(apply ⊕ coll)" :dispatch "fold a collection with a monoid ⊕ (+→0 *→1 max→0); min has no Nat identity" :denotation "List.foldl ⊕ id⊕ coll" :lowering "as reduce" :tier :core}]
   [reduce      {:sig "(reduce f init coll)" :dispatch "List; accumulator type inferred from the STEP" :denotation "List.foldl acc elem f init coll" :lowering "afoldl; apfoldl (parallel fork-join) when the op holds a wandler.algebra monoid licence" :tier :core}]
   [reductions  {:sig "(reductions f init coll)" :dispatch "List → scanl · Strm → Strm.scan (incremental running aggregate)" :denotation "List.scanl / Strm.scan" :lowering "reductions / lazy scan" :tier :core}]
   [count       {:sig "(count coll)" :dispatch "List → length · Map → entry count · Value → vsize" :denotation "List.length / List.length∘Map.entries / vsize" :lowering "count" :tier :core}]
   [take        {:sig "(take n coll)" :dispatch "List → List.take · Strm/LSeq → the WINDOW (stream → List)" :denotation "List.take / Strm.take / LSeq.take" :lowering "take (lazy; windows infinite sources)" :tier :core}]
   [drop        {:sig "(drop n coll)" :dispatch "List" :denotation "List.drop" :lowering "drop" :tier :core}]
   [take-while  {:sig "(take-while p coll)" :dispatch "List" :denotation "List.takeWhile" :lowering "take-while" :tier :core}]
   [drop-while  {:sig "(drop-while p coll)" :dispatch "List" :denotation "List.dropWhile" :lowering "drop-while" :tier :core}]
   [range       {:sig "(range n) | (range)" :dispatch "(range n) → List.range · (range) → Strm.range (infinite source)" :denotation "List.range n / Strm.range" :lowering "range / identity-as-stream" :tier :core}]
   [nth         {:sig "(nth coll i default)" :dispatch "3-arg form only (2-arg needs a bounds proof)" :denotation "List.getD" :lowering "nth" :tier :core}]
   [reverse     {:sig "(reverse coll)" :dispatch "List" :denotation "List.reverse" :lowering "reverse" :tier :core}]
   [concat      {:sig "(concat a b …)" :dispatch "List (n-ary as nested append)" :denotation "List.append" :lowering "concat" :tier :core}]
   [interpose   {:sig "(interpose sep coll)" :dispatch "List" :denotation "List.intersperse" :lowering "interpose" :tier :core}]
   [first       {:sig "(first x)" :dispatch "Prod → fst · List → head? (Option)" :denotation "Prod.fst / List.head?" :lowering "nth 0 / first" :tier :core}]
   [second      {:sig "(second x)" :dispatch "Prod → snd · List → 2nd element (Option)" :denotation "Prod.snd / head?∘tail" :lowering "nth 1 / second" :tier :core}]
   [rest        {:sig "(rest xs)" :dispatch "List" :denotation "List.tail" :lowering "rest" :tier :core}]
   [last        {:sig "(last xs)" :dispatch "List → Option" :denotation "List.getLast?" :lowering "last" :tier :core}]
   [mapcat      {:sig "(mapcat f coll)" :dispatch "List; f : α → List β" :denotation "List.flatMap" :lowering "mapcat" :tier :core}]
   [map-indexed {:sig "(map-indexed f coll)" :dispatch "List; f : Nat → α → β" :denotation "List.mapIdx" :lowering "map-indexed" :tier :core}]
   [into        {:sig "(into [] xform? coll)" :dispatch "vector target only; the xform desugars to the nested SOAC form" :denotation "the desugared pipeline" :lowering "as the pipeline" :tier :core}]
   [transduce   {:sig "(transduce xform rf init coll)" :dispatch "xform = (comp (map f) (filter p) (remove p)…)" :denotation "reduce over the desugared pipeline" :lowering "as the pipeline (fuses + certifies)" :tier :core}]
   [sequence    {:sig "(sequence xform coll)" :dispatch "as into" :denotation "the desugared pipeline" :lowering "as the pipeline" :tier :core}]
   [inc         {:sig "(inc x)" :dispatch "Nat" :denotation "Nat.succ" :lowering "inc" :tier :core}]
   [dec         {:sig "(dec x)" :dispatch "Nat (truncated)" :denotation "Nat.sub x 1" :lowering "max 0 (dec x)" :tier :core}]
   [->          {:sig "(-> x f1 (f2 a) …)" :dispatch "pure form rewrite (macro_rules-shaped)" :denotation "the threaded form" :lowering "—" :tier :core}]
   [->>         {:sig "(->> x f1 (f2 a) …)" :dispatch "pure form rewrite" :denotation "the threaded form" :lowering "—" :tier :core}]])

(declare-verbs! 'wandler.surface.relational
 '[[join        {:sig "(join kf lf xs ys)" :dispatch "key fns compiled with element types injected" :denotation "Map.join K X Y dec kf lf xs ys" :lowering "group-by + hash probe (O(n)); optimizer may reorder/factor/spill, certified" :tier :core}]
   [group-by    {:sig "(group-by f coll)" :dispatch "key type from f's codomain; needs DecidableEq" :denotation "Map.group_by" :lowering "clojure.core/group-by" :tier :core}]
   [member      {:sig "(member x ys)" :dispatch "the canonical membership; optimizer rewrites filter∘member to the certified hash-index SEMIJOIN" :denotation "List.elem" :lowering "index probe after the rewrite" :tier :core}]
   [contains?   {:sig "(contains? ys x) | (contains? (set ys) x)" :dispatch "normalizes to List.elem (same semijoin)" :denotation "List.elem" :lowering "as member" :tier :core}]
   [some        {:sig "(some pred ys) | (some #{x} ys)" :dispatch "∃ via List.any; membership spellings normalize to List.elem" :denotation "List.any / List.elem" :lowering "some / index probe" :tier :core}]
   [every?      {:sig "(every? pred ys)" :dispatch "∀" :denotation "List.all" :lowering "every?" :tier :core}]
   [distinct    {:sig "(distinct xs)" :dispatch "needs DecidableEq on the element type" :denotation "List.eraseDups" :lowering "distinct" :tier :core}]
   [dedupe      {:sig "(dedupe xs)" :dispatch "consecutive duplicates" :denotation "List.eraseReps" :lowering "dedupe" :tier :core}]
   [sort        {:sig "(sort xs)" :dispatch "ascending; needs a Bool comparator (Nat.ble / <T>.ble)" :denotation "List.mergeSort" :lowering "sort" :tier :core}]
   [sort-by     {:sig "(sort-by keyfn xs)" :dispatch "key type from keyfn's codomain" :denotation "List.mergeSort with key comparator" :lowering "sort-by" :tier :core}]
   [vals        {:sig "(vals m)" :dispatch "Map K V (e.g. a group-by result)" :denotation "List.map snd (Map.entries m)" :lowering "vals" :tier :core}]
   [keys        {:sig "(keys m)" :dispatch "Map K V" :denotation "List.map fst (Map.entries m)" :lowering "keys" :tier :core}]
   [frequencies {:sig "(frequencies xs)" :dispatch "extrinsic AList accumulation" :denotation "foldl + AList.put-bump" :lowering "frequencies" :tier :core}]
   [->map       {:sig "(->map m)" :dispatch "Map boundary: entries as a Clojure map" :denotation "Map.entries" :lowering "identity (runtime Map IS a hash-map)" :tier :core}]
   [aempty      {:sig "(aempty K V)" :dispatch "extrinsic assoc-list map" :denotation "AList.empty" :lowering "{}" :tier :core}]
   [aput        {:sig "(aput m k v)" :dispatch "extrinsic assoc-list map" :denotation "AList.put" :lowering "assoc" :tier :core}]
   [aget        {:sig "(aget m k default)" :dispatch "extrinsic assoc-list map" :denotation "AList.get" :lowering "get" :tier :core}]])

(declare-verbs! 'wandler.surface.records
 '[[assoc       {:sig "(assoc r :k v …)" :dispatch "record → fused rebuild (overwrite-eliminated) · Value → vput chain" :denotation "<T>.mk with the field replaced / vput" :lowering "plain map / record ctor" :tier :core}]
   [update      {:sig "(update r :k f args…)" :dispatch "record (refined fields re-prove their refinement) · Value" :denotation "<T>.mk with f applied / vput∘vget" :lowering "as assoc" :tier :core}]
   [get-in      {:sig "(get-in r [path…])" :dispatch "record → nested projections · Value → vget chain" :denotation "nested e/proj / vget" :lowering "keyword access chain" :tier :core}]
   [assoc-in    {:sig "(assoc-in r [path…] v)" :dispatch "record → nested rebuilds · Value" :denotation "nested <T>.mk / vput" :lowering "as assoc" :tier :core}]
   [update-in   {:sig "(update-in r [path…] f args…)" :dispatch "record · Value" :denotation "nested rebuild with f at the leaf" :lowering "as assoc" :tier :core}]
   [select-keys {:sig "(select-keys r [:a :b])" :dispatch "record → a SYNTHESIZED projection record <T>__a_b" :denotation "<T>__a_b.mk of the kept projections" :lowering "defrecord" :tier :core}]])

(declare-verbs! 'wandler.surface.streams
 '[[smap        {:sig "(map f strm)" :dispatch "via the routed map: Strm/LSeq receivers" :denotation "Strm.smap / LSeq.smap" :lowering "compose / lazy map" :tier :streams}]
   [window      {:sig "(take n strm)" :dispatch "via the routed take: the BOUNDED window of an infinite source" :denotation "Strm.take / Stream.unfoldTake" :lowering "mapv over indices / unfold-take" :tier :streams}]])

(declare-verbs! 'ansatz.surface.data
 '[[get         {:sig "(get v k)" :dispatch "Value → vget · records fall back to keyword projection" :denotation "vget (Value.vkw k) v" :lowering "get" :tier :edn}]
   [int?        {:sig "(int? v) — and string? boolean? keyword? nil? map? vector? set? double? float? some? any?" :dispatch "Value receivers only (named error otherwise)" :denotation "vint? / vstr? / …" :lowering "predicate" :tier :edn}]])
