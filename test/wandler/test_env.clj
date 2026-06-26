(ns wandler.test-env
  "Shared, lazily-loaded kernel environments for tests.

   Loading Init is expensive and several namespaces need it, so each source is
   loaded at most ONCE per test run via these delays. Resolution order for the full
   `Init` env, first hit wins:

   1. A prebuilt PSS store at `test-data/init-store` — opened lazily with on-demand
      declaration loading; ~40ms to a usable env. Build it once with:

        clj -J-Xmx10g -M -e '(require (quote [ansatz.export.storage :as s]))
          (let [sm (s/open-store \"test-data/init-store\")]
            (s/import-ndjson-streaming! sm \"test-data/init.ndjson\" \"init\"))'

   2. `test-data/init.ndjson` replayed in TRUST mode (`:verify? false`) — tests use
      Init, they don't validate the export, so admit without re-typechecking.

   3. A previously-fetched cache store under `$XDG_CACHE_HOME/wandler/init-store`
      (see #4) — reused with no re-download.

   4. ON-DEMAND FETCH (opt-in, `WANDLER_FETCH_INIT=1`): download `init.ndjson` from a
      release asset (`WANDLER_INIT_URL`, default the ansatz GitHub release) and import
      it into the cache store once. This is how CI / a fresh clone gets a real Init
      without committing the ~96M export. The store is the Init export only (NOT
      Mathlib — wandler's laws are Init-only thanks to the owned ansatz.prelude).

   The full store is gitignored (large). `WANDLER_REQUIRE_STORE=1` turns a missing
   store into a hard failure (see `wandler.store-gate-test`). nil if nothing resolves,
   so integration tests skip. See docs/REPO_HARDENING_PLAN.md Phase 2."
  (:require [clojure.java.io :as io]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.export.storage :as storage]))

(defn- store-env [store-dir branch]
  (when (and store-dir (.exists (java.io.File. ^String store-dir)))
    (try (storage/load-env (storage/open-store store-dir) branch)
         (catch Throwable _ nil))))

(defn- ndjson-env [f]
  (when (.exists (java.io.File. ^String f))
    (:env (replay/replay (:decls (parser/parse-ndjson-file f)) :verify? false))))

;; ── on-demand fetch + local PSS cache (#3/#4 above) ──────────────────────────────
(def ^:private cache-store-dir
  (str (or (System/getenv "XDG_CACHE_HOME")
           (str (System/getProperty "user.home") "/.cache"))
       "/wandler/init-store"))

(def ^:private init-ndjson-url
  ;; The Init export attached to an ansatz GitHub release. Override for a mirror/test.
  (or (System/getenv "WANDLER_INIT_URL")
      ;; gzipped full Init export (~51M) attached to the ansatz release; a `.gz` URL is gunzipped on fetch.
      "https://github.com/replikativ/ansatz/releases/download/0.2.68/init.ndjson.gz"))

(defn- cached-store-env
  "Reuse a previously-fetched cache store (a `.complete` sentinel guards partials)."
  []
  (when (.exists (io/file cache-store-dir ".complete"))
    (store-env cache-store-dir "init")))

(defn- fetch-and-build-store!
  "Download `init.ndjson` from the release and import it into the cache PSS store
   (once), then return its env. Writes a `.complete` sentinel on success so a partial
   build is never reused. Returns nil on any failure (network etc.)."
  []
  (try
    (.mkdirs (io/file cache-store-dir))
    (let [tmp (java.io.File/createTempFile "wandler-init" ".ndjson")]
      (println "wandler.test-env: fetching Init export (~51M, once) from" init-ndjson-url)
      (with-open [raw (io/input-stream (.toURL (java.net.URI. init-ndjson-url)))
                  in  (if (.endsWith init-ndjson-url ".gz")
                        (java.util.zip.GZIPInputStream. raw)
                        raw)]
        (io/copy in tmp))
      (let [sm (storage/open-store cache-store-dir)]
        (storage/import-ndjson-streaming! sm (.getPath tmp) "init"))
      (.delete tmp)
      (spit (io/file cache-store-dir ".complete") "")
      (println "wandler.test-env: Init store cached at" cache-store-dir)
      (store-env cache-store-dir "init"))
    (catch Throwable e
      (println "wandler.test-env: Init fetch/build failed —" (.getMessage e))
      nil)))

(def init-full-env
  "Full Lean `Init` library. Resolution: test-data store -> test-data ndjson -> cache
   store -> (opt-in) on-demand fetch. nil if none resolve."
  (delay (or (store-env "test-data/init-store" "init")
             (ndjson-env "test-data/init.ndjson")
             (cached-store-env)
             (when (= "1" (System/getenv "WANDLER_FETCH_INIT"))
               (fetch-and-build-store!)))))

(def init-medium-env
  "Medium Init slice (2997 declarations) for fast Nat/monoid tests. Resolves from a local
   test-data medium store/ndjson; in CI (no local test-data) falls back to the FULL Init —
   a superset carrying the same Nat/monoid laws, which `init-full-env` fetches on demand —
   so medium-tier tests are exercised in CI instead of erroring on a missing fixture."
  (delay (or (store-env "test-data/init-medium-store" "init")
             (ndjson-env "test-data/init-medium.ndjson")
             @init-full-env)))
