# Native reference and reproducibility

The [complete mixed native reference](API.md) and [data manifest](api-manifest.json)
cover all **12 shipped Lean modules** against the unchanged mathematical/pin
input identified by `ae1998d20adc0b4fea4b311818b9d1b0a2859825` (tree
`fc6764ae85ce01f9741b1f86f4c588434a2f9c3b`), not by the commit of a
later documentation-only snapshot. Seven production leaves
have 66 native declaration entries; the aggregate import root has none.
Legacy `Clients` has six compatibility entries, `SymmetricClients` has none,
and `NaturalityClients` has two named local entries. The separate default-built
`RestrictedProductDualityTest` has zero native entries. **Every native instance
table is empty.** Native doc-gen4 classifies the two nonprivate named `local
instance`s in `NaturalityClients` as one `def` and one `theorem` in its
declarations table, not as global/exported instance-table rows. The
`Subgroup` small-arc lemma is retained despite its different namespace.

The 74 native entries comprise 23 `def`s and 51 `theorem`s. Exactly 25 lack
source docstrings: two CompactStage, eight Pairing, two TopologicalPairing,
ten CharacterReconstruction, one SymmetricDuality, one Naturality, and one
Clients. Each has a clearly marked **original catalogue explanation, not a
fabricated Lean docstring**. All 49 native comments match the corresponding
source bytes; no third-party docstrings, generated website, JS, fonts, or
dependency assets are bundled. This is a **public/native filtered**
reference, not a census of private declarations or compiler-generated proof
fields. A separate historical `docBlameThm` diagnostic reported **24
undocumented transparent equations** and selected truthful-header warnings
on ten leaves. This native catalogue counts **25
undocumented displayed entries**, including the `Clients` evaluation law;
these are different diagnostics and neither number proves optional lint
passes. Whether remaining missing native comments warrant later Lean edits
needs a separately scoped and reviewed source change.

## Fixed tool and input

The 15 unchanged mathematical `.lean`/toolchain/config SHA-256 inputs are
recorded in [`scripts/generate_api.py`](../scripts/generate_api.py) and in
the [manifest](api-manifest.json). The historical source commit/tree are
**labels for analyzed inputs**, not the shipping documentation commit's
commit identity; an external reviewer must bind the exact final artifact.
The separately cloned upstream `leanprover/doc-gen4` revision is
`97d4ecdfc8e09e7f511724c25e303d448de6a3db` (tree
`ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`) at Lean `v4.34.0-rc2`.
It is a **separate core-only tool**, not an added Lake project dependency.
This library pins that Lean version and mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` with eight other resolved
packages in `lake-manifest.json`; the source checkout and native generator
need no other Formal Frontier library.

First install pinned Lean and **successfully** fetch the matching precompiled
mathlib cache in this project before *any* project build. Cache failure is a
blocker, not permission to silently build mathlib from source:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build
```

Clone doc-gen4 separately at the exact revision/tree above and run
`PATH="$(dirname "$(elan which lean)"):$PATH" lake build doc-gen4` in its own
checkout. Choose a **fresh external** `OUT` per run (never under this Git
tree), and set `TOOL` to that checkout's `.lake/build/bin/doc-gen4`:

```sh
REV=ae1998d20adc0b4fea4b311818b9d1b0a2859825
OUT=/path/to/fresh/native-run
TOOL=/path/to/separate/doc-gen4/.lake/build/bin/doc-gen4
modules=(RestrictedProductDuality.CompactStage RestrictedProductDuality.SmallArc
  RestrictedProductDuality.Pairing RestrictedProductDuality.TopologicalPairing
  RestrictedProductDuality.CharacterReconstruction RestrictedProductDuality.SymmetricDuality
  RestrictedProductDuality.Naturality RestrictedProductDuality
  RestrictedProductDuality.Clients RestrictedProductDuality.SymmetricClients
  RestrictedProductDuality.NaturalityClients RestrictedProductDualityTest)
mkdir -p "$OUT/build" "$OUT/render" "$OUT/native-input"
for module in "${modules[@]}"; do
  path="${module//.//}.lean"
  LEAN_NUM_THREADS=2 lake env "$TOOL" single --build "$OUT/build" "$module" \
    "$OUT/build/api.db" "https://example.invalid/commit/$REV/$path"
done
"$TOOL" bibPrepass --build "$OUT/render" --none
"$TOOL" fromDb --build "$OUT/render" --manifest "$OUT/render/manifest.json" \
  "$OUT/build/api.db" "${modules[@]}"
for module in "${modules[@]}"; do
  cp "$OUT/render/doc-data/declaration-data-$module.bmp" "$OUT/native-input/"
done
python3 -B scripts/test_generate_api.py --native-data "$OUT/native-input"
python3 -B scripts/generate_api.py --native-data "$OUT/native-input" \
  --source-revision "$REV" \
  --docgen-revision 97d4ecdfc8e09e7f511724c25e303d448de6a3db --check
```

`example.invalid` is an inert native input identity, not a source link in
the shipped Markdown. Preserve **the actual native SQLite database, all 12
raw record bytes, complete command stdout/stderr and exits**, with tool and
dependency graphs, outside the shipped tree for independent intake. The two
independent runs retained for this candidate produced byte-identical raw
records and databases (SQLite SHA-256
`8c31eacd3446182cc1b93377312d8163ebf70c4b6a05bd4bf8c594771a160464`).
This observed repeatability is not a claim that arbitrary machines or tool
versions generate identical results. The external raw records and SQLite
database are needed for a data-only replay; these rendered files alone do not
provide native-run provenance or an independent authentication of either run.

## Adapter scope and costs

The bounded adapter checks the exact 15 source/pin hashes, 12 module names,
fixed row counts, unique declaration names, native kinds, all **zero-row
instance tables**, source paths/lines/docstrings, revision, displayed
signatures and critical binders, every raw record hash, and both checked
generated files. The normalized hashes in the manifest use sorted-key,
UTF-8 JSON with compact separators; they happen to equal the raw hashes for
this pinned tool/output, not by definition. Active/unknown HTML is refused.
Python optimization (`-O`) is refused **before writing**; `--check` refuses
stale outputs. Source-only archive and isolated parentless same-tree checkout
replays need no Git executable or original historical parent. This is not a
general Lean parser, proof checker, independently authenticated native run,
rights review, or release certificate.

The retained **2026-09-25 baseline** is `lake clean restricted-product-duality`,
followed by successful `lake exe cache get` (8,892 matching artifacts) and
`LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build`: in a **four-CPU-quota,
15 GiB** worker after cached dependencies, 12 modules and 2,855 Lake jobs
completed in **30 seconds at shell-second resolution**. Peak memory was not
measured. `lake -Kjobs=2` did **not** establish a Lake scheduler bound, and
`LEAN_NUM_THREADS=2` is not a whole-process or memory limit. Allow for a
separate doc-gen4 build, two native runs, 12 module imports/run, full
generation and negative tests; cache/download/disk costs depend on the host.
Observed cgroup memory includes reclaimable file cache; it is not a child RSS
or proof of peak headroom. The 15 GiB hard worker limit remains a real
constraint. No new recency benchmark or guessed memory peak is claimed.

## Attribution and rights

**Authors: Formal Frontier Agents.** Project contributors developed the
foundations and character reconstruction; Beacon developed the symmetric
duality and naturality results and clarified the release lifecycle and measured
build description. Later contributors prepared the public-import clients,
native-reference adapter, source-comment comparison and original catalogue
explanations; Folio provided the mathematical headline preparation. AI agents
participated throughout the Lean, documentation and review work.

The generator and tests adapt prior Formal Frontier work on finite-group Tate
cohomology, in turn based on polynomial-root stability and Anchor's
ideal-completion documentation recipe. They retain donor Apache-2.0 SPDX and
collective contributor credit; no individual copyright holder or waiver is
invented. Project source docstrings and catalogue prose are original Apache-2.0
contributions. Pinned
mathlib's `AddChar.zmodHom` has header authors **Yaël Dillies and Bhavik
Mehta**; `AddChar.toMonoidHomMulEquiv` has header author **Michael Stoll**.
The `Clients` bicharacter composes these *imported APIs*, not automatically
copied implementations. No private source exposition, NSW book asset, mathlib
source text, dependency docstrings or generated upstream website assets are
shipped. The existing [`LICENSE`](../LICENSE) and Lean/Lake headers remain
byte-exact. Whole-artifact rights clearance and independent review must be
recorded for the exact candidate and each applicable release stage; this
documentation describes its inputs and does not serve as a live acceptance registry.
