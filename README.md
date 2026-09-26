# Restricted-product duality

Authors: Formal Frontier Agents. Original Formal Frontier contributions are
offered under Apache-2.0 (see [`LICENSE`](LICENSE)); imported dependency APIs
retain their own authorship and licenses. Release of the complete artifact
requires separate exact-tree rights review.

Reusable Lean theory of restricted products and Pontryagin duality.

Responsible maintainer: Beacon.

## Status

This repository develops reusable restricted-product character theory.
Historical mathematical reviews approved PRs #2, #3, #5 and #6; README-only
PR #7 was accepted at `c2a54a2547185e8db3ddfc860a749c265d2b8e5a`.
The module-migration and public-import client candidate PR #8
(`d69e71cc9cfa490376db400569be95c66975505d`) received independent
ordinary-main review #2975 (issue #1 comment 40197), Beacon's ordinary-main
acceptance (issue #1 comment 40233), and exact-tree integration (issue #1
comment 40239) as `ae1998d20adc0b4fea4b311818b9d1b0a2859825` (tree
`fc6764ae85ce01f9741b1f86f4c588434a2f9c3b`). These dated historical
records are not live registry status. The accepted library at this revision proves:

- every compact subset of a cofinite restricted product with open
  distinguished subsets lies in one finite exceptional-coordinate stage;
- a subgroup mapped by a circle-valued homomorphism into the centered
  `π / 2` arc lies in its kernel;
- orthogonality makes the coordinatewise product pairing of two cofinite
  restricted products finitely supported, independent of its finite
  presentation, and multiplicative in both variables;
- jointly continuous local bicharacters induce a jointly continuous global
  pairing and a canonical continuous homomorphism to the Pontryagin dual; and
- local separation in the second variable makes that homomorphism injective;
- continuity of a global character forces finite coordinate dependence on the
  distinguished product, for an arbitrary index type;
- explicit bijectivity of every local character map together with the exact
  right-annihilator equality reconstructs every global character, proving
  surjectivity without nondegeneracy or cardinality shortcuts; and
- when the character-domain coordinates are finite discrete groups and the
  representing coordinates are topological groups, explicit compact-open test
  sets prove continuity of the reconstruction map and bundle the result as a
  `ContinuousMulEquiv`; and
- left local perfectness and the reverse exact-annihilator equality directly
  give the opposite-direction equivalence and its evaluation identity, without
  invoking a general Pontryagin biduality theorem; and
- coordinatewise continuous homomorphisms preserving distinguished subgroups
  cofinitely induce restricted-product maps, and pointwise adjoint maps satisfy
  the contravariant naturality square for the pairing and duality equivalence.

The compact-stage theorem and the bundled equivalence are exercised at empty,
nonempty finite, and genuinely infinite index types in
`RestrictedProductDuality/Clients.lean`.

The naturality clients exercise arbitrary and infinite index types and
apply the full naturality square to a genuinely non-identity adjoint
coordinate map on both restricted products.

That accepted revision also opts the mathematical files into Lean's
module system, gives the original anonymous clients private stable names and
builds `RestrictedProductDualityTest.lean` from the public umbrella import.
The existing six public `Clients` helpers remain available through the root
import, including `punitBicharacter` and `zmodBicharacter`. Private named tests
are audit handles, not an advertised mathematical API. AI agents developed
the Lean code and documentation with pinned-toolchain checks. Ordinary-main
review does not accept this documentation successor, release readiness,
redistribution rights or source correspondence. [`formalization.yaml`](formalization.yaml)
records the methods and historical review distinction.

Accepted main does **not** yet contain the general locally compact-coordinate
theorem of NSW (1.1.13) or the arithmetic inputs of NSW (8.5.2). The repository
claims no NSW source correspondence or coverage.
Subsequent mathematical or API changes still require fresh-context review and
maintainer acceptance before integration.

The motivating mathematical proof exposition at
`FormalFrontier/source-nsw@6aa9219432580134ac086953d1fe98599c88d6e0:expositions/finite-restricted-product-pontryagin-duality.md`
received independent review #936 and source-nsw issue #133 comment 8141.
That review covers the Markdown mathematics only: it does not validate this
Lean code or establish Lean/source correspondence or coverage.

## Public API and hypotheses

Import `RestrictedProductDuality` for the full API, or directly import one of
the modules below. For arbitrary cofinite index types, `cofiniteStage` and
`exists_subset_cofiniteStage` control compact subsets when each distinguished
set is **open**. `Subgroup.le_ker_of_mapsTo_centeredArc` supplies the small-arc
kernel argument. `pairing`, `pairing_eq_prod` and `pairingHom` evaluate a
finite-support circle-valued bicharacter; orthogonality of the two distinguished
subgroups makes the support finite. `continuous_pairing` requires joint local
continuity and both families of distinguished subgroups open.

`toPontryaginDual` gives a continuous map from the representing restricted
product into the compact-open dual; `toPontryaginDual_injective` separately
requires local separation. `rightCharacter` and `rightAnnihilator` describe
the **actual** local character map and its exact annihilator. The reconstruction
and `toPontryaginDual_surjective` require bijectivity of every right-character
map and equality of the right annihilator with the representing subgroup;
neither condition follows merely from local nondegeneracy. To obtain
`pontryaginDualEquiv`, inverse continuity additionally requires finite discrete
character-domain coordinate groups and topological representing groups. Its
`symmetricPontryaginDualEquiv` counterpart swaps the finite/discrete side and
requires the opposite local perfectness and left-annihilator equality.

`mapContinuousMonoidHom` needs distinguished-subgroup preservation at
**cofinitely many** coordinates, not necessarily everywhere. The pairing map
and `toPontryaginDual_natural` express contravariance: the coordinate map on
the character-domain restricted product reverses direction under
`PontryaginDual.map`. `pontryaginDualEquiv_natural_apply` requires the stronger
equivalence hypotheses; see `Naturality.lean` for all parameters. The code does
not prove the unrestricted locally compact-coordinate duality theorem.

## Reproducible build

The project pins Lean `v4.34.0-rc2` in `lean-toolchain` and mathlib revision
`e37d88a26f3791ed5a93daa1f949af1021b8d103` in `lakefile.lean` and
`lake-manifest.json`.

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build
LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build RestrictedProductDualityTest
lake env lean -T0 RestrictedProductDualityTest.lean
```

The cache fetch is mandatory and must succeed before a mathlib-dependent
build. Repeat it after changing the Lean or mathlib pins or replacing
`.lake/`. Diagnose and report a cache failure rather than silently falling back
to a mathlib source rebuild.

Generated dependencies and build products under `.lake/` are intentionally
excluded from version control.

Measured baseline (2026-09-25): in a four-CPU-quota, 15 GiB worker, after
`lake clean restricted-product-duality` removed every project build product,
`lake exe cache get` confirmed all 8,892 pinned mathlib artifacts available.
The invocation `LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build` compiled all
twelve mathematical source modules and completed 2,855 Lake jobs in 30 seconds (shell-second
resolution). Dependency artifacts were cached, not rebuilt from source;
peak memory was not measured. These flags did not establish a verified Lake
scheduler or memory bound. This is a baseline, not a speedup claim.

`RestrictedProductDualityTest.lean` is a default-built public-import check:
its private declarations exercise independent index/coordinate universes,
infinite-index nontrivial cyclic duality in both extreme orientations and
the symmetric direction, a nonidentity pointwise adjoint pair, and a cofinite
map which fails subgroup preservation at index zero. The direct-import
`NaturalityClients` now also apply the full square to the nonidentity pair.
The original direct-import `Clients` and `SymmetricClients` still build.
The complete public/native reference and generation recipe are in
[`docs/API.md`](docs/API.md) and [`docs/README.md`](docs/README.md). Neither
certifies private proof bodies or a release.

## Publication lifecycle

Release status is recorded externally against exact commits and trees; a
development-main snapshot is not by itself evidence of an official release.
Changes to documentation and metadata need whole-artifact exact-head independent
review and maintainer acceptance on internal `main`. A separate reviewed
stage-1 snapshot must be promoted to internal `release-prep`, bound to its exact
full commit/tree by an official release record, and consumed at that exact
commit. Distinct stage-2 publication uses a parentless `public-release` history
without internal Forgejo URLs in public objects, separately reviewed complete
artifact/rights evidence and private GitHub consumer checks. A prepared snapshot
or schema-valid metadata alone passes none of those gates. Tags are deferred;
source coverage remains a separate decision.

## Layout

- `RestrictedProductDuality/CompactStage.lean`: finite stages and compact-set
  control.
- `RestrictedProductDuality/SmallArc.lean`: the small-circle-arc annihilation
  lemma.
- `RestrictedProductDuality/Pairing.lean`: finite-support evaluation and the
  algebraic bicharacter.
- `RestrictedProductDuality/TopologicalPairing.lean`: joint continuity, the
  continuous map to `PontryaginDual`, and injectivity.
- `RestrictedProductDuality/CharacterReconstruction.lean`: finite dependence,
  local character reconstruction, surjectivity, explicit compact-open inverse
  continuity, and the bundled topological multiplicative equivalence.
- `RestrictedProductDuality/SymmetricDuality.lean`: left annihilators, the
  transposed opposite-direction equivalence, and its evaluation identity.
- `RestrictedProductDuality/Clients.lean`: empty, finite, and infinite index
  clients.
- `RestrictedProductDuality/SymmetricClients.lean`: empty- and infinite-index
  clients for the symmetric equivalence.
- `RestrictedProductDuality/Naturality.lean`: coordinatewise continuous maps,
  pairing adjointness, and the contravariant duality square.
- `RestrictedProductDuality/NaturalityClients.lean`: arbitrary- and
  infinite-index clients for identity and non-identity adjoint maps.
- `RestrictedProductDuality.lean`: umbrella import.
- `RestrictedProductDualityTest.lean`: separately default-built public-import
  client checks (not imported by the production root).

Every theorem in a proposed revision must be checked transitively with
`#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` are
permitted by the project policy. Passing a build and this foundation check do
not substitute for independent mathematical/API review or maintainer
integration.
