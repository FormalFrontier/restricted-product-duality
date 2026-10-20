# Restricted-product duality

Authors: Formal Frontier Agents. Original Formal Frontier contributions are
offered under Apache-2.0 (see [`LICENSE`](LICENSE)); imported dependency APIs
retain their own authorship and licenses.

Reusable Lean theory of restricted products, ordinary finite-support stages,
path components, homotopy groups and Pontryagin duality.

## Scope

This library provides conditional character reconstruction and duality for
cofinite restricted products over an arbitrary index type. Its theorems do
**not** establish general locally compact-coordinate duality or arithmetic
applications; no source correspondence or coverage is claimed.
The mathematical modules and public-import client checks
are default build targets. The six existing public `Clients` helpers remain
available through the umbrella import; private named tests are not a new
public mathematical API. AI agents developed the Lean code and documentation;
see [`formalization.yaml`](formalization.yaml) for methods and bibliography.

## Headline results

These constructions use mathlib's restricted products, circle-valued
characters and compact-open Pontryagin dual; they do not redefine those APIs.

- **Compact subsets occupy one finite-exceptional stage.** Any compact subset
  of a **T1 cofinite restricted product** lies in one finite-exceptional stage,
  with arbitrary distinguished subsets and arbitrary index type. Only the
  restricted product, not each factor, is required to be T1. The existing
  theorem for **open distinguished subsets** remains available without a T1
  hypothesis. Neither compact stages nor a countable compact exhaustion are
  asserted. [Compact-stage theorems](RestrictedProductDuality/CompactStage.lean).
- **Singleton stages are ordinary products.** For chosen points `b i` and any
  set `F` of free coordinates, restriction is a named homeomorphism from the
  singleton principal stage to the ordinary dependent product over `F`.
  Its inverse inserts `b i` outside `F`; no finiteness or separation is needed.
  Finite insertions embed with range exactly the corresponding cofinite stage,
  and these ordinary finite products detect continuity out of the cofinite
  restricted product. [Principal comparison](RestrictedProductDuality/PrincipalStage.lean).
- **Path components are coordinatewise.** For arbitrary spaces and chosen points,
  the stock path-component quotient of the singleton cofinite restricted product
  is canonically equivalent, as a set, to the cofinite restricted product of the
  factor path-component quotients at their chosen-point classes. Both index and
  factor universes are independent; no separation, local path connectedness,
  finiteness or nonemptiness hypothesis is needed. The inverse chooses points
  only at finitely many exceptional coordinates. This is not a comparison with
  connected components or a statement about positive homotopy groups.
  [Path-component comparison](RestrictedProductDuality/PathComponents.lean).
- **Compact maps factor by finite restriction.** A continuous map from any
  compact space to a **T1 singleton cofinite restricted product** factors
  through an ordinary finite product. The continuous factor is exactly the
  original coordinate function restricted to the chosen finite set.
  [Compact-map factorization](RestrictedProductDuality/FiniteStage.lean).
- **Homotopy groups have finite coordinate support.** For pointed spaces whose
  singleton cofinite restricted product is **T1**, coordinate evaluation gives a
  named multiplicative equivalence with the algebraic restricted product of the
  factor homotopy groups at their bottom subgroups. The cube index is an arbitrary
  nonempty type with decidable equality; neither it nor the factor index need be
  finite. No separation of individual factors is assumed.
  [Homotopy comparison](RestrictedProductDuality/HomotopyGroups.lean).
- **Homotopy comparisons are natural under based coordinate maps.** Continuous
  coordinate maps satisfying every equation `f i (b i) = c i` induce commuting
  squares for both comparisons. The path-component square includes empty index
  types and needs no separation. The positive square uses arbitrary nonempty
  cube-index types with the same decidable equality and requires T1 of both
  restricted products. Based postcomposition has representative, identity and
  composition laws and agrees with Mathlib's fundamental-group map in dimension
  one. [Homotopy naturality](RestrictedProductDuality/HomotopyMaps.lean).
- **Based coordinate homotopies assemble jointly.** For arbitrary factor
  topologies and any possibly empty factor index, continuous coordinate
  `HomotopyRel`s fixed at the chosen source points assemble to
  `pointMapHomotopyRel` between the canonical singleton-cofinite `pointMap`s.
  The `pointMapHomotopyRel_apply` formula holds at every time and coordinate;
  `pointMapHomotopyRel_base` fixes the canonical point throughout. Based-homotopic
  families induce equal path-component maps and equal positive homotopy-group
  homomorphisms for any nonempty cube-index type with its supplied decidable
  equality. No T1, local compactness, countability, CW or local path-connectedness
  hypothesis is needed. [Based homotopies](RestrictedProductDuality/BasedHomotopy.lean).
- **Bottom restricted products are finitely supported coordinates.** For a
  dependent family `G i` of `MulOneClass` factors, the cofinite restricted product
  at the bottom submonoids is multiplicatively equivalent to
  `Multiplicative (DFinsupp (fun i ↦ Additive (G i)))`, preserving every coordinate
  and its nonidentity support set. Index and factor universes are independent,
  and the index may be empty. Bundled evaluation and pointwise family-map
  naturality use `Monoid` factors. For `Group` factors the same comparison applies
  to the bottom-subgroup restricted product with its original pointwise group
  operations. No commutativity or topology is required; this is not a categorical
  coproduct of noncommutative groups.
  [Finite-support coordinates](RestrictedProductDuality/FiniteSupport.lean).
- **Homotopy groups in DFinsupp coordinates.** Composing the singleton homotopy
  comparison above with the algebraic coordinate comparison gives a multiplicative
  equivalence to `Multiplicative (DFinsupp (fun i ↦ Additive (HomotopyGroup N (R i) (b i))))`.
  The factors retain their given topologies and basepoints; the hypothesis is
  **T1 on the original singleton cofinite restricted product**. The cube index
  `N` is arbitrary and nonempty with its given decidable equality, and the cube,
  factor and family-index universes are independent. Coordinate-class evaluation,
  an inverse characterization, uniqueness and class-support formulas use the
  existing homotopy comparison; no factor separation, CW/CGWH, commutativity or
  homotopy-group classification assumption is added.
  [Composite comparison](RestrictedProductDuality/HomotopyGroupsFiniteSupport.lean).
- **Finite-support pairing and continuous dual map.** For commutative
  coordinate groups with circle bicharacters, orthogonality on both
  distinguished subgroups makes coordinatewise evaluation a well-defined,
  multiplicative finite product. Joint local continuity and openness of both
  subgroup families yield a jointly continuous pairing and continuous map
  into the compact-open character group; local separation in the representing
  variable gives injectivity, **not** surjectivity.
  [Pairing](RestrictedProductDuality/Pairing.lean),
  [continuity](docs/API.md#restrictedproductcontinuous_pairing),
  [injectivity](docs/API.md#restrictedproducttopontryagindual_injective).
- **Finite tail dependence and character reconstruction.** A continuous
  global character kills a finite-coordinate tail **of the distinguished
  product**, not necessarily a tail of the full restricted product. Under the
  preceding continuity/openness assumptions, bijectivity of each actual map
  `Y_i → (X_i →* Circle)` onto *all algebraic* circle characters and equality
  of `V_i` with the exact right annihilator of `U_i` reconstruct every global
  continuous character. Separation or bijectivity only for continuous local
  characters is insufficient; finite/discrete coordinates are not required
  for this surjectivity step. [Finite dependence](docs/API.md#restrictedproductexists_producttail_le_ker),
  [local map](docs/API.md#restrictedproductrightcharacter),
  [surjectivity](docs/API.md#restrictedproducttopontryagindual_surjective).
- **Topological equivalences in both orientations.** Finite discrete
  character-domain coordinates `X_i` and topological representing groups
  `Y_i` give inverse continuity and an equivalence with the compact-open
  dual. The transposed direction instead requires finite discrete `Y_i`,
  topological `X_i`, bijectivity of the *left* local character maps and exact
  left annihilators. The evaluation identity uses this transposition, not
  general biduality or an open-mapping theorem.
  [Equivalence](docs/API.md#restrictedproductpontryagindualequiv),
  [opposite direction](docs/API.md#restrictedproductsymmetricpontryagindualequiv).
- **Naturality under adjoint coordinate maps.** Coordinatewise continuous
  homomorphisms preserve restricted products when subgroup preservation holds
  **cofinitely**, even with exceptional failures. For adjoint
  `f : X' → X` and `g : Y → Y'`, the pairing and canonical dual maps form a
  contravariant square. The equivalence-level square additionally requires
  its stronger local-perfectness, exact-annihilator and finite-discrete
  assumptions. [Induced maps](docs/API.md#restrictedproductmapcontinuousmonoidhom),
  [naturality](docs/API.md#restrictedproducttopontryagindual_natural),
  [equivalence square](docs/API.md#restrictedproductpontryagindualequiv_natural_apply).

## Mathematical outline and references

An element of a cofinite restricted product lies in a stage allowing finitely
many coordinates outside their distinguished subsets. Openness makes these
stages an open, directed cover; compactness selects a single containing stage.
Alternatively, under T1 on the restricted product alone, failure of finite
containment would give an infinite sequence with distinct exceptional
coordinates. Every subset of its range has finite, hence closed, preimage in
each principal stage. Finality would make that range closed and discrete,
contradicting compactness. The singleton principal comparison identifies the
free coordinates with an ordinary product and turns containment of a compact
map's range into factorization by finite coordinate restriction.

These are ordinary topological products and Mathlib's restricted-product final
topology, not compactly generated products or a comparison with their colimits.
For homotopy groups, compactness of the cube places each representative in a
finite stage. Coordinate homotopies are assembled only over the union of two
finite representative stages, and finite insertion reconstructs representatives
from finitely supported coordinate classes. Multiplication uses Mathlib's
concatenation convention. No CGWH or CW-complex comparison is asserted.
For path components, two endpoints
already lie in the union of their finite supports. A product of coordinate paths
on that finite set, followed by continuous finite insertion, joins them exactly
when all coordinate endpoints are joined. This argument needs no compact-family
finite-stage theorem or T1 hypothesis.

For a continuous circle character, the centered small-arc kernel lemma then
controls an open product of distinguished subgroups, leaving only finitely
many relevant coordinates **on that product**. Orthogonality makes the
coordinatewise bicharacter evaluation independent of any choice of finite
support for its product.

Restricting a global character to one-coordinate elements produces algebraic
local characters. Bijectivity of the *actual* local maps chooses representing
coordinates; the finite-tail condition together with the exact right
annihilator places those coordinates in the representing restricted product.
Compact-stage control and finite discrete character-domain coordinates supply
the compact-open inverse-continuity tests. Swapping the two groups and using
the left annihilator gives the symmetric construction; pointwise adjointness
then explains the contravariant naturality square. See
[`CharacterReconstruction.lean`](RestrictedProductDuality/CharacterReconstruction.lean),
[`SymmetricDuality.lean`](RestrictedProductDuality/SymmetricDuality.lean) and
[`Naturality.lean`](RestrictedProductDuality/Naturality.lean) for exact assumptions.

**Motivation:** Jürgen Neukirch, Alexander Schmidt and Kay Wingberg,
*Cohomology of Number Fields*, corrected second edition, version 2.3
(May 2020), Proposition (1.1.13), pp. 10–11. This library proves a
finite-coordinate **conditional specialization** only: it neither proves that
general proposition nor the arithmetic inputs of (8.5.2). The formalization
uses mathlib4 at the [pinned revision](lakefile.lean); the bibliography and
scope are also recorded in [`formalization.yaml`](formalization.yaml).
The carrier, final topology and principal inclusions reuse Mathlib's
restricted-product formalization by Anatole Dedecker. The algebraic
finite-support coordinates use Mathlib's dependent finitely supported functions
by Johannes Hölzl and Kenny Lau and additive/multiplicative type tags by Mario
Carneiro. The homotopy-coordinate composite reuses the singleton homotopy
comparison and Mathlib's homotopy groups by Roberto Alvarez. The ordinary
finite-support-product viewpoint is motivated by J. P. May,
*A Concise Course in Algebraic Topology*. The T1 compactness argument above
and the ordinary-product comparisons concern this topological setting, not
compactly generated replacements.

## Public API and hypotheses

Import `RestrictedProductDuality` for the full API, or directly import one of
the modules below. For arbitrary cofinite index types, `cofiniteStage` and
`exists_subset_cofiniteStage_of_t1` control compact subsets when the restricted
product is **T1**. The original `exists_subset_cofiniteStage` instead assumes
that each distinguished set is **open**, without requiring T1.
`singletonPrincipalHomeomorph` provides restriction, inverse-insertion,
coordinate, extensionality and uniqueness formulas for arbitrary free sets.
`singletonFinsetInsert` has embedding, continuity, range and two restriction
identities; `continuous_dom_singleton_iff` expresses finality on ordinary finite
products. `exists_singletonFinsetInsert_factorization` constructs a continuous
finite restriction of a compact map, together with its insertion identity.
`homotopyGroupSingletonHom` descends coordinate evaluation to homotopy classes;
`homotopyGroupSingletonMulEquiv` gives the resulting multiplicative equivalence.
Its representative application formula, inverse characterization and uniqueness
are stated for `HomotopyGroup N`, with arbitrary nonempty cube index `N`.
The usual positive finite degrees specialize this to `N = Fin (n+1)`.
`RestrictedProduct.SingletonPathComponents.canonicalEquiv` compares the stock
`ZerothHomotopy` of `PointProduct b` with the set-valued `ComponentProduct b`.
Its representative and arbitrary-class coordinate formulas, inverse reconstruction,
inverse characterizations, `joined_iff`, existence and uniqueness lemmas allow use
without unfolding quotient descent or choosing representatives.
`GenLoop.map` postcomposes based cube maps for every cube-index type;
`HomotopyGroup.map` bundles the induced homomorphism for any nonempty cube index.
The latter's `map_class`, `map_id`, `map_comp` and
`pi1MulEquivFundamentalGroup_map` give its characteristic computations.
In `RestrictedProduct.SingletonNaturality`, `pointMap`, `pathMap`, `componentMap`
and `homotopyTupleMap` name the stock continuous, quotient and restricted-product
arrows, with evaluation and identity/composition formulas.
`canonicalEquiv_naturality` and `homotopyGroupSingletonMulEquiv_naturality`
express the two comparison squares. No map needs factorwise T1; the positive
square has precisely the two restricted-product T1 assumptions of its comparisons.
`Subgroup.le_ker_of_mapsTo_centeredArc` supplies the small-arc
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

## Using the library

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "restricted-product-duality"
git = "https://github.com/FormalFrontier/restricted-product-duality.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves it when you add or
update the dependency; `lake-manifest.json` keeps the resolved commit until you
update again. Replace `main` with a release commit to pin explicitly.

```lean
import RestrictedProductDuality
```

## Reproducible build

The project pins Lean `v4.34.0-rc2` in `lean-toolchain` and mathlib revision
`e37d88a26f3791ed5a93daa1f949af1021b8d103` in `lakefile.lean` and
`lake-manifest.json`.

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build
```

The cache fetch is mandatory and must succeed before a mathlib-dependent
build. Repeat it after changing the Lean or mathlib pins or replacing
`.lake/`. Diagnose and report a cache failure rather than silently falling back
to a mathlib source rebuild.

Generated dependencies and build products under `.lake/` are intentionally
excluded from version control.

Historical cached baseline: in a four-CPU-quota, 15 GiB worker, after
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
map which fails subgroup preservation at index zero. Its canonical circle
example has nonopen singleton basepoints and a nonconstant compact
single-coordinate range; it applies both T1 compact containment and compact-map
factorization through exact finite restriction. The same single-coordinate
once-around Circle representative also exercises the homotopy comparison: its
image is the bottom-subgroup tuple with identity coordinates outside `{0}`
and the Circle loop class at zero. This equation does not assert a
classification of Circle homotopy classes. A Nat-indexed discrete-Bool example
computes the full path-class tuple of the point which is true only at zero, with a
separate nonvacuity proof distinguishing the Bool path classes. The same Circle
representative also exercises the coordinatewise square map
`z ↦ z^2`, and Bool negation changes the default from false to true. In each case
both routes compute an explicit whole target tuple. No nonidentity positive
homotopy class is inferred from these space maps. The direct-import
`NaturalityClients` also apply the full square to the nonidentity pair.
The direct-import `Clients` and `SymmetricClients` are included in the
production build. Direct `lean -T0` checks are optional, not another required
build of the default test target.
A historical, pinned duality public/native reference is in
[`docs/API.md`](docs/API.md), with a separate fixed-public-revision reproduction
recipe in [`docs/README.md`](docs/README.md). It is not a current whole-library
inventory and omits the later principal/finite-stage API; neither document
certifies private proof bodies.

## Layout

| Finite-support module | Contents |
| --- | --- |
| [`FiniteSupport`](RestrictedProductDuality/FiniteSupport.lean) | Bottom-submonoid coordinates at `MulOneClass`, bundled evaluation and family maps at `Monoid`, and direct use for bottom-subgroup products at `Group`. |
| [`HomotopyGroupsFiniteSupport`](RestrictedProductDuality/HomotopyGroupsFiniteSupport.lean) | Composition of the singleton homotopy comparison with finite-support coordinates, for arbitrary nonempty cube index with decidable equality and T1 on the original singleton cofinite restricted product. |

- `RestrictedProductDuality/CompactStage.lean`: finite stages and compact-set
  control, either for open distinguished subsets or under T1 on the restricted
  product.
- `RestrictedProductDuality/PrincipalStage.lean`: arbitrary-set singleton
  principal homeomorphism, finite insertion embeddings and ordinary-product
  finality.
- `RestrictedProductDuality/PathComponents.lean`: singleton cofinite path-component
  equivalence, coordinate formulas, finite inverse reconstruction and uniqueness.
- `RestrictedProductDuality/FiniteStage.lean`: compact-map factorization by
  ordinary finite coordinate restriction.
- `RestrictedProductDuality/HomotopyGroups.lean`: coordinate homomorphism and
  multiplicative comparison for homotopy groups of T1 singleton cofinite
  restricted products, with representative and inverse characterizations.
- `RestrictedProductDuality/HomotopyMaps.lean`: based postcomposition, its
  fundamental-group compatibility and both coordinate-comparison naturality squares.
- `RestrictedProductDuality/BasedHomotopy.lean`: joint coordinatewise based
  homotopies, all-time coordinate and basepoint formulas, and invariance of the
  induced path-component and positive homotopy-group maps.
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
