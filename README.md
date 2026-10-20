# Restricted-product duality

Reusable Lean theory of cofinite restricted products: ordinary finite-support
stages, path components, homotopy groups and conditional Pontryagin duality.
The library uses Mathlib's restricted products, circle characters and
compact-open dual, rather than redefining them. The [mathematical guide](docs/mathematical-guide.md)
contains the detailed statements, API formulas, examples and proof outlines.

## Headline results

- **Compact containment and finite factorization.** Every compact subset of a
  **T1 restricted product** lies in one finite-exceptional stage, for arbitrary
  distinguished subsets and index type; only the original restricted product,
  not the factors, must be T1. The open-distinguished-subset theorem instead
  needs openness, not T1. Continuous maps from compact spaces to a T1 singleton
  cofinite product factor by ordinary finite coordinate restriction. No compact
  stages or countable exhaustion are asserted.
  [Containment](RestrictedProductDuality/CompactStage.lean),
  [factorization](RestrictedProductDuality/FiniteStage.lean).
- **Ordinary singleton stages and coordinatewise path components.** Restriction
  identifies a singleton principal stage on any free set with its ordinary Pi
  product; the inverse inserts the chosen points elsewhere. Finite insertions
  embed and detect continuity out of the singleton cofinite product.
  Its stock path-component quotient is canonically equivalent **as a set** to
  the cofinite product of the factor path-component quotients, with finite
  inverse reconstruction; no separation or connected-component assertion.
  [Stages](RestrictedProductDuality/PrincipalStage.lean),
  [path components](RestrictedProductDuality/PathComponents.lean).
- **Factorwise connectivity and quotient maps.** For a given family `b i`,
  `PointProduct b` is path connected iff every factor is path connected, and
  locally path connected iff every factor is locally path connected (no path
  connectedness is needed for the latter); forward instances are provided.
  Raw coordinate evaluation and the **whole** insertion map from the
  topological sum `Σ s : Finset ι, ∀ j : s, X j` are quotient maps. Individual
  finite insertions are embeddings, not generally surjective.
  [Connectivity](RestrictedProductDuality/Connectivity.lean).
- **Positive homotopy groups have finite support.** For a **T1 original
  singleton cofinite restricted product**, coordinate evaluation gives a
  multiplicative equivalence with the bottom-subgroup restricted product of
  the factor homotopy groups, hence with
  `Multiplicative (DFinsupp (fun i ↦ Additive (HomotopyGroup N (R i) (b i))))`.
  The cube index `N` is arbitrary nonempty with decidable equality, not
  necessarily finite; no factor T1, CW/CGWH or classification assumption.
  [Comparison](RestrictedProductDuality/HomotopyGroups.lean),
  [DFinsupp composite](RestrictedProductDuality/HomotopyGroupsFiniteSupport.lean).
- **Based naturality and joint homotopies.** Continuous coordinate maps preserving every
  chosen point give both comparison squares. The path-component square needs
  no separation; the positive square requires T1 of **both** original products.
  Based postcomposition, its homomorphisms and coordinate `HomotopyRel`s
  assembling jointly need no T1; based-homotopic families induce equal maps.
  [Naturality](RestrictedProductDuality/HomotopyMaps.lean),
  [joint homotopies](RestrictedProductDuality/BasedHomotopy.lean).
- **Based coordinate equivalences and contractions.** Homeomorphisms carrying
  each `b i` to `c i` give product homeomorphisms. Based continuous `f i`, `g i`
  with both inverse homotopies relative to `{b i}`, `{c i}` give product
  homotopy equivalences. Chosen factor homotopies `id → const (b i)` fixing
  `b i` give a contraction and `ContractibleSpace`; mere unbased factor
  contractibility is not the input. None requires separation or finite index.
  [Homeomorphisms](RestrictedProductDuality/BasedHomeomorphisms.lean),
  [homotopy equivalences](RestrictedProductDuality/HomotopyEquivalences.lean),
  [contractions](RestrictedProductDuality/Contractibility.lean).
- **Algebraic finite-support coordinates.** At bottom submonoids, `MulOneClass`
  factors give a multiplicative equivalence with `Multiplicative (DFinsupp
  (fun i ↦ Additive (G i)))`. Bundled evaluation and family maps use `Monoid`;
  bottom-subgroup products use `Group`. No topology or commutativity is needed;
  this is not a noncommutative categorical coproduct.
  [Finite support](RestrictedProductDuality/FiniteSupport.lean).
- **Conditional character reconstruction and duality.** For commutative groups,
  local circle bicharacters and orthogonality on both distinguished subgroups
  give a finite-product pairing. Joint local continuity and **both** subgroup
  families open give a jointly continuous pairing and continuous dual map;
  local separation gives injectivity, **not** surjectivity. A global continuous
  character kills a finite-coordinate tail **of the distinguished product**.
  Reconstruction requires bijective actual right local maps onto **all
  algebraic** circle characters and exact right annihilator `= V`, not merely
  continuous-character perfectness or nondegeneracy. Topological equivalence
  additionally needs finite discrete character-domain `X i` and topological
  representing `Y i`. Transposition requires finite discrete `Y i`, topological
  `X i`, left local perfectness and exact left annihilator; this is not general
  biduality or open mapping.
  [Pairing](RestrictedProductDuality/Pairing.lean),
  [continuity](RestrictedProductDuality/TopologicalPairing.lean),
  [reconstruction](RestrictedProductDuality/CharacterReconstruction.lean),
  [transpose](RestrictedProductDuality/SymmetricDuality.lean).
- **Contravariant duality naturality.** Adjoint continuous coordinate
  homomorphisms give the pairing/dual-map square with subgroup preservation
  only **cofinitely** (exceptional failures allowed). The equivalence square
  retains its stronger local-perfectness, exact-annihilator and finite-discrete
  assumptions. [Naturality](RestrictedProductDuality/Naturality.lean).

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

The [public-import examples](docs/mathematical-guide.md#examples-and-public-import-clients)
include Circle coordinate loops, discrete Bool path classes, and based real
maps. These compute points and coordinate classes, not a Circle homotopy-group
classification or a nonidentity positive class inferred from a space map.

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
to a mathlib source rebuild. Generated dependencies and build products under
`.lake/` are intentionally excluded from version control.

Both mathematical modules and public-import clients are default build targets.
`RestrictedProductDualityTest` is separately default-built, not imported by the
production root; direct-import `Clients`, `SymmetricClients` and
`NaturalityClients` are also built. The six existing public `Clients` helpers
remain available through the umbrella import; private tests are not new public
mathematical API. See the guide for the examples and optional direct checks.

## Public API and hypotheses

Import the umbrella above or an individual module in the table below. The
[full API outline](docs/mathematical-guide.md#public-api-and-hypotheses) gives
named constructions, computation rules, inverse characterizations and uniqueness
lemmas. The [pinned duality reference](docs/API.md) is an older, narrow snapshot,
not a current whole-library inventory; its [reproduction recipe](docs/README.md)
is for a fixed public revision and omits later principal/finite-stage API.

## Contents

| Module | Contents |
| --- | --- |
| [`FiniteSupport`](RestrictedProductDuality/FiniteSupport.lean) | Bottom-submonoid coordinates at `MulOneClass`, bundled evaluation and family maps at `Monoid`, and direct use for bottom-subgroup products at `Group`. |
| [`HomotopyGroupsFiniteSupport`](RestrictedProductDuality/HomotopyGroupsFiniteSupport.lean) | Composition of the singleton homotopy comparison with finite-support coordinates, for arbitrary nonempty cube index with decidable equality and T1 on the original singleton cofinite restricted product. |
| [`RestrictedProductDuality.CompactStage`](RestrictedProductDuality/CompactStage.lean) | finite stages and compact-set control, either for open distinguished subsets or under T1 on the restricted product. |
| [`RestrictedProductDuality.PrincipalStage`](RestrictedProductDuality/PrincipalStage.lean) | arbitrary-set singleton principal homeomorphism, finite insertion embeddings and ordinary-product finality. |
| [`RestrictedProductDuality.PathComponents`](RestrictedProductDuality/PathComponents.lean) | singleton cofinite path-component equivalence, coordinate formulas, finite inverse reconstruction and uniqueness. |
| [`RestrictedProductDuality.Connectivity`](RestrictedProductDuality/Connectivity.lean) | quotient coordinate evaluations and whole finite-stage-sum insertion map, factorwise path-connectedness and local-path-connectedness characterizations, and their forward instances. |
| [`RestrictedProductDuality.FiniteStage`](RestrictedProductDuality/FiniteStage.lean) | compact-map factorization by ordinary finite coordinate restriction. |
| [`RestrictedProductDuality.HomotopyGroups`](RestrictedProductDuality/HomotopyGroups.lean) | coordinate homomorphism and multiplicative comparison for homotopy groups of T1 singleton cofinite restricted products, with representative and inverse characterizations. |
| [`RestrictedProductDuality.HomotopyMaps`](RestrictedProductDuality/HomotopyMaps.lean) | based postcomposition, its fundamental-group compatibility and both coordinate-comparison naturality squares. |
| [`RestrictedProductDuality.BasedHomotopy`](RestrictedProductDuality/BasedHomotopy.lean) | joint coordinatewise based homotopies, all-time coordinate and basepoint formulas, and invariance of the induced path-component and positive homotopy-group maps. |
| [`RestrictedProductDuality.BasedHomeomorphisms`](RestrictedProductDuality/BasedHomeomorphisms.lean) | based coordinate homeomorphisms of singleton cofinite products, with forward/inverse continuous-map, coordinate and canonical-point formulas. |
| [`RestrictedProductDuality.Contractibility`](RestrictedProductDuality/Contractibility.lean) | contraction fixing the canonical point from chosen based coordinate contractions, its coordinate formula and the resulting `ContractibleSpace` corollary. |
| [`RestrictedProductDuality.HomotopyEquivalences`](RestrictedProductDuality/HomotopyEquivalences.lean) | homotopy equivalences from based coordinate maps and relative inverse homotopies, with forward, inverse, coordinate and chosen-point formulas for arbitrary factor topologies. |
| [`RestrictedProductDuality.SmallArc`](RestrictedProductDuality/SmallArc.lean) | the small-circle-arc annihilation lemma. |
| [`RestrictedProductDuality.Pairing`](RestrictedProductDuality/Pairing.lean) | finite-support evaluation and the algebraic bicharacter. |
| [`RestrictedProductDuality.TopologicalPairing`](RestrictedProductDuality/TopologicalPairing.lean) | joint continuity, the continuous map to `PontryaginDual`, and injectivity. |
| [`RestrictedProductDuality.CharacterReconstruction`](RestrictedProductDuality/CharacterReconstruction.lean) | finite dependence, local character reconstruction, surjectivity, explicit compact-open inverse continuity, and the bundled topological multiplicative equivalence. |
| [`RestrictedProductDuality.SymmetricDuality`](RestrictedProductDuality/SymmetricDuality.lean) | left annihilators, the transposed opposite-direction equivalence, and its evaluation identity. |
| [`RestrictedProductDuality.Clients`](RestrictedProductDuality/Clients.lean) | empty, finite, and infinite index clients. |
| [`RestrictedProductDuality.SymmetricClients`](RestrictedProductDuality/SymmetricClients.lean) | empty- and infinite-index clients for the symmetric equivalence. |
| [`RestrictedProductDuality.Naturality`](RestrictedProductDuality/Naturality.lean) | coordinatewise continuous maps, pairing adjointness, and the contravariant duality square. |
| [`RestrictedProductDuality.NaturalityClients`](RestrictedProductDuality/NaturalityClients.lean) | arbitrary- and infinite-index clients for identity and non-identity adjoint maps. |
| [`RestrictedProductDuality`](RestrictedProductDuality.lean) | umbrella import. |
| [`RestrictedProductDualityTest`](RestrictedProductDualityTest.lean) | separately default-built public-import client checks (not imported by the production root). |
| [`RestrictedProductDualityTest.BasedHomeomorphisms`](RestrictedProductDualityTest/BasedHomeomorphisms.lean) | Real doubling/halving homeomorphism, coordinate formulas and empty-index example. |
| [`RestrictedProductDualityTest.BasedHomotopy`](RestrictedProductDualityTest/BasedHomotopy.lean) | Real straight-line based homotopy from identity to doubling and its coordinate formulas. |
| [`RestrictedProductDualityTest.Contractibility`](RestrictedProductDualityTest/Contractibility.lean) | Based real contractions, empty-index cases, and path/local-path-connectedness examples. |
| [`RestrictedProductDualityTest.FiniteSupport`](RestrictedProductDualityTest/FiniteSupport.lean) | Independently constructed sparse integer coordinates and empty-index comparison. |
| [`RestrictedProductDualityTest.HomotopyEquivalences`](RestrictedProductDualityTest/HomotopyEquivalences.lean) | Based doubling/halving homotopy equivalence on real families and the empty index. |

## Conventions and limitations

`PointProduct b` has its **original singleton-cofinite final finite-stage
topology**, with ordinary finite Pi stages, not the subspace topology of an
infinite Pi product or a CGWH/CW replacement. The singleton constructions use
arbitrary given points and independent index/factor universes; the index may be
empty. No separation, local compactness, countability or connectivity is added
unless explicitly stated above. For positive comparisons, the cube index is
nonempty and the original products are T1; no factor T1 is imposed.

Path components are the quotient by paths, not connected components.
Homotopy-group multiplication uses Mathlib's concatenation convention. No
unrestricted locally compact-coordinate duality or arithmetic application is
proved. All headline constructions above are implemented; the guide separates
their hypotheses and the stated consequences from these unsupported extensions.

## References

- Jürgen Neukirch, Alexander Schmidt and Kay Wingberg, *Cohomology of Number
  Fields*, corrected second edition, version 2.3 (May 2020), Proposition
  (1.1.13), pp. 10–11: motivation for a **finite-coordinate conditional
  specialization**, not a proof of that general proposition or arithmetic (8.5.2).
- J. P. May, *A Concise Course in Algebraic Topology*: motivation for ordinary
  finite-support products, not a formalized inventory of the book.
- [Pinned Mathlib and bibliography](formalization.yaml);
  [detailed mathematical outline and credits](docs/mathematical-guide.md#mathematical-outline-and-references).

## Credits and license

Authors: Formal Frontier Agents. AI agents developed the Lean code and
documentation. Mathlib credit: Anatole Dedecker (restricted products), Johannes
Hölzl and Kenny Lau (DFinsupp), Mario Carneiro (type tags), Roberto Alvarez
(homotopy groups), Shing Tak Lam (homotopy equivalences and relative homotopies),
Patrick Massot, Ben Eltschig and subsequent contributors (connectivity).
[Methods and further attribution](formalization.yaml) and the guide describe the
reused APIs. Original Formal Frontier contributions are Apache-2.0 (see
[`LICENSE`](LICENSE)); dependencies retain their own authorship and licenses.
