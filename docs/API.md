# Native API reference

Fixed Lean `v4.34.0-rc2`, mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`
and separately pinned doc-gen4 `97d4ecdfc8e09e7f511724c25e303d448de6a3db`. These are the full
displayed signatures, including implicit parameters and independent universes,
of **all 74 entries in the native declarations tables for all 12 shipped modules**.
All twelve native instance tables have zero rows. Two named `local instance`s
in `NaturalityClients` occur in the native declarations table as `def` and
`theorem`, not as instance-table rows; the local instance attribute is not
asserted to be exported. The `Subgroup` lemma is retained across namespaces.
This public/native filtered reference is not a census of private or
compiler-generated proofs and does not certify axioms, source coverage
or rights. [Reproduce and assess provenance](README.md).

Source links target only the unchanged `.lean` files shipped here.
**Native source docstring** matches an original Lean comment;
**Original catalogue explanation** is newly written here for an
entry without a source docstring, not a fabricated Lean docstring.

## Native module inventory

| Shipped module | Definitions | Theorems | Native instance-table rows |
| --- | ---: | ---: | ---: |
| [`RestrictedProductDuality.CompactStage`](../RestrictedProductDuality/CompactStage.lean) | 2 | 5 | 0 |
| [`RestrictedProductDuality.SmallArc`](../RestrictedProductDuality/SmallArc.lean) | 0 | 1 | 0 |
| [`RestrictedProductDuality.Pairing`](../RestrictedProductDuality/Pairing.lean) | 3 | 10 | 0 |
| [`RestrictedProductDuality.TopologicalPairing`](../RestrictedProductDuality/TopologicalPairing.lean) | 2 | 4 | 0 |
| [`RestrictedProductDuality.CharacterReconstruction`](../RestrictedProductDuality/CharacterReconstruction.lean) | 10 | 16 | 0 |
| [`RestrictedProductDuality.SymmetricDuality`](../RestrictedProductDuality/SymmetricDuality.lean) | 2 | 6 | 0 |
| [`RestrictedProductDuality.Naturality`](../RestrictedProductDuality/Naturality.lean) | 1 | 4 | 0 |
| [`RestrictedProductDuality`](../RestrictedProductDuality.lean) | 0 | 0 | 0 |
| [`RestrictedProductDuality.Clients`](../RestrictedProductDuality/Clients.lean) | 2 | 4 | 0 |
| [`RestrictedProductDuality.SymmetricClients`](../RestrictedProductDuality/SymmetricClients.lean) | 0 | 0 | 0 |
| [`RestrictedProductDuality.NaturalityClients`](../RestrictedProductDuality/NaturalityClients.lean) | 1 | 1 | 0 |
| [`RestrictedProductDualityTest`](../RestrictedProductDualityTest.lean) | 0 | 0 | 0 |

## Production API (66 native entries)

### RestrictedProduct.cofiniteStage

Kind: `def`.

```lean
def RestrictedProduct.cofiniteStage {ι : Type u_1} {R : ι → Type u_2} {A : (i : ι) → Set (R i)} (s : Finset ι) : Set (RestrictedProduct (fun (i : ι) => R i) (fun (i : ι) => A i) Filter.cofinite)
```

**Native source docstring:** The cofinite stage on which coordinates outside `s` lie in the distinguished subsets.

[Source](../RestrictedProductDuality/CompactStage.lean#L27) (native source start line).

### RestrictedProduct.mem_cofiniteStage

Kind: `theorem`.

```lean
theorem RestrictedProduct.mem_cofiniteStage {ι : Type u_1} {R : ι → Type u_2} {A : (i : ι) → Set (R i)} {s : Finset ι} {x : RestrictedProduct (fun (i : ι) => R i) (fun (i : ι) => A i) Filter.cofinite} : x ∈ cofiniteStage s ↔ ∀ i ∉ s, x i ∈ A i
```

**Original catalogue explanation (not a Lean docstring):** Membership in a cofinite stage means every coordinate outside its finite exceptional set lies in the distinguished subset.

[Source](../RestrictedProductDuality/CompactStage.lean#L31) (native source start line).

### RestrictedProduct.cofiniteStage_mono

Kind: `theorem`.

```lean
theorem RestrictedProduct.cofiniteStage_mono {ι : Type u_1} {R : ι → Type u_2} {A : (i : ι) → Set (R i)} {s t : Finset ι} (hst : s ⊆ t) : cofiniteStage s ⊆ cofiniteStage t
```

**Native source docstring:** Cofinite stages grow when their finite exceptional sets grow.

[Source](../RestrictedProductDuality/CompactStage.lean#L36) (native source start line).

### RestrictedProduct.exceptionalFinset

Kind: `def`.

```lean
noncomputable def RestrictedProduct.exceptionalFinset {ι : Type u_1} {R : ι → Type u_2} {A : (i : ι) → Set (R i)} (x : RestrictedProduct (fun (i : ι) => R i) (fun (i : ι) => A i) Filter.cofinite) : Finset ι
```

**Native source docstring:** A canonical finite exceptional set for an element of a cofinite restricted product.

[Source](../RestrictedProductDuality/CompactStage.lean#L42) (native source start line).

### RestrictedProduct.mem_cofiniteStage_exceptionalFinset

Kind: `theorem`.

```lean
theorem RestrictedProduct.mem_cofiniteStage_exceptionalFinset {ι : Type u_1} {R : ι → Type u_2} {A : (i : ι) → Set (R i)} (x : RestrictedProduct (fun (i : ι) => R i) (fun (i : ι) => A i) Filter.cofinite) : x ∈ cofiniteStage x.exceptionalFinset
```

**Original catalogue explanation (not a Lean docstring):** Each restricted-product element belongs to the stage cut out by its own finite exceptional-coordinate set.

[Source](../RestrictedProductDuality/CompactStage.lean#L46) (native source start line).

### RestrictedProduct.isOpen_cofiniteStage

Kind: `theorem`.

```lean
theorem RestrictedProduct.isOpen_cofiniteStage {ι : Type u_1} {R : ι → Type u_2} {A : (i : ι) → Set (R i)} [(i : ι) → TopologicalSpace (R i)] (hAopen : ∀ (i : ι), IsOpen (A i)) (s : Finset ι) : IsOpen (cofiniteStage s)
```

**Native source docstring:** A cofinite stage is open when all distinguished subsets are open.

[Source](../RestrictedProductDuality/CompactStage.lean#L57) (native source start line).

### RestrictedProduct.exists_subset_cofiniteStage

Kind: `theorem`.

```lean
theorem RestrictedProduct.exists_subset_cofiniteStage {ι : Type u_1} {R : ι → Type u_2} {A : (i : ι) → Set (R i)} [(i : ι) → TopologicalSpace (R i)] (hAopen : ∀ (i : ι), IsOpen (A i)) {K : Set (RestrictedProduct (fun (i : ι) => R i) (fun (i : ι) => A i) Filter.cofinite)} (hK : IsCompact K) : ∃ (s : Finset ι), K ⊆ cofiniteStage s
```

**Native source docstring:** Every compact subset of a cofinite restricted product lies in one finite stage.

The index type is arbitrary. The proof uses the directed open cover by cofinite stages, so it
does not require a countable exhaustion or a sigma-compactness assumption.

[Source](../RestrictedProductDuality/CompactStage.lean#L63) (native source start line).

### Subgroup.le_ker_of_mapsTo_centeredArc

Kind: `theorem`.

```lean
theorem Subgroup.le_ker_of_mapsTo_centeredArc {G : Type u_1} [Group G] (S : Subgroup G) (f : G →* Circle) (hf : Set.MapsTo (⇑f) (↑S) (Circle.centeredArc (Real.pi / 2))) : S ≤ f.ker
```

**Native source docstring:** A subgroup whose image under a circle-valued homomorphism lies in the centered `π / 2` arc
is contained in the homomorphism's kernel.

[Source](../RestrictedProductDuality/SmallArc.lean#L27) (native source start line).

### RestrictedProduct.pairing_hasFiniteMulSupport

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_hasFiniteMulSupport {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : Function.HasFiniteMulSupport fun (i : ι) => ((e i) (x i)) (y i)
```

**Native source docstring:** Orthogonality of the distinguished subgroups makes every restricted-product evaluation
family finitely supported.

[Source](../RestrictedProductDuality/Pairing.lean#L33) (native source start line).

### RestrictedProduct.pairing

Kind: `def`.

```lean
noncomputable def RestrictedProduct.pairing {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : Circle
```

**Native source docstring:** The product pairing induced on two cofinite restricted products.

The `finprod` agrees with the ordinary product over any finite set containing all coordinates
where the local factor is not `1`.

[Source](../RestrictedProductDuality/Pairing.lean#L42) (native source start line).

### RestrictedProduct.pairing_eq_prod

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_eq_prod {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) (s : Finset ι) (hs : ∀ i ∉ s, ((e i) (x i)) (y i) = 1) : pairing U V e x y = ∏ i ∈ s, ((e i) (x i)) (y i)
```

**Native source docstring:** Evaluation is the ordinary product over any finite set outside which all local factors are
`1`. In particular, its value is independent of a chosen finite exceptional presentation.

[Source](../RestrictedProductDuality/Pairing.lean#L50) (native source start line).

### RestrictedProduct.pairing_mulSingle_left

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_mulSingle_left {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (i : ι) (x : X i) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : pairing U V e (mulSingle U i x) y = ((e i) x) (y i)
```

**Original catalogue explanation (not a Lean docstring):** A single nontrivial character-domain coordinate evaluates the global pairing by its corresponding local bicharacter.

[Source](../RestrictedProductDuality/Pairing.lean#L62) (native source start line).

### RestrictedProduct.pairing_mulSingle_right

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_mulSingle_right {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (i : ι) (y : Y i) : pairing U V e x (mulSingle V i y) = ((e i) (x i)) y
```

**Original catalogue explanation (not a Lean docstring):** A single representing coordinate evaluates the global pairing by the corresponding local bicharacter.

[Source](../RestrictedProductDuality/Pairing.lean#L73) (native source start line).

### RestrictedProduct.pairing_one_left

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_one_left {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : pairing U V e 1 y = 1
```

**Original catalogue explanation (not a Lean docstring):** The global pairing is one when its first argument is the identity.

[Source](../RestrictedProductDuality/Pairing.lean#L83) (native source start line).

### RestrictedProduct.pairing_one_right

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_one_right {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) : pairing U V e x 1 = 1
```

**Original catalogue explanation (not a Lean docstring):** The global pairing is one when its second argument is the identity.

[Source](../RestrictedProductDuality/Pairing.lean#L88) (native source start line).

### RestrictedProduct.pairing_mul_left

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_mul_left {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (x x' : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : pairing U V e (x * x') y = pairing U V e x y * pairing U V e x' y
```

**Original catalogue explanation (not a Lean docstring):** The global pairing multiplies pointwise under multiplication in its first argument.

[Source](../RestrictedProductDuality/Pairing.lean#L93) (native source start line).

### RestrictedProduct.pairing_mul_right

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_mul_right {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (y y' : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : pairing U V e x (y * y') = pairing U V e x y * pairing U V e x y'
```

**Original catalogue explanation (not a Lean docstring):** The global pairing multiplies pointwise under multiplication in its second argument.

[Source](../RestrictedProductDuality/Pairing.lean#L101) (native source start line).

### RestrictedProduct.pairingMonoidHom

Kind: `def`.

```lean
noncomputable def RestrictedProduct.pairingMonoidHom {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite →* Circle
```

**Native source docstring:** The character of the first restricted product determined by an element of the second one.

[Source](../RestrictedProductDuality/Pairing.lean#L109) (native source start line).

### RestrictedProduct.pairingMonoidHom_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairingMonoidHom_apply {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) : (pairingMonoidHom U V e horth y) x = pairing U V e x y
```

**Original catalogue explanation (not a Lean docstring):** Evaluating the pairing monoid homomorphism at a first-product element yields the global pairing with its fixed second-product element.

[Source](../RestrictedProductDuality/Pairing.lean#L117) (native source start line).

### RestrictedProduct.pairingHom

Kind: `def`.

```lean
noncomputable def RestrictedProduct.pairingHom {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite →* RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite →* Circle
```

**Native source docstring:** The global pairing, bundled as a homomorphism into the algebraic character group.

[Source](../RestrictedProductDuality/Pairing.lean#L124) (native source start line).

### RestrictedProduct.pairingHom_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairingHom_apply {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) : ((pairingHom U V e horth) y) x = pairing U V e x y
```

**Original catalogue explanation (not a Lean docstring):** The curried pairing homomorphism evaluates to the underlying global bicharacter at both arguments.

[Source](../RestrictedProductDuality/Pairing.lean#L132) (native source start line).

### RestrictedProduct.continuous_pairing

Kind: `theorem`.

```lean
theorem RestrictedProduct.continuous_pairing {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) : Continuous fun (p : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite × RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) => pairing U V e p.1 p.2
```

**Native source docstring:** The pairing induced by jointly continuous local bicharacters is jointly continuous on the two
cofinite restricted products.

[Source](../RestrictedProductDuality/TopologicalPairing.lean#L33) (native source start line).

### RestrictedProduct.pairingCharacter

Kind: `def`.

```lean
noncomputable def RestrictedProduct.pairingCharacter {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)
```

**Native source docstring:** The continuous character of the first restricted product determined by an element of the
second restricted product.

[Source](../RestrictedProductDuality/TopologicalPairing.lean#L62) (native source start line).

### RestrictedProduct.pairingCharacter_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairingCharacter_apply {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) : (pairingCharacter U V e horth hUopen hVopen he y) x = pairing U V e x y
```

**Original catalogue explanation (not a Lean docstring):** Evaluation of the constructed continuous character at a first-product element is the global pairing.

[Source](../RestrictedProductDuality/TopologicalPairing.lean#L72) (native source start line).

### RestrictedProduct.toPontryaginDual

Kind: `def`.

```lean
noncomputable def RestrictedProduct.toPontryaginDual {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite →ₜ* PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)
```

**Native source docstring:** The canonical continuous homomorphism from the second restricted product to the Pontryagin
dual of the first. This construction assumes orthogonality and continuity, but not perfectness or
exact-annihilator hypotheses.

[Source](../RestrictedProductDuality/TopologicalPairing.lean#L81) (native source start line).

### RestrictedProduct.toPontryaginDual_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.toPontryaginDual_apply {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) : ((toPontryaginDual U V e horth hUopen hVopen he) y) x = pairing U V e x y
```

**Original catalogue explanation (not a Lean docstring):** Evaluating the canonical continuous dual map on a representing element and a character-domain element gives the global pairing.

[Source](../RestrictedProductDuality/TopologicalPairing.lean#L98) (native source start line).

### RestrictedProduct.toPontryaginDual_injective

Kind: `theorem`.

```lean
theorem RestrictedProduct.toPontryaginDual_injective {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hsep : ∀ (i : ι) (y y' : Y i), (∀ (x : X i), ((e i) x) y = ((e i) x) y') → y = y') : Function.Injective ⇑(toPontryaginDual U V e horth hUopen hVopen he)
```

**Native source docstring:** Local separation in the second variable makes the canonical map to the Pontryagin dual
injective.

[Source](../RestrictedProductDuality/TopologicalPairing.lean#L108) (native source start line).

### RestrictedProduct.rightCharacter

Kind: `def`.

```lean
noncomputable def RestrictedProduct.rightCharacter {X : Type u_4} {Y : Type u_5} [CommGroup X] [CommGroup Y] (e : X →* Y →* Circle) : Y →* X →* Circle
```

**Native source docstring:** The character of `X` represented by `y` through a multiplicative bicharacter.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L34) (native source start line).

### RestrictedProduct.rightCharacter_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.rightCharacter_apply {X : Type u_4} {Y : Type u_5} [CommGroup X] [CommGroup Y] (e : X →* Y →* Circle) (y : Y) (x : X) : ((rightCharacter e) y) x = (e x) y
```

**Original catalogue explanation (not a Lean docstring):** A local right character evaluated on the left group element is the original local bicharacter value.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L44) (native source start line).

### RestrictedProduct.rightAnnihilator

Kind: `def`.

```lean
def RestrictedProduct.rightAnnihilator {X : Type u_4} {Y : Type u_5} [CommGroup X] [CommGroup Y] (U : Subgroup X) (e : X →* Y →* Circle) : Subgroup Y
```

**Native source docstring:** The right annihilator of a subgroup under a multiplicative bicharacter.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L50) (native source start line).

### RestrictedProduct.mem_rightAnnihilator

Kind: `theorem`.

```lean
theorem RestrictedProduct.mem_rightAnnihilator {X : Type u_4} {Y : Type u_5} [CommGroup X] [CommGroup Y] {U : Subgroup X} {e : X →* Y →* Circle} {y : Y} : y ∈ rightAnnihilator U e ↔ ∀ x ∈ U, (e x) y = 1
```

**Original catalogue explanation (not a Lean docstring):** Membership in the right annihilator is equivalent to pairing to one with every element of the chosen left subgroup.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L58) (native source start line).

### RestrictedProduct.structureMapMonoidHom

Kind: `def`.

```lean
def RestrictedProduct.structureMapMonoidHom {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) : ((i : ι) → ↥(U i)) →* RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite
```

**Native source docstring:** The distinguished product, bundled as a homomorphism into the cofinite restricted product.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L64) (native source start line).

### RestrictedProduct.structureMapMonoidHom_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.structureMapMonoidHom_apply {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) (u : (i : ι) → ↥(U i)) (i : ι) : ((structureMapMonoidHom U) u) i = ↑(u i)
```

**Original catalogue explanation (not a Lean docstring):** The distinguished product's structure map evaluates coordinatewise by the underlying subgroup inclusion.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L70) (native source start line).

### RestrictedProduct.productTail

Kind: `def`.

```lean
def RestrictedProduct.productTail {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) (s : Finset ι) : Subgroup ((i : ι) → ↥(U i))
```

**Native source docstring:** Elements of the distinguished product which are `1` on `s`.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L75) (native source start line).

### RestrictedProduct.restrictedProductTail

Kind: `def`.

```lean
def RestrictedProduct.restrictedProductTail {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) (s : Finset ι) : Subgroup (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)
```

**Native source docstring:** The product tail, embedded as a subgroup of the cofinite restricted product.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L79) (native source start line).

### RestrictedProduct.mem_productTail

Kind: `theorem`.

```lean
theorem RestrictedProduct.mem_productTail {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) {s : Finset ι} {u : (i : ι) → ↥(U i)} : u ∈ productTail U s ↔ ∀ i ∈ s, u i = 1
```

**Original catalogue explanation (not a Lean docstring):** Membership in the product tail means every coordinate in the selected finite set equals one.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L83) (native source start line).

### RestrictedProduct.structureMapMonoidHom_pi_mulSingle

Kind: `theorem`.

```lean
theorem RestrictedProduct.structureMapMonoidHom_pi_mulSingle {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) (i : ι) (u : ↥(U i)) : (structureMapMonoidHom U) (Pi.mulSingle i u) = mulSingle U i ↑u
```

**Original catalogue explanation (not a Lean docstring):** The structure map sends a single distinguished subgroup coordinate to the corresponding single restricted-product coordinate.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L89) (native source start line).

### RestrictedProduct.exists_productTail_le_ker

Kind: `theorem`.

```lean
theorem RestrictedProduct.exists_productTail_le_ker {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) [(i : ι) → TopologicalSpace (X i)] (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (χ : PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)) : ∃ (s : Finset ι), productTail U s ≤ (χ.comp (structureMapMonoidHom U)).ker
```

**Native source docstring:** Continuity of a character forces its restriction to the distinguished product to annihilate
all coordinates outside one finite set.

The index type is arbitrary.  The proof pulls a centered small arc back to the product, chooses a
finite cylinder contained in that preimage, and applies `Subgroup.le_ker_of_mapsTo_centeredArc` to
the corresponding product tail.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L100) (native source start line).

### RestrictedProduct.exists_restrictedProductTail_subset_of_mem_nhds

Kind: `theorem`.

```lean
theorem RestrictedProduct.exists_restrictedProductTail_subset_of_mem_nhds {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) [(i : ι) → TopologicalSpace (X i)] (hUopen : ∀ (i : ι), IsOpen ↑(U i)) {N : Set (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)} (hN : N ∈ nhds 1) : ∃ (s : Finset ι), ↑(restrictedProductTail U s) ⊆ N
```

**Native source docstring:** Every identity neighborhood in a cofinite restricted product with open distinguished
subgroups contains an embedded product tail.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L134) (native source start line).

### RestrictedProduct.characterTestSet

Kind: `def`.

```lean
def RestrictedProduct.characterTestSet {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) (s : Finset ι) : Set (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)
```

**Native source docstring:** A compact-open test set: the whole distinguished product together with the full
single-coordinate copies indexed by `s`.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L156) (native source start line).

### RestrictedProduct.isCompact_characterTestSet

Kind: `theorem`.

```lean
theorem RestrictedProduct.isCompact_characterTestSet {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) [(i : ι) → TopologicalSpace (X i)] [∀ (i : ι), Finite (X i)] [∀ (i : ι), DiscreteTopology (X i)] (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (s : Finset ι) : IsCompact (characterTestSet U s)
```

**Native source docstring:** For finite discrete coordinates, `characterTestSet` is compact.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L164) (native source start line).

### RestrictedProduct.coordinateCharacter

Kind: `def`.

```lean
noncomputable def RestrictedProduct.coordinateCharacter {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) [(i : ι) → TopologicalSpace (X i)] (χ : PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)) (i : ι) : X i →* Circle
```

**Native source docstring:** The local coordinate character obtained by restricting a global character to a
single-coordinate copy.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L177) (native source start line).

### RestrictedProduct.coordinateCharacter_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.coordinateCharacter_apply {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) [(i : ι) → TopologicalSpace (X i)] (χ : PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)) (i : ι) (x : X i) : (coordinateCharacter U χ i) x = χ (mulSingle U i x)
```

**Original catalogue explanation (not a Lean docstring):** The coordinate character obtained by probing a global character at a single coordinate evaluates at that coordinate's element.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L185) (native source start line).

### RestrictedProduct.reconstructedCoordinate

Kind: `def`.

```lean
noncomputable def RestrictedProduct.reconstructedCoordinate {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (χ : PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)) (i : ι) : Y i
```

**Native source docstring:** The coordinate recovered from a global character through an explicitly bijective local
character map.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L190) (native source start line).

### RestrictedProduct.reconstructedCoordinate_spec

Kind: `theorem`.

```lean
theorem RestrictedProduct.reconstructedCoordinate_spec {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (χ : PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)) (i : ι) (x : X i) : ((e i) x) (reconstructedCoordinate U e hperfect χ i) = χ (mulSingle U i x)
```

**Original catalogue explanation (not a Lean docstring):** The reconstructed representing coordinate has the specified local right-character values on every coordinate-domain element.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L198) (native source start line).

### RestrictedProduct.finset_prod_mulSingle_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.finset_prod_mulSingle_apply {ι : Type u_1} {X : ι → Type u_2} [(i : ι) → CommGroup (X i)] (U : (i : ι) → Subgroup (X i)) (s : Finset ι) (x : (i : ι) → X i) (i : ι) : (∏ j ∈ s, mulSingle U j (x j)) i = if i ∈ s then x i else 1
```

**Original catalogue explanation (not a Lean docstring):** At a coordinate in the selected finite set, the finite product of single-coordinate elements has the prescribed value; elsewhere it is one.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L209) (native source start line).

### RestrictedProduct.toPontryaginDual_surjective

Kind: `theorem`.

```lean
theorem RestrictedProduct.toPontryaginDual_surjective {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) : Function.Surjective ⇑(toPontryaginDual U V e horth hUopen hVopen he)
```

**Native source docstring:** Exact local perfectness and exact right-annihilator subgroups make the canonical map from the
second restricted product onto the Pontryagin dual of the first restricted product.

This proof works for arbitrary index types.  Local perfectness is the actual bijectivity of the
map `Y i →* (X i →* Circle)` defined by the bicharacter; no nondegeneracy or cardinality shortcut
is used.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L230) (native source start line).

### RestrictedProduct.toPontryaginDual_bijective

Kind: `theorem`.

```lean
theorem RestrictedProduct.toPontryaginDual_bijective {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) : Function.Bijective ⇑(toPontryaginDual U V e horth hUopen hVopen he)
```

**Native source docstring:** Under explicit local perfectness and exact right-annihilator hypotheses, the canonical map is
bijective.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L304) (native source start line).

### RestrictedProduct.toPontryaginDualMulEquiv

Kind: `def`.

```lean
noncomputable def RestrictedProduct.toPontryaginDualMulEquiv {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite ≃* PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)
```

**Native source docstring:** The algebraic equivalence underlying restricted-product character reconstruction.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L319) (native source start line).

### RestrictedProduct.toPontryaginDualMulEquiv_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.toPontryaginDualMulEquiv_apply {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : (toPontryaginDualMulEquiv U V e horth hUopen hVopen he hperfect hV) y = (toPontryaginDual U V e horth hUopen hVopen he) y
```

**Original catalogue explanation (not a Lean docstring):** The algebraic equivalence acts on a representing element through the canonical continuous dual map.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L330) (native source start line).

### RestrictedProduct.continuous_toPontryaginDualMulEquiv_symm

Kind: `theorem`.

```lean
theorem RestrictedProduct.continuous_toPontryaginDualMulEquiv_symm {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] [∀ (i : ι), Finite (X i)] [∀ (i : ι), DiscreteTopology (X i)] [∀ (i : ι), IsTopologicalGroup (Y i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) : Continuous ⇑(toPontryaginDualMulEquiv U V e horth hUopen hVopen he hperfect hV).symm
```

**Native source docstring:** For finite discrete coordinates on the character's domain, the inverse algebraic
reconstruction map is continuous.  The proof uses explicit compact-open test sets and product
tails; it does not use an open-mapping theorem.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L341) (native source start line).

### RestrictedProduct.pontryaginDualEquiv

Kind: `def`.

```lean
noncomputable def RestrictedProduct.pontryaginDualEquiv {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] [∀ (i : ι), Finite (X i)] [∀ (i : ι), DiscreteTopology (X i)] [∀ (i : ι), IsTopologicalGroup (Y i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite ≃ₜ* PontryaginDual (RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite)
```

**Native source docstring:** Finite discrete character-domain groups and topological representing groups, with explicit
local perfectness and exact annihilators, yield a topological multiplicative equivalence with the
compact-open Pontryagin dual.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L425) (native source start line).

### RestrictedProduct.pontryaginDualEquiv_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.pontryaginDualEquiv_apply {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] [∀ (i : ι), Finite (X i)] [∀ (i : ι), DiscreteTopology (X i)] [∀ (i : ι), IsTopologicalGroup (Y i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : (pontryaginDualEquiv U V e horth hUopen hVopen he hperfect hV) y = (toPontryaginDual U V e horth hUopen hVopen he) y
```

**Original catalogue explanation (not a Lean docstring):** The topological multiplicative equivalence acts through the same canonical continuous dual map.

[Source](../RestrictedProductDuality/CharacterReconstruction.lean#L441) (native source start line).

### RestrictedProduct.leftAnnihilator

Kind: `def`.

```lean
noncomputable def RestrictedProduct.leftAnnihilator {X : Type u_4} {Y : Type u_5} [CommGroup X] [CommGroup Y] (V : Subgroup Y) (e : X →* Y →* Circle) : Subgroup X
```

**Native source docstring:** The left annihilator of a subgroup under a multiplicative bicharacter.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L32) (native source start line).

### RestrictedProduct.mem_leftAnnihilator

Kind: `theorem`.

```lean
theorem RestrictedProduct.mem_leftAnnihilator {X : Type u_4} {Y : Type u_5} [CommGroup X] [CommGroup Y] {V : Subgroup Y} {e : X →* Y →* Circle} {x : X} : x ∈ leftAnnihilator V e ↔ ∀ y ∈ V, (e x) y = 1
```

**Original catalogue explanation (not a Lean docstring):** Membership in the left annihilator is equivalent to pairing to one with every element of the chosen right subgroup.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L37) (native source start line).

### RestrictedProduct.orthogonal_rightCharacter

Kind: `theorem`.

```lean
theorem RestrictedProduct.orthogonal_rightCharacter {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (i : ι) (y : Y i) : y ∈ V i → ∀ x ∈ U i, ((rightCharacter (e i)) y) x = 1
```

**Native source docstring:** Orthogonality is preserved when a bicharacter is viewed in the opposite
direction through `rightCharacter`.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L43) (native source start line).

### RestrictedProduct.pairing_rightCharacter

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_rightCharacter {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) : pairing V U (fun (i : ι) => rightCharacter (e i)) y x = pairing U V e x y
```

**Native source docstring:** Transposing every local bicharacter does not change the global pairing's
evaluation.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L51) (native source start line).

### RestrictedProduct.continuous_rightCharacter

Kind: `theorem`.

```lean
theorem RestrictedProduct.continuous_rightCharacter {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (i : ι) : Continuous fun (p : Y i × X i) => ((rightCharacter (e i)) p.1) p.2
```

**Native source docstring:** Joint continuity is preserved by transposing the two inputs of a local
bicharacter.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L60) (native source start line).

### RestrictedProduct.symmetricPontryaginDualEquiv

Kind: `def`.

```lean
noncomputable def RestrictedProduct.symmetricPontryaginDualEquiv {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] [∀ (i : ι), Finite (Y i)] [∀ (i : ι), DiscreteTopology (Y i)] [∀ (i : ι), IsTopologicalGroup (X i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(e i)) (hU : ∀ (i : ι), U i = leftAnnihilator (V i) (e i)) : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite ≃ₜ* PontryaginDual (RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite)
```

**Native source docstring:** The symmetric restricted-product duality equivalence, constructed directly
from left local perfectness and the reverse exact-annihilator equality.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L68) (native source start line).

### RestrictedProduct.symmetricPontryaginDualEquiv_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.symmetricPontryaginDualEquiv_apply {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] [∀ (i : ι), Finite (Y i)] [∀ (i : ι), DiscreteTopology (Y i)] [∀ (i : ι), IsTopologicalGroup (X i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(e i)) (hU : ∀ (i : ι), U i = leftAnnihilator (V i) (e i)) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : ((symmetricPontryaginDualEquiv U V e horth hUopen hVopen he hperfect hU) x) y = pairing U V e x y
```

**Native source docstring:** Evaluation of the symmetric equivalence is the original global pairing
with its arguments in their original order.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L82) (native source start line).

### RestrictedProduct.pontryaginDualEquiv_apply_eq_symmetric

Kind: `theorem`.

```lean
theorem RestrictedProduct.pontryaginDualEquiv_apply_eq_symmetric {ι : Type u_1} {X : ι → Type u_2} {Y : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (Y i)] (U : (i : ι) → Subgroup (X i)) (V : (i : ι) → Subgroup (Y i)) (e : (i : ι) → X i →* Y i →* Circle) [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)] [∀ (i : ι), Finite (X i)] [∀ (i : ι), DiscreteTopology (X i)] [∀ (i : ι), IsTopologicalGroup (Y i)] [∀ (i : ι), Finite (Y i)] [∀ (i : ι), DiscreteTopology (Y i)] [∀ (i : ι), IsTopologicalGroup (X i)] (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (hperfectRight : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) (hperfectLeft : ∀ (i : ι), Function.Bijective ⇑(e i)) (hU : ∀ (i : ι), U i = leftAnnihilator (V i) (e i)) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : ((pontryaginDualEquiv U V e horth hUopen hVopen he hperfectRight hV) y) x = ((symmetricPontryaginDualEquiv U V e horth hUopen hVopen he hperfectLeft hU) x) y
```

**Native source docstring:** The original and symmetric restricted-product duality equivalences have
the same evaluation pairing.  This is a direct computation, not an application
of a general biduality equivalence.

[Source](../RestrictedProductDuality/SymmetricDuality.lean#L97) (native source start line).

### RestrictedProduct.mapContinuousMonoidHom

Kind: `def`.

```lean
def RestrictedProduct.mapContinuousMonoidHom {ι : Type u_1} {X : ι → Type u_2} {X' : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (X' i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (X' i)] (U : (i : ι) → Subgroup (X i)) (U' : (i : ι) → Subgroup (X' i)) (f : (i : ι) → X i →ₜ* X' i) (hf : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(f i) ↑(U i) ↑(U' i)) : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite →ₜ* RestrictedProduct (fun (i : ι) => X' i) (fun (i : ι) => ↑(U' i)) Filter.cofinite
```

**Native source docstring:** A coordinatewise continuous homomorphism preserving the distinguished
subgroups at cofinitely many indices induces a continuous homomorphism of
cofinite restricted products.

[Source](../RestrictedProductDuality/Naturality.lean#L34) (native source start line).

### RestrictedProduct.mapContinuousMonoidHom_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.mapContinuousMonoidHom_apply {ι : Type u_1} {X : ι → Type u_2} {X' : ι → Type u_3} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (X' i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (X' i)] (U : (i : ι) → Subgroup (X i)) (U' : (i : ι) → Subgroup (X' i)) (f : (i : ι) → X i →ₜ* X' i) (hf : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(f i) ↑(U i) ↑(U' i)) (x : RestrictedProduct (fun (i : ι) => X i) (fun (i : ι) => ↑(U i)) Filter.cofinite) (i : ι) : ((mapContinuousMonoidHom U U' f hf) x) i = (f i) (x i)
```

**Original catalogue explanation (not a Lean docstring):** The induced continuous restricted-product homomorphism evaluates each coordinate through its original coordinate map.

[Source](../RestrictedProductDuality/Naturality.lean#L48) (native source start line).

### RestrictedProduct.pairing_mapContinuousMonoidHom

Kind: `theorem`.

```lean
theorem RestrictedProduct.pairing_mapContinuousMonoidHom {ι : Type u_1} {X : ι → Type u_2} {X' : ι → Type u_3} {Y : ι → Type u_4} {Y' : ι → Type u_5} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (X' i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → CommGroup (Y' i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (X' i)] [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → TopologicalSpace (Y' i)] (U : (i : ι) → Subgroup (X i)) (U' : (i : ι) → Subgroup (X' i)) (V : (i : ι) → Subgroup (Y i)) (V' : (i : ι) → Subgroup (Y' i)) (e : (i : ι) → X i →* Y i →* Circle) (e' : (i : ι) → X' i →* Y' i →* Circle) (f : (i : ι) → X' i →ₜ* X i) (g : (i : ι) → Y i →ₜ* Y' i) (hf : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(f i) ↑(U' i) ↑(U i)) (hg : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(g i) ↑(V i) ↑(V' i)) (hadj : ∀ (i : ι) (x : X' i) (y : Y i), ((e' i) x) ((g i) y) = ((e i) ((f i) x)) y) (x : RestrictedProduct (fun (i : ι) => X' i) (fun (i : ι) => ↑(U' i)) Filter.cofinite) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : pairing U' V' e' x ((mapContinuousMonoidHom V V' g hg) y) = pairing U V e ((mapContinuousMonoidHom U' U f hf) x) y
```

**Native source docstring:** Coordinatewise adjoint maps carry the global restricted-product pairing
to the global pairing.

[Source](../RestrictedProductDuality/Naturality.lean#L57) (native source start line).

### RestrictedProduct.toPontryaginDual_natural

Kind: `theorem`.

```lean
theorem RestrictedProduct.toPontryaginDual_natural {ι : Type u_1} {X : ι → Type u_2} {X' : ι → Type u_3} {Y : ι → Type u_4} {Y' : ι → Type u_5} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (X' i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → CommGroup (Y' i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (X' i)] [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → TopologicalSpace (Y' i)] (U : (i : ι) → Subgroup (X i)) (U' : (i : ι) → Subgroup (X' i)) (V : (i : ι) → Subgroup (Y i)) (V' : (i : ι) → Subgroup (Y' i)) (e : (i : ι) → X i →* Y i →* Circle) (e' : (i : ι) → X' i →* Y' i →* Circle) (f : (i : ι) → X' i →ₜ* X i) (g : (i : ι) → Y i →ₜ* Y' i) (hf : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(f i) ↑(U' i) ↑(U i)) (hg : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(g i) ↑(V i) ↑(V' i)) (hadj : ∀ (i : ι) (x : X' i) (y : Y i), ((e' i) x) ((g i) y) = ((e i) ((f i) x)) y) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (horth' : ∀ (i : ι), ∀ x ∈ U' i, ∀ y ∈ V' i, ((e' i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hUopen' : ∀ (i : ι), IsOpen ↑(U' i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (hVopen' : ∀ (i : ι), IsOpen ↑(V' i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (he' : ∀ (i : ι), Continuous fun (p : X' i × Y' i) => ((e' i) p.1) p.2) : (toPontryaginDual U' V' e' horth' hUopen' hVopen' he').comp (mapContinuousMonoidHom V V' g hg) = (PontryaginDual.map (mapContinuousMonoidHom U' U f hf)).comp (toPontryaginDual U V e horth hUopen hVopen he)
```

**Native source docstring:** The canonical restricted-product pairing map is natural: covariant maps on
the representing coordinates correspond to contravariant Pontryagin-dual maps
on the character-domain coordinates.

[Source](../RestrictedProductDuality/Naturality.lean#L74) (native source start line).

### RestrictedProduct.pontryaginDualEquiv_natural_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.pontryaginDualEquiv_natural_apply {ι : Type u_1} {X : ι → Type u_2} {X' : ι → Type u_3} {Y : ι → Type u_4} {Y' : ι → Type u_5} [(i : ι) → CommGroup (X i)] [(i : ι) → CommGroup (X' i)] [(i : ι) → CommGroup (Y i)] [(i : ι) → CommGroup (Y' i)] [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (X' i)] [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → TopologicalSpace (Y' i)] [∀ (i : ι), Finite (X i)] [∀ (i : ι), Finite (X' i)] [∀ (i : ι), DiscreteTopology (X i)] [∀ (i : ι), DiscreteTopology (X' i)] [∀ (i : ι), IsTopologicalGroup (Y i)] [∀ (i : ι), IsTopologicalGroup (Y' i)] (U : (i : ι) → Subgroup (X i)) (U' : (i : ι) → Subgroup (X' i)) (V : (i : ι) → Subgroup (Y i)) (V' : (i : ι) → Subgroup (Y' i)) (e : (i : ι) → X i →* Y i →* Circle) (e' : (i : ι) → X' i →* Y' i →* Circle) (f : (i : ι) → X' i →ₜ* X i) (g : (i : ι) → Y i →ₜ* Y' i) (hf : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(f i) ↑(U' i) ↑(U i)) (hg : ∀ᶠ (i : ι) in Filter.cofinite, Set.MapsTo ⇑(g i) ↑(V i) ↑(V' i)) (hadj : ∀ (i : ι) (x : X' i) (y : Y i), ((e' i) x) ((g i) y) = ((e i) ((f i) x)) y) (horth : ∀ (i : ι), ∀ x ∈ U i, ∀ y ∈ V i, ((e i) x) y = 1) (horth' : ∀ (i : ι), ∀ x ∈ U' i, ∀ y ∈ V' i, ((e' i) x) y = 1) (hUopen : ∀ (i : ι), IsOpen ↑(U i)) (hUopen' : ∀ (i : ι), IsOpen ↑(U' i)) (hVopen : ∀ (i : ι), IsOpen ↑(V i)) (hVopen' : ∀ (i : ι), IsOpen ↑(V' i)) (he : ∀ (i : ι), Continuous fun (p : X i × Y i) => ((e i) p.1) p.2) (he' : ∀ (i : ι), Continuous fun (p : X' i × Y' i) => ((e' i) p.1) p.2) (hperfect : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e i))) (hperfect' : ∀ (i : ι), Function.Bijective ⇑(rightCharacter (e' i))) (hV : ∀ (i : ι), V i = rightAnnihilator (U i) (e i)) (hV' : ∀ (i : ι), V' i = rightAnnihilator (U' i) (e' i)) (y : RestrictedProduct (fun (i : ι) => Y i) (fun (i : ι) => ↑(V i)) Filter.cofinite) : (pontryaginDualEquiv U' V' e' horth' hUopen' hVopen' he' hperfect' hV') ((mapContinuousMonoidHom V V' g hg) y) = (PontryaginDual.map (mapContinuousMonoidHom U' U f hf)) ((pontryaginDualEquiv U V e horth hUopen hVopen he hperfect hV) y)
```

**Native source docstring:** Pointwise naturality of the restricted-product duality equivalence.

[Source](../RestrictedProductDuality/Naturality.lean#L103) (native source start line).

## Legacy client and scoped local entries (8 native entries)

### RestrictedProduct.punitBicharacter

Kind: `def`.

```lean
noncomputable def RestrictedProduct.punitBicharacter : PUnit.{u_1 + 1} →* PUnit.{u_2 + 1} →* Circle
```

**Native source docstring:** The unique bicharacter between trivial groups, used to exercise index-size edge cases.

[Source](../RestrictedProductDuality/Clients.lean#L60) (native source start line).

### RestrictedProduct.punitBicharacter_perfect

Kind: `theorem`.

```lean
theorem RestrictedProduct.punitBicharacter_perfect : Function.Bijective ⇑(rightCharacter punitBicharacter)
```

**Native source docstring:** The trivial bicharacter is locally perfect because both its source and character group are
singletons.

[Source](../RestrictedProductDuality/Clients.lean#L63) (native source start line).

### RestrictedProduct.punit_rightAnnihilator

Kind: `theorem`.

```lean
theorem RestrictedProduct.punit_rightAnnihilator : ⊤ = rightAnnihilator ⊤ punitBicharacter
```

**Native source docstring:** The full subgroup of the trivial group is its own right annihilator.

[Source](../RestrictedProductDuality/Clients.lean#L76) (native source start line).

### RestrictedProduct.zmodBicharacter

Kind: `def`.

```lean
noncomputable def RestrictedProduct.zmodBicharacter (n : ℕ) [NeZero n] : Multiplicative (ZMod n) →* Multiplicative (ZMod n) →* Circle
```

**Native source docstring:** The standard symmetric bicharacter on a finite cyclic group, in multiplicative notation.

[Source](../RestrictedProductDuality/Clients.lean#L90) (native source start line).

### RestrictedProduct.zmodBicharacter_apply

Kind: `theorem`.

```lean
theorem RestrictedProduct.zmodBicharacter_apply (n : ℕ) [NeZero n] (x y : Multiplicative (ZMod n)) : ((zmodBicharacter n) x) y = (AddChar.zmod n (Multiplicative.toAdd x)) (Multiplicative.toAdd y)
```

**Original catalogue explanation (not a Lean docstring):** Evaluation of the cyclic multiplicative bicharacter is the standard finite-character value from the two underlying residues.

[Source](../RestrictedProductDuality/Clients.lean#L97) (native source start line).

### RestrictedProduct.zmodBicharacter_perfect

Kind: `theorem`.

```lean
theorem RestrictedProduct.zmodBicharacter_perfect (n : ℕ) [NeZero n] : Function.Bijective ⇑(rightCharacter (zmodBicharacter n))
```

**Native source docstring:** The standard cyclic bicharacter induces the actual bijection onto circle-valued
characters.

[Source](../RestrictedProductDuality/Clients.lean#L103) (native source start line).

### RestrictedProduct.zmodTwoTopologicalSpaceNaturality

Kind: `def`.

```lean
def RestrictedProduct.zmodTwoTopologicalSpaceNaturality : TopologicalSpace (Multiplicative (ZMod 2))
```

**Native source docstring:** The discrete topology for cyclic naturality clients, scoped to this file.

[Source](../RestrictedProductDuality/NaturalityClients.lean#L31) (native source start line).

### RestrictedProduct.zmodTwoDiscreteTopologyNaturality

Kind: `theorem`.

```lean
theorem RestrictedProduct.zmodTwoDiscreteTopologyNaturality : DiscreteTopology (Multiplicative (ZMod 2))
```

**Native source docstring:** The corresponding discrete-topology witness for cyclic naturality clients.

[Source](../RestrictedProductDuality/NaturalityClients.lean#L34) (native source start line).

## Default-built public-import test (0 native entries)

No public/native named entries in this section.
