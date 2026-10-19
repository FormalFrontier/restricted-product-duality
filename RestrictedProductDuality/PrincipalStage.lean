/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.CompactStage

/-!
# Singleton principal stages and ordinary products

For chosen points `b i`, the restricted product at the principal filter on `Fᶜ` is
homeomorphic to the ordinary dependent product over an arbitrary set `F`. The
homeomorphism is restriction; its inverse inserts the chosen points outside `F`.
No finiteness, separation, openness or algebraic structure is required.

For finite `F`, the comparison followed by Mathlib's restricted-product inclusion
embeds the ordinary finite product into the cofinite restricted product. Its range
is the corresponding `cofiniteStage`. The ordinary finite products detect continuity
out of the cofinite restricted product by Mathlib's final-topology universal property.

## References

The restricted-product carrier, principal induced topology, inclusions, embeddings
and final-topology universal property are from Mathlib's
`Topology.Algebra.RestrictedProduct` modules, due to Anatole Dedecker. The finite
exception stages are from `RestrictedProductDuality.CompactStage`. These comparisons
express the ordinary finite-support product construction; all products in this file
have the ordinary Pi topology, not a compactly generated modification.
-/

@[expose] public section

noncomputable section

open Filter Set Topology
open scoped RestrictedProduct

universe u v w

namespace RestrictedProduct

variable {ι : Type u} {R : ι → Type v}

/-- Insert the chosen points outside an arbitrary set of free coordinates. -/
def singletonPrincipalInsert (b : ∀ i, R i) (F : Set ι) (y : ∀ i : F, R i) :
    RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ) := by
  classical
  exact ⟨fun i ↦ if hi : i ∈ F then y ⟨i, hi⟩ else b i, by
    intro i hi
    have hiF : i ∉ F := hi
    change (if hi : i ∈ F then y ⟨i, hi⟩ else b i) = b i
    exact dite_eq_right hiF⟩

@[simp]
theorem singletonPrincipalInsert_apply_of_mem (b : ∀ i, R i) (F : Set ι)
    (y : ∀ i : F, R i) (i : ι) (hi : i ∈ F) :
    singletonPrincipalInsert b F y i = y ⟨i, hi⟩ := by
  classical
  change (if hi' : i ∈ F then y ⟨i, hi'⟩ else b i) = y ⟨i, hi⟩
  exact dite_eq_left hi

@[simp]
theorem singletonPrincipalInsert_apply_of_notMem (b : ∀ i, R i) (F : Set ι)
    (y : ∀ i : F, R i) (i : ι) (hi : i ∉ F) :
    singletonPrincipalInsert b F y i = b i := by
  classical
  change (if hi' : i ∈ F then y ⟨i, hi'⟩ else b i) = b i
  exact dite_eq_right hi

/-- A singleton principal-stage point is fixed outside its free coordinates. -/
theorem singletonPrincipal_apply_of_notMem (b : ∀ i, R i) (F : Set ι)
    (x : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ))
    (i : ι) (hi : i ∉ F) : x i = b i :=
  Set.mem_singleton_iff.mp (x.2 hi)

/-- Singleton principal-stage points are determined by their free coordinates. -/
@[ext (iff := false)]
theorem singletonPrincipal_ext {b : ∀ i, R i} {F : Set ι}
    {x x' : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ)}
    (h : ∀ i : F, x i = x' i) : x = x' := by
  apply RestrictedProduct.ext
  intro i
  by_cases hi : i ∈ F
  · exact h ⟨i, hi⟩
  · exact (singletonPrincipal_apply_of_notMem b F x i hi).trans
      (singletonPrincipal_apply_of_notMem b F x' i hi).symm

/-- Equality in a singleton principal stage is equality on the free coordinates. -/
theorem singletonPrincipal_ext_iff {b : ∀ i, R i} {F : Set ι}
    {x x' : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ)} :
    x = x' ↔ ∀ i : F, x i = x' i :=
  ⟨fun h i ↦ congrArg (fun z ↦ z i) h, singletonPrincipal_ext⟩

@[simp]
theorem domRestrict_singletonPrincipalInsert (b : ∀ i, R i) (F : Set ι)
    (y : ∀ i : F, R i) :
    F.domRestrict (fun i ↦ singletonPrincipalInsert b F y i) = y := by
  funext i
  exact singletonPrincipalInsert_apply_of_mem b F y i i.2

@[simp]
theorem singletonPrincipalInsert_domRestrict (b : ∀ i, R i) (F : Set ι)
    (x : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ)) :
    singletonPrincipalInsert b F (F.domRestrict (fun i ↦ x i)) = x := by
  apply singletonPrincipal_ext
  intro i
  exact singletonPrincipalInsert_apply_of_mem b F _ i i.2

/-- Insert an ordinary finite product using the principal-stage inclusion. -/
def singletonFinsetInsert (b : ∀ i, R i) (s : Finset ι) (y : ∀ i : s, R i) :
    RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite :=
  inclusion R (fun i ↦ ({b i} : Set (R i)))
    (Filter.le_principal_iff.mpr s.eventually_cofinite_notMem)
    (singletonPrincipalInsert b (↑s : Set ι) y)

@[simp]
theorem singletonFinsetInsert_apply_of_mem (b : ∀ i, R i) (s : Finset ι)
    (y : ∀ i : s, R i) (i : ι) (hi : i ∈ s) :
    singletonFinsetInsert b s y i = y ⟨i, hi⟩ :=
  singletonPrincipalInsert_apply_of_mem b (↑s : Set ι) y i hi

@[simp]
theorem singletonFinsetInsert_apply_of_notMem (b : ∀ i, R i) (s : Finset ι)
    (y : ∀ i : s, R i) (i : ι) (hi : i ∉ s) :
    singletonFinsetInsert b s y i = b i :=
  singletonPrincipalInsert_apply_of_notMem b (↑s : Set ι) y i hi

/-- Restricting a finite insertion recovers the original ordinary product point. -/
theorem restrict_singletonFinsetInsert (b : ∀ i, R i) (s : Finset ι)
    (y : ∀ i : s, R i) :
    s.restrict (fun i ↦ singletonFinsetInsert b s y i) = y := by
  funext i
  exact singletonFinsetInsert_apply_of_mem b s y i i.2

/-- Insertion after restriction recovers precisely the points in the finite stage. -/
theorem singletonFinsetInsert_restrict (b : ∀ i, R i) (s : Finset ι)
    (x : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
    (hx : x ∈ cofiniteStage (R := R) (A := fun i ↦ ({b i} : Set (R i))) s) :
    singletonFinsetInsert b s (s.restrict (fun i ↦ x i)) = x := by
  apply RestrictedProduct.ext
  intro i
  by_cases hi : i ∈ s
  · exact singletonFinsetInsert_apply_of_mem b s _ i hi
  · rw [singletonFinsetInsert_apply_of_notMem b s _ i hi]
    exact (Set.mem_singleton_iff.mp (hx i hi)).symm

section Topology

variable [∀ i, TopologicalSpace (R i)]

/-- Insertion into a singleton principal stage is continuous for the ordinary Pi topology. -/
@[fun_prop]
theorem continuous_singletonPrincipalInsert (b : ∀ i, R i) (F : Set ι) :
    Continuous (singletonPrincipalInsert b F) := by
  apply (continuous_rng_of_principal_iff_forall
    (R := R) (A := fun i ↦ ({b i} : Set (R i))) (S := Fᶜ)
    (f := singletonPrincipalInsert b F)).mpr
  intro i
  change Continuous (fun y : ∀ j : F, R j ↦ singletonPrincipalInsert b F y i)
  by_cases hi : i ∈ F
  · simpa only [singletonPrincipalInsert_apply_of_mem b F _ i hi]
      using (continuous_apply (⟨i, hi⟩ : F) :
        Continuous (fun y : ∀ j : F, R j ↦ y ⟨i, hi⟩))
  · simpa only [singletonPrincipalInsert_apply_of_notMem b F _ i hi]
      using (continuous_const : Continuous (fun _ : ∀ j : F, R j ↦ b i))

/-- Restriction identifies a singleton principal stage with the ordinary dependent product
on its free coordinates. The inverse inserts `b i` outside `F`.

The set `F` is arbitrary. The topology is Mathlib's principal restricted-product topology,
which is induced from the full ordinary product. -/
def singletonPrincipalHomeomorph (b : ∀ i, R i) (F : Set ι) :
    RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ) ≃ₜ (∀ i : F, R i) where
  toFun x := F.domRestrict (fun i ↦ x i)
  invFun := singletonPrincipalInsert b F
  left_inv := singletonPrincipalInsert_domRestrict b F
  right_inv := domRestrict_singletonPrincipalInsert b F
  continuous_toFun := (Pi.continuous_domRestrict F).comp continuous_coe
  continuous_invFun := continuous_singletonPrincipalInsert b F

/-- The forward comparison is exactly ordinary restriction. -/
theorem singletonPrincipalHomeomorph_apply (b : ∀ i, R i) (F : Set ι)
    (x : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ)) :
    singletonPrincipalHomeomorph b F x = F.domRestrict (fun i ↦ x i) :=
  rfl

@[simp]
theorem singletonPrincipalHomeomorph_apply_apply (b : ∀ i, R i) (F : Set ι)
    (x : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ)) (i : F) :
    singletonPrincipalHomeomorph b F x i = x i :=
  rfl

/-- The inverse comparison is exactly insertion of the chosen points. -/
theorem singletonPrincipalHomeomorph_symm_apply (b : ∀ i, R i) (F : Set ι)
    (y : ∀ i : F, R i) :
    (singletonPrincipalHomeomorph b F).symm y = singletonPrincipalInsert b F y :=
  rfl

@[simp]
theorem singletonPrincipalHomeomorph_symm_apply_of_mem (b : ∀ i, R i) (F : Set ι)
    (y : ∀ i : F, R i) (i : ι) (hi : i ∈ F) :
    (singletonPrincipalHomeomorph b F).symm y i = y ⟨i, hi⟩ :=
  singletonPrincipalInsert_apply_of_mem b F y i hi

@[simp]
theorem singletonPrincipalHomeomorph_symm_apply_of_notMem (b : ∀ i, R i) (F : Set ι)
    (y : ∀ i : F, R i) (i : ι) (hi : i ∉ F) :
    (singletonPrincipalHomeomorph b F).symm y i = b i :=
  singletonPrincipalInsert_apply_of_notMem b F y i hi

/-- The coordinate restriction formula uniquely determines the principal comparison. -/
theorem singletonPrincipalHomeomorph_unique (b : ∀ i, R i) (F : Set ι)
    (e : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ) ≃ₜ (∀ i : F, R i))
    (he : ∀ x (i : F), e x i = x i) : e = singletonPrincipalHomeomorph b F := by
  apply Homeomorph.ext
  intro x
  funext i
  exact he x i

/-- Characterization of the principal comparison by its free-coordinate evaluations. -/
theorem singletonPrincipalHomeomorph_eq_iff (b : ∀ i, R i) (F : Set ι)
    (e : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 Fᶜ) ≃ₜ (∀ i : F, R i)) :
    e = singletonPrincipalHomeomorph b F ↔ ∀ x (i : F), e x i = x i := by
  constructor
  · rintro rfl
    exact singletonPrincipalHomeomorph_apply_apply b F
  · exact singletonPrincipalHomeomorph_unique b F e

/-- At the empty set of free coordinates, the inverse comparison has every coordinate
at its chosen point. -/
theorem singletonPrincipalHomeomorph_empty_symm_apply (b : ∀ i, R i)
    (y : ∀ i : (∅ : Set ι), R i) (i : ι) :
    (singletonPrincipalHomeomorph b ∅).symm y i = b i :=
  singletonPrincipalHomeomorph_symm_apply_of_notMem b ∅ y i (by simp)

/-- Finite insertion is the inverse principal comparison followed by the stock inclusion. -/
theorem singletonFinsetInsert_eq_inclusion_comp (b : ∀ i, R i) (s : Finset ι) :
    singletonFinsetInsert b s =
      inclusion R (fun i ↦ ({b i} : Set (R i)))
        (Filter.le_principal_iff.mpr s.eventually_cofinite_notMem) ∘
      (singletonPrincipalHomeomorph b (↑s : Set ι)).symm :=
  rfl

/-- Every ordinary finite product embeds as the corresponding singleton cofinite stage. -/
theorem isEmbedding_singletonFinsetInsert (b : ∀ i, R i) (s : Finset ι) :
    IsEmbedding (singletonFinsetInsert b s) := by
  rw [singletonFinsetInsert_eq_inclusion_comp]
  exact (isEmbedding_inclusion_principal
    (Filter.le_principal_iff.mpr s.eventually_cofinite_notMem)).comp
    (singletonPrincipalHomeomorph b (↑s : Set ι)).symm.isEmbedding

@[fun_prop]
theorem continuous_singletonFinsetInsert (b : ∀ i, R i) (s : Finset ι) :
    Continuous (singletonFinsetInsert b s) :=
  (isEmbedding_singletonFinsetInsert b s).continuous

/-- The range of ordinary finite insertion is exactly the finite exceptional-coordinate stage. -/
theorem range_singletonFinsetInsert (b : ∀ i, R i) (s : Finset ι) :
    Set.range (singletonFinsetInsert b s) =
      cofiniteStage (R := R) (A := fun i ↦ ({b i} : Set (R i))) s := by
  rw [singletonFinsetInsert_eq_inclusion_comp, Set.range_comp,
    (singletonPrincipalHomeomorph b (↑s : Set ι)).symm.range_coe,
    Set.image_univ, range_inclusion]
  rfl

/-- A map out of the singleton cofinite restricted product is continuous exactly when
its restrictions to all ordinary finite products are continuous.

This is Mathlib's `RestrictedProduct.continuous_dom` expressed through the principal
comparisons, not a change of topology. The observer universe is independent of the
index and fiber universes. -/
theorem continuous_dom_singleton_iff (b : ∀ i, R i) {X : Type w} [TopologicalSpace X]
    {f : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite → X} :
    Continuous f ↔ ∀ s : Finset ι, Continuous (f ∘ singletonFinsetInsert b s) := by
  classical
  refine ⟨fun hf s ↦ hf.comp (continuous_singletonFinsetInsert b s), fun h ↦ ?_⟩
  apply continuous_dom.mpr
  intro S hS
  have hSc : Sᶜ.Finite := Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
  let s : Finset ι := hSc.toFinset
  have heq : f ∘ inclusion R (fun i ↦ ({b i} : Set (R i))) hS =
      (f ∘ singletonFinsetInsert b s) ∘
        (fun x : RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) (𝓟 S) ↦
          s.restrict (fun i ↦ x i)) := by
    funext x
    apply congrArg f
    exact (singletonFinsetInsert_restrict b s
      (inclusion R (fun i ↦ ({b i} : Set (R i))) hS x) (by
        intro i hi
        have hiS : i ∈ S := by
          by_contra hn
          exact hi (hSc.mem_toFinset.mpr hn)
        exact x.2 hiS)).symm
  rw [heq]
  exact (h s).comp ((Finset.continuous_restrict s).comp continuous_coe)

end Topology

end RestrictedProduct
