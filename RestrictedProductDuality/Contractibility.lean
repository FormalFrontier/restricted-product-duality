/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.BasedHomotopy
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Based contractions of singleton restricted products

Chosen coordinate contractions, relative to their chosen points, assemble to a
contraction relative to the canonical restricted-product point. The topology is
the final topology of the singleton-cofinite restricted product. Factor topologies
are arbitrary and the index type may be empty.

The input is chosen relative homotopy data, not merely contractibility of the
factors. The resulting relative homotopy also gives `ContractibleSpace`. Its
endpoints and fixed point are described by `ContinuousMap.HomotopyWith.apply_zero`,
`ContinuousMap.HomotopyWith.apply_one` and `ContinuousMap.HomotopyRel.eq_fst`.

## References

The construction uses `RestrictedProduct.SingletonNaturality.pointMapHomotopyRel`
and Mathlib's `ContinuousMap.HomotopyRel.cast`. The contractibility conclusion uses
Mathlib's `contractible_iff_id_nullhomotopic`.
-/

@[expose] public section

noncomputable section

open scoped unitInterval

universe u v

namespace RestrictedProduct.SingletonNaturality

open RestrictedProduct.SingletonPathComponents

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- Chosen based contractions of the factors induce a contraction fixing the
canonical point of the singleton-cofinite restricted product. -/
def pointContraction (b : ∀ i, X i)
    (H : ∀ i, ContinuousMap.HomotopyRel (ContinuousMap.id (X i))
      (ContinuousMap.const (X i) (b i)) ({b i} : Set (X i))) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PointProduct b))
      (ContinuousMap.const (PointProduct b) (RestrictedProduct.singletonBasepoint b))
      ({RestrictedProduct.singletonBasepoint b} : Set (PointProduct b)) :=
  (pointMapHomotopyRel (X := X) (Y := X) b b (fun i ↦ ContinuousMap.id (X i))
    (fun i ↦ ContinuousMap.const (X i) (b i)) (fun _ ↦ rfl) (fun _ ↦ rfl) H).cast
      (pointMap_id b) (pointMap_const (X := X) (Y := X) b b)

/-- Every coordinate of the contraction is the chosen coordinate contraction. -/
@[simp]
theorem pointContraction_apply (b : ∀ i, X i)
    (H : ∀ i, ContinuousMap.HomotopyRel (ContinuousMap.id (X i))
      (ContinuousMap.const (X i) (b i)) ({b i} : Set (X i)))
    (t : I) (x : PointProduct b) (i : ι) :
    pointContraction b H (t, x) i = H i (t, x i) := by
  exact pointMapHomotopyRel_apply b b (fun i ↦ ContinuousMap.id (X i))
    (fun i ↦ ContinuousMap.const (X i) (b i)) (fun _ ↦ rfl) (fun _ ↦ rfl) H t x i

/-- A singleton-cofinite restricted product with chosen based coordinate
contractions is contractible. -/
theorem contractibleSpace_of_basedContractions (b : ∀ i, X i)
    (H : ∀ i, ContinuousMap.HomotopyRel (ContinuousMap.id (X i))
      (ContinuousMap.const (X i) (b i)) ({b i} : Set (X i))) :
    ContractibleSpace (PointProduct b) := by
  exact (contractible_iff_id_nullhomotopic (PointProduct b)).2
    ⟨RestrictedProduct.singletonBasepoint b, ⟨(pointContraction b H).toHomotopy⟩⟩

end RestrictedProduct.SingletonNaturality
