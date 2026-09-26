/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Compact subsets of cofinite restricted products

This file records reusable stage-control lemmas for the cofinite topology on a
restricted product.
-/

public section

set_option warningAsError true

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)}

/-- The cofinite stage on which coordinates outside `s` lie in the distinguished subsets. -/
@[expose] def cofiniteStage (s : Finset ι) : Set (Πʳ i, [R i, A i]) :=
  {x | ∀ i, i ∉ s → x i ∈ A i}

@[simp]
theorem mem_cofiniteStage {s : Finset ι} {x : Πʳ i, [R i, A i]} :
    x ∈ cofiniteStage (R := R) (A := A) s ↔ ∀ i, i ∉ s → x i ∈ A i :=
  Iff.rfl

/-- Cofinite stages grow when their finite exceptional sets grow. -/
theorem cofiniteStage_mono {s t : Finset ι} (hst : s ⊆ t) :
    cofiniteStage (R := R) (A := A) s ⊆ cofiniteStage (R := R) (A := A) t := by
  intro x hx i hi
  exact hx i fun his ↦ hi (hst his)

/-- A canonical finite exceptional set for an element of a cofinite restricted product. -/
noncomputable def exceptionalFinset (x : Πʳ i, [R i, A i]) : Finset ι :=
  (Filter.eventually_cofinite.mp x.2).toFinset

theorem mem_cofiniteStage_exceptionalFinset (x : Πʳ i, [R i, A i]) :
    x ∈ cofiniteStage (R := R) (A := A) (exceptionalFinset x) := by
  intro i hi
  by_contra hxi
  apply hi
  exact (Filter.eventually_cofinite.mp x.2).mem_toFinset.mpr hxi

section Topology

variable [∀ i, TopologicalSpace (R i)]

/-- A cofinite stage is open when all distinguished subsets are open. -/
theorem isOpen_cofiniteStage (hAopen : ∀ i, IsOpen (A i)) (s : Finset ι) :
    IsOpen (cofiniteStage (R := R) (A := A) s) := by
  change IsOpen {f : Πʳ i, [R i, A i] | ∀ i, i ∉ s → f.1 i ∈ A i}
  exact isOpen_forall_imp_mem (R := R) (A := A) hAopen

/-- Every compact subset of a cofinite restricted product lies in one finite stage.

The index type is arbitrary. The proof uses the directed open cover by cofinite stages, so it
does not require a countable exhaustion or a sigma-compactness assumption. -/
theorem exists_subset_cofiniteStage (hAopen : ∀ i, IsOpen (A i))
    {K : Set (Πʳ i, [R i, A i])} (hK : IsCompact K) :
    ∃ s : Finset ι, K ⊆ cofiniteStage (R := R) (A := A) s := by
  classical
  apply hK.elim_directed_cover (fun s : Finset ι ↦ cofiniteStage (R := R) (A := A) s)
  · exact fun s ↦ isOpen_cofiniteStage hAopen s
  · intro x _
    exact Set.mem_iUnion.mpr ⟨exceptionalFinset x, mem_cofiniteStage_exceptionalFinset x⟩
  · intro s t
    exact ⟨s ∪ t, cofiniteStage_mono Finset.subset_union_left,
      cofiniteStage_mono Finset.subset_union_right⟩

end Topology

end RestrictedProduct
