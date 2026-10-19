/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact subsets of cofinite restricted products

This file records reusable stage-control lemmas for the cofinite topology on a
restricted product. Besides the open-stage argument, it gives compact containment
for arbitrary distinguished subsets when the restricted product is T1.

## References

The carrier, topology and principal-stage inclusions are from Mathlib's restricted-product
formalization. For the finite-support-product viewpoint, see J. P. May,
*A Concise Course in Algebraic Topology*. This formalization was developed by
Formal Frontier's AI agents.
-/

@[expose] public section

set_option warningAsError true

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

universe u v

variable {ι : Type u} {R : ι → Type v} {A : (i : ι) → Set (R i)}

/-- The cofinite stage on which coordinates outside `s` lie in the distinguished subsets. -/
def cofiniteStage (s : Finset ι) : Set (Πʳ i, [R i, A i]) :=
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

/-- Membership in the canonical exceptional set means failure to lie in the distinguished subset. -/
@[simp]
theorem mem_exceptionalFinset {x : Πʳ i, [R i, A i]} {i : ι} :
    i ∈ exceptionalFinset x ↔ x i ∉ A i := by
  classical
  exact (Filter.eventually_cofinite.mp x.2).mem_toFinset

theorem mem_cofiniteStage_exceptionalFinset (x : Πʳ i, [R i, A i]) :
    x ∈ cofiniteStage (R := R) (A := A) (exceptionalFinset x) := by
  intro i hi
  by_contra hxi
  apply hi
  exact (Filter.eventually_cofinite.mp x.2).mem_toFinset.mpr hxi

-- Under failure of uniform finite containment, choose points with a fresh bad coordinate.
-- Accumulating whole exceptional sets makes both the points and the bad coordinates distinct.
private theorem exists_sequence_fresh_exceptional {K : Set (Πʳ i, [R i, A i])}
    (h : ∀ s : Finset ι, ∃ x ∈ K, ∃ i, i ∉ s ∧ i ∈ exceptionalFinset x) :
    ∃ f : ℕ → Πʳ i, [R i, A i], ∃ c : ℕ → ι,
      (∀ n, f n ∈ K) ∧ Function.Injective f ∧ Function.Injective c ∧
        ∀ n, c n ∈ exceptionalFinset (f n) := by
  classical
  choose x hx i hi hbad using h
  let s : ℕ → Finset ι := Nat.rec ∅ (fun _ t ↦ t ∪ exceptionalFinset (x t))
  let f : ℕ → Πʳ i, [R i, A i] := fun n ↦ x (s n)
  let c : ℕ → ι := fun n ↦ i (s n)
  have hs_succ (n : ℕ) : s (n + 1) = s n ∪ exceptionalFinset (f n) := rfl
  have hs_mono : Monotone s := monotone_nat_of_le_succ fun n ↦ by
    rw [hs_succ]
    exact Finset.subset_union_left
  have hprior {m n : ℕ} (hmn : m < n) : exceptionalFinset (f m) ⊆ s n := by
    have hm : exceptionalFinset (f m) ⊆ s (m + 1) := by
      rw [hs_succ]
      exact Finset.subset_union_right
    exact hm.trans (hs_mono (Nat.succ_le_of_lt hmn))
  have hf_ne {m n : ℕ} (hmn : m < n) : f m ≠ f n := by
    intro heq
    apply hi (s n)
    apply hprior hmn
    rw [heq]
    exact hbad (s n)
  have hc_ne {m n : ℕ} (hmn : m < n) : c m ≠ c n := by
    intro heq
    apply hi (s n)
    change c n ∈ s n
    rw [← heq]
    exact hprior hmn (hbad (s m))
  refine ⟨f, c, (fun n ↦ hx (s n)), ?_, ?_, (fun n ↦ hbad (s n))⟩
  · intro m n heq
    rcases lt_trichotomy m n with hlt | he | hgt
    · exact (hf_ne hlt heq).elim
    · exact he
    · exact (hf_ne hgt heq.symm).elim
  · intro m n heq
    rcases lt_trichotomy m n with hlt | he | hgt
    · exact (hc_ne hlt heq).elim
    · exact he
    · exact (hc_ne hgt heq.symm).elim

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

-- A sparse sequence meets each principal stage in finitely many points. The stock final
-- topology therefore makes every subset of its range closed, without assumptions on the A i.
private theorem isClosed_of_subset_range_exceptional [T1Space (Πʳ i, [R i, A i])]
    {f : ℕ → Πʳ i, [R i, A i]} {c : ℕ → ι} (hc : Function.Injective c)
    (hbad : ∀ n, c n ∈ exceptionalFinset (f n))
    {D : Set (Πʳ i, [R i, A i])} (hD : D ⊆ Set.range f) : IsClosed D := by
  classical
  rw [topologicalSpace_eq_iSup (R := R) (A := A) cofinite]
  apply isClosed_iSup_iff.mpr
  intro S
  apply isClosed_iSup_iff.mpr
  intro hS
  apply isClosed_coinduced.mpr
  let g : (Πʳ i, [R i, A i]_[𝓟 S]) → Πʳ i, [R i, A i] := inclusion R A hS
  have hg : IsEmbedding g := isEmbedding_inclusion_principal hS
  let : T1Space (Πʳ i, [R i, A i]_[𝓟 S]) := hg.t1Space
  have hfin : Sᶜ.Finite := mem_cofinite.mp (le_principal_iff.mp hS)
  have hnfin : (c ⁻¹' Sᶜ).Finite := Set.Finite.preimage hc.injOn hfin
  have hpre : (g ⁻¹' D).Finite := by
    refine (Set.Finite.preimage hg.injective.injOn (hnfin.image f)).subset ?_
    intro y hy
    obtain ⟨n, hn⟩ := hD hy
    have hcn : c n ∉ S := by
      intro hcS
      apply (mem_exceptionalFinset.mp (hbad n))
      rw [hn]
      exact y.2 hcS
    exact ⟨n, hcn, hn⟩
  exact hpre.isClosed

/-- Every compact subset of a T1 cofinite restricted product lies in one finite stage.

Only the restricted product itself is assumed T1; the distinguished subsets need not be
open or closed, and the index type need not be countable. If no finite stage contains the
compact set, choose a sequence with distinct fresh exceptional coordinates. Each subset
of its range has finite, hence closed, preimage in every principal stage. Finality then
makes the range an infinite closed discrete subset of the compact set, a contradiction. -/
theorem exists_subset_cofiniteStage_of_t1 [T1Space (Πʳ i, [R i, A i])]
    {K : Set (Πʳ i, [R i, A i])} (hK : IsCompact K) :
    ∃ s : Finset ι, K ⊆ cofiniteStage (R := R) (A := A) s := by
  classical
  by_contra h
  have hw : ∀ s : Finset ι, ∃ x ∈ K, ∃ i, i ∉ s ∧ i ∈ exceptionalFinset x := by
    intro s
    have hs : ¬ K ⊆ cofiniteStage (R := R) (A := A) s := fun hs ↦ h ⟨s, hs⟩
    obtain ⟨x, hxK, hxs⟩ := Set.not_subset.mp hs
    simp only [mem_cofiniteStage, not_forall] at hxs
    obtain ⟨i, his, hbad⟩ := hxs
    exact ⟨x, hxK, i, his, mem_exceptionalFinset.mpr hbad⟩
  obtain ⟨f, c, hfK, hf, hc, hbad⟩ := exists_sequence_fresh_exceptional hw
  have hclosed : ∀ D : Set (Πʳ i, [R i, A i]), D ⊆ Set.range f → IsClosed D :=
    fun _ hD ↦ isClosed_of_subset_range_exceptional hc hbad hD
  have hcompact : IsCompact (Set.range f) :=
    hK.of_isClosed_subset (hclosed _ (fun _ hx ↦ hx)) (Set.range_subset_iff.mpr hfK)
  have hdiscrete : IsDiscrete (Set.range f) := by
    refine ⟨discreteTopology_iff_forall_isClosed.mpr ?_⟩
    intro E
    have hE : IsClosed ((Subtype.val : Set.range f → Πʳ i, [R i, A i]) '' E) :=
      hclosed _ (by rintro _ ⟨x, _, rfl⟩; exact x.2)
    have hpre : (Subtype.val : Set.range f → Πʳ i, [R i, A i]) ⁻¹'
        (Subtype.val '' E) = E := Set.preimage_image_eq E Subtype.val_injective
    rw [← hpre]
    exact hE.preimage continuous_subtype_val
  exact Set.infinite_range_of_injective hf (hcompact.finite hdiscrete)

end Topology

end RestrictedProduct
