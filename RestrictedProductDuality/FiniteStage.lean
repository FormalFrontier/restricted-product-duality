/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.PrincipalStage
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Compact maps through ordinary finite stages

A continuous map from a compact space into a singleton cofinite restricted product
with T1 topology factors through an ordinary finite product. The factor is exactly
restriction of the original coordinate function to the chosen finite set.

This combines compact containment from `RestrictedProductDuality.CompactStage` with
the insertion and restriction API from `RestrictedProductDuality.PrincipalStage`.
All products carry the ordinary Pi topology. No comparison with compactly generated
products or their colimits is asserted.

## References

The restricted-product carrier, topology and inclusions are from Mathlib's
restricted-product formalization by Anatole Dedecker. The finite-support-product
viewpoint is that of J. P. May, *A Concise Course in Algebraic Topology*.
-/

@[expose] public section

open Filter Set Topology

universe u v w

namespace RestrictedProduct

variable {ι : Type u} {R : ι → Type v} [∀ i, TopologicalSpace (R i)]

/-- A continuous map from a compact space into a T1 singleton cofinite restricted
product factors through an ordinary finite product by finite coordinate restriction.

Only the restricted product itself is assumed T1. No separation of the factors,
openness of the singleton subsets, or nonemptiness of the domain is required. -/
theorem exists_singletonFinsetInsert_factorization (b : ∀ i, R i)
    {X : Type w} [TopologicalSpace X] [CompactSpace X]
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    {f : X → RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite}
    (hf : Continuous f) :
    ∃ s : Finset ι, ∃ g : C(X, ∀ i : s, R i),
      (∀ x, g x = s.restrict (fun i ↦ f x i)) ∧
      ∀ x, singletonFinsetInsert b s (g x) = f x := by
  obtain ⟨s, hs⟩ := exists_subset_cofiniteStage_of_t1 (isCompact_range hf)
  refine ⟨s, ⟨fun x ↦ s.restrict (fun i ↦ f x i),
    (Finset.continuous_restrict s).comp (continuous_coe.comp hf)⟩,
    (fun _ ↦ rfl), ?_⟩
  intro x
  exact singletonFinsetInsert_restrict b s (f x) (hs ⟨x, rfl⟩)

end RestrictedProduct
