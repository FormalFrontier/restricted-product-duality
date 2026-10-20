/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.PathComponents
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Connectivity of singleton cofinite restricted products

For a given family of chosen points, path connectedness and local path connectedness
of the singleton cofinite restricted product are characterized by the corresponding
properties of its factors. The topology is Mathlib's final restricted-product topology,
with the ordinary Pi topology on each finite stage.

Coordinate evaluation and evaluation from the topological sum of finite stages are
quotient maps. The path-connectedness comparison uses the coordinatewise path criterion
`RestrictedProduct.SingletonPathComponents.joined_iff`. Local path connectedness descends
from the sum of finite products along the finite-stage evaluation map, and descends to
each factor along coordinate evaluation.

## References

Mathlib's restricted products (Anatole Dedecker), path-connected spaces (Patrick Massot
and subsequent contributors), and locally path-connected spaces (Patrick Massot,
Ben Eltschig and subsequent contributors) supply the topologies and connectivity API.
Finite insertion and finality are reused from `RestrictedProductDuality.PrincipalStage`.
The finite-support-product viewpoint occurs in J. P. May,
*A Concise Course in Algebraic Topology*.
-/

@[expose] public section

universe u v

namespace RestrictedProduct.SingletonPathComponents

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- Coordinate evaluation from the singleton cofinite restricted product is a quotient map. -/
theorem isQuotientMap_eval (b : ∀ i, X i) (i : ι) :
    Topology.IsQuotientMap (fun x : PointProduct b ↦ x i) := by
  classical
  let toSingleton : X i → ∀ j : ({i} : Finset ι), X j :=
    fun z j ↦ (Finset.mem_singleton.mp j.2).symm ▸ z
  have htoSingleton : Continuous toSingleton := by
    apply continuous_pi
    intro j
    have hj : j = ⟨i, Finset.mem_singleton_self i⟩ :=
      Subtype.ext (Finset.mem_singleton.mp j.2)
    subst j
    change Continuous (fun z : X i ↦ z)
    exact continuous_id
  refine Topology.IsQuotientMap.of_inverse
    ((continuous_singletonFinsetInsert b {i}).comp htoSingleton)
    (RestrictedProduct.continuous_eval i) ?_
  intro z
  change singletonFinsetInsert b {i} (toSingleton z) i = z
  simpa only [toSingleton] using
    (singletonFinsetInsert_apply_of_mem b {i} (toSingleton z) i
      (Finset.mem_singleton_self i))

/-- Evaluation from the topological sum of ordinary finite products is a quotient map
onto the singleton cofinite restricted product. -/
theorem isQuotientMap_sigmaFinsetInsert (b : ∀ i, X i) :
    Topology.IsQuotientMap
      (fun p : (Σ s : Finset ι, ∀ j : s, X j) ↦ singletonFinsetInsert b p.1 p.2) := by
  refine ⟨Topology.isCoinducing_iff.mpr (fun U ↦ ?_), ?_⟩
  · calc
      IsOpen ((fun p : (Σ s : Finset ι, ∀ j : s, X j) ↦
          singletonFinsetInsert b p.1 p.2) ⁻¹' U) ↔
          ∀ s : Finset ι, IsOpen (singletonFinsetInsert b s ⁻¹' U) :=
        isOpen_sigma_iff
      _ ↔ ∀ s : Finset ι,
          Continuous ((fun x : PointProduct b ↦ x ∈ U) ∘ singletonFinsetInsert b s) :=
        forall_congr' fun _ ↦ isOpen_iff_continuous_mem
      _ ↔ Continuous (fun x : PointProduct b ↦ x ∈ U) :=
        (continuous_dom_singleton_iff b).symm
      _ ↔ IsOpen U := isOpen_iff_continuous_mem.symm
  · intro x
    refine ⟨⟨exceptionalFinset x, (exceptionalFinset x).restrict (fun i ↦ x i)⟩, ?_⟩
    exact singletonFinsetInsert_restrict b (exceptionalFinset x) x
      (mem_cofiniteStage_exceptionalFinset x)

/-- The singleton cofinite restricted product is path connected exactly when every factor is
path connected. The chosen points provide nonemptiness, including for an empty index type. -/
theorem pathConnectedSpace_iff (b : ∀ i, X i) :
    PathConnectedSpace (PointProduct b) ↔ ∀ i, PathConnectedSpace (X i) := by
  constructor
  · intro h i
    let : PathConnectedSpace (PointProduct b) := h
    exact (isQuotientMap_eval b i).surjective.pathConnectedSpace
      (RestrictedProduct.continuous_eval i)
  · intro h
    let : ∀ i, PathConnectedSpace (X i) := h
    exact ⟨⟨singletonFinsetInsert b ∅ (fun j ↦ b j)⟩,
      fun x y ↦ (joined_iff b x y).mpr (fun i ↦ PathConnectedSpace.joined (x i) (y i))⟩

/-- Path connectedness of the factors is preserved by the singleton cofinite restricted product. -/
instance instPathConnectedSpace (b : ∀ i, X i) [∀ i, PathConnectedSpace (X i)] :
    PathConnectedSpace (PointProduct b) := by
  exact (pathConnectedSpace_iff b).mpr (fun _ ↦ inferInstance)

/-- The singleton cofinite restricted product is locally path connected exactly when every factor
is locally path connected, without requiring path connectedness of the factors. -/
theorem locallyPathConnectedSpace_iff (b : ∀ i, X i) :
    LocallyPathConnectedSpace (PointProduct b) ↔ ∀ i, LocallyPathConnectedSpace (X i) := by
  constructor
  · intro h i
    let : LocallyPathConnectedSpace (PointProduct b) := h
    exact (isQuotientMap_eval b i).locallyPathConnectedSpace
  · intro h
    let : ∀ i, LocallyPathConnectedSpace (X i) := h
    let : ∀ s : Finset ι, LocallyPathConnectedSpace (∀ j : s, X j) :=
      fun s ↦ Pi.locallyPathConnectedSpace_of_finite
    let : LocallyPathConnectedSpace (Σ s : Finset ι, ∀ j : s, X j) :=
      Sigma.locallyPathConnectedSpace
    exact (isQuotientMap_sigmaFinsetInsert b).locallyPathConnectedSpace

/-- Local path connectedness of the factors is preserved by the singleton cofinite restricted
product with its final finite-stage topology. -/
instance instLocallyPathConnectedSpace (b : ∀ i, X i) [∀ i, LocallyPathConnectedSpace (X i)] :
    LocallyPathConnectedSpace (PointProduct b) := by
  exact (locallyPathConnectedSpace_iff b).mpr (fun _ ↦ inferInstance)

end RestrictedProduct.SingletonPathComponents
