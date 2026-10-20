/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.BasedHomotopy
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences of singleton restricted products

Based continuous coordinate maps with inverse homotopies relative to the chosen
points induce a homotopy equivalence of the singleton-cofinite restricted products.
Its forward and backward maps are the coordinatewise maps `pointMap`. The inverse
homotopies are assembled by `pointMapHomotopyRel`, using the given coordinate
homotopies at the same time parameter.

The factor topologies are arbitrary and the index type may be empty. All restricted
products carry their canonical final topology; no separation, local compactness,
countability or CW structure on the factors is required.

## References

This construction uses Mathlib's `ContinuousMap.HomotopyEquiv` and relative homotopies
(Shing Tak Lam), and the based restricted-product maps and homotopies of this library.
Mathlib's `HomotopyEquiv.piCongrRight` concerns the full ordinary product, rather than
these singleton-cofinite restricted products.
-/

@[expose] public section

noncomputable section

open Set

universe u v w

namespace RestrictedProduct.SingletonNaturality

open RestrictedProduct.SingletonPathComponents

variable {ι : Type u} {X : ι → Type v} {Y : ι → Type w}
variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
variable (b : ∀ i, X i) (c : ∀ i, Y i)
variable (f : ∀ i, C(X i, Y i)) (g : ∀ i, C(Y i, X i))
variable (hf : ∀ i, f i (b i) = c i) (hg : ∀ i, g i (c i) = b i)

/-- The coordinate left inverse homotopies, assembled relative to the canonical
source point. Endpoint casts change only the endpoint labels of the homotopy. -/
private def pointMapLeftInverseHomotopyRel
    (Hgf : ∀ i, ContinuousMap.HomotopyRel ((g i).comp (f i))
      (ContinuousMap.id (X i)) ({b i} : Set (X i))) :
    ContinuousMap.HomotopyRel
      ((pointMap c b g hg).comp (pointMap b c f hf))
      (ContinuousMap.id (PointProduct b))
      ({RestrictedProduct.singletonBasepoint b} : Set (PointProduct b)) :=
  ContinuousMap.HomotopyRel.cast
    (pointMapHomotopyRel b b (fun i ↦ (g i).comp (f i))
      (fun i ↦ ContinuousMap.id (X i))
      (fun i ↦ (congrArg (g i) (hf i)).trans (hg i)) (fun _ ↦ rfl) Hgf)
    (pointMap_comp b c b g hg f hf) (pointMap_id b)

/-- The coordinate right inverse homotopies, assembled relative to the canonical
target point. Endpoint casts change only the endpoint labels of the homotopy. -/
private def pointMapRightInverseHomotopyRel
    (Hfg : ∀ i, ContinuousMap.HomotopyRel ((f i).comp (g i))
      (ContinuousMap.id (Y i)) ({c i} : Set (Y i))) :
    ContinuousMap.HomotopyRel
      ((pointMap b c f hf).comp (pointMap c b g hg))
      (ContinuousMap.id (PointProduct c))
      ({RestrictedProduct.singletonBasepoint c} : Set (PointProduct c)) :=
  ContinuousMap.HomotopyRel.cast
    (pointMapHomotopyRel c c (fun i ↦ (f i).comp (g i))
      (fun i ↦ ContinuousMap.id (Y i))
      (fun i ↦ (congrArg (f i) (hg i)).trans (hf i)) (fun _ ↦ rfl) Hfg)
    (pointMap_comp c b c f hf g hg) (pointMap_id c)

variable (Hgf : ∀ i, ContinuousMap.HomotopyRel ((g i).comp (f i))
  (ContinuousMap.id (X i)) ({b i} : Set (X i)))
variable (Hfg : ∀ i, ContinuousMap.HomotopyRel ((f i).comp (g i))
  (ContinuousMap.id (Y i)) ({c i} : Set (Y i)))

/-- The homotopy equivalence induced by based coordinate maps and their relative
inverse homotopies. Both maps are the existing continuous restricted-product maps. -/
def pointMapHomotopyEquiv : ContinuousMap.HomotopyEquiv (PointProduct b) (PointProduct c) where
  toFun := pointMap b c f hf
  invFun := pointMap c b g hg
  left_inv := by
    have H := pointMapLeftInverseHomotopyRel b c f g hf hg Hgf
    exact ⟨H.toHomotopy⟩
  right_inv := by
    have H := pointMapRightInverseHomotopyRel b c f g hf hg Hfg
    exact ⟨H.toHomotopy⟩

/-- The forward continuous map of the equivalence is `pointMap`. -/
@[simp]
theorem pointMapHomotopyEquiv_toFun :
    (pointMapHomotopyEquiv b c f g hf hg Hgf Hfg).toFun = pointMap b c f hf := by
  rfl

/-- The backward continuous map of the equivalence is `pointMap` for the inverse family. -/
@[simp]
theorem pointMapHomotopyEquiv_symm_toFun :
    (pointMapHomotopyEquiv b c f g hf hg Hgf Hfg).symm.toFun = pointMap c b g hg := by
  rfl

/-- Evaluation of the forward equivalence at any coordinate. -/
@[simp]
theorem pointMapHomotopyEquiv_apply (x : PointProduct b) (i : ι) :
    pointMapHomotopyEquiv b c f g hf hg Hgf Hfg x i = f i (x i) := by
  calc
    _ = pointMap b c f hf x i :=
      congrArg (fun h : C(PointProduct b, PointProduct c) ↦ h x i)
        (pointMapHomotopyEquiv_toFun b c f g hf hg Hgf Hfg)
    _ = f i (x i) := pointMap_apply b c f hf x i

/-- Evaluation of the inverse equivalence at any coordinate. -/
@[simp]
theorem pointMapHomotopyEquiv_symm_apply (y : PointProduct c) (i : ι) :
    (pointMapHomotopyEquiv b c f g hf hg Hgf Hfg).symm y i = g i (y i) := by
  calc
    _ = pointMap c b g hg y i :=
      congrArg (fun h : C(PointProduct c, PointProduct b) ↦ h y i)
        (pointMapHomotopyEquiv_symm_toFun b c f g hf hg Hgf Hfg)
    _ = g i (y i) := pointMap_apply c b g hg y i

/-- The equivalence preserves the canonical chosen point. -/
@[simp]
theorem pointMapHomotopyEquiv_base :
    pointMapHomotopyEquiv b c f g hf hg Hgf Hfg (RestrictedProduct.singletonBasepoint b) =
      RestrictedProduct.singletonBasepoint c := by
  calc
    _ = pointMap b c f hf (RestrictedProduct.singletonBasepoint b) :=
      congrArg (fun h : C(PointProduct b, PointProduct c) ↦
        h (RestrictedProduct.singletonBasepoint b))
        (pointMapHomotopyEquiv_toFun b c f g hf hg Hgf Hfg)
    _ = RestrictedProduct.singletonBasepoint c := pointMap_base b c f hf

/-- The inverse equivalence preserves the canonical chosen point. -/
@[simp]
theorem pointMapHomotopyEquiv_symm_base :
    (pointMapHomotopyEquiv b c f g hf hg Hgf Hfg).symm
        (RestrictedProduct.singletonBasepoint c) = RestrictedProduct.singletonBasepoint b := by
  calc
    _ = pointMap c b g hg (RestrictedProduct.singletonBasepoint c) :=
      congrArg (fun h : C(PointProduct c, PointProduct b) ↦
        h (RestrictedProduct.singletonBasepoint c))
        (pointMapHomotopyEquiv_symm_toFun b c f g hf hg Hgf Hfg)
    _ = RestrictedProduct.singletonBasepoint b := pointMap_base c b g hg

end RestrictedProduct.SingletonNaturality
