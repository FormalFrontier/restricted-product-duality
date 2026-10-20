/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.HomotopyMaps

/-!
# Based homeomorphisms of singleton restricted products

Coordinate homeomorphisms carrying the chosen points to one another induce a
homeomorphism of the singleton-cofinite restricted products. Its forward and
inverse continuous maps are the existing coordinatewise `pointMap` constructions.
The characteristic API gives both continuous maps, their coordinate values, and
their values at the canonical points.

The factor topologies and the restricted products' final topologies are unchanged.
The index may be empty, and the source and target fibers have independent universes.
No separation, local compactness, or finiteness assumption is needed.

## References

This construction uses Mathlib's `Homeomorph` and continuous-map structures and
Anatole Dedecker's restricted products, together with this library's based
`pointMap`, `pointMap_id`, and `pointMap_comp` API. The finite-support-product
viewpoint occurs in J. P. May, *A Concise Course in Algebraic Topology*.
-/

@[expose] public section

noncomputable section

universe u v w

namespace RestrictedProduct.SingletonNaturality

open RestrictedProduct.SingletonPathComponents

variable {ι : Type u} {X : ι → Type v} {Y : ι → Type w}
variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

private theorem inverse_based (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i) :
    ∀ i, (e i).symm (c i) = b i :=
  fun i ↦ (congrArg (e i).symm (he i)).symm.trans ((e i).symm_apply_apply (b i))

/-- Coordinatewise based homeomorphisms induce a homeomorphism of the singleton
cofinite restricted products, with the canonical final topologies on both sides. -/
def pointMapHomeomorph (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i) :
    PointProduct b ≃ₜ PointProduct c where
  toFun := pointMap b c (fun i ↦ (e i : C(X i, Y i))) he
  invFun := pointMap c b (fun i ↦ ((e i).symm : C(Y i, X i))) (by exact inverse_based b c e he)
  left_inv := by
    intro x
    apply RestrictedProduct.ext
    intro i
    rw [pointMap_apply, pointMap_apply]
    exact (e i).symm_apply_apply (x i)
  right_inv := by
    intro y
    apply RestrictedProduct.ext
    intro i
    rw [pointMap_apply, pointMap_apply]
    exact (e i).apply_symm_apply (y i)
  continuous_toFun := (pointMap b c (fun i ↦ (e i : C(X i, Y i))) he).continuous
  continuous_invFun :=
    (pointMap c b (fun i ↦ ((e i).symm : C(Y i, X i))) (by exact inverse_based b c e he)).continuous

/-- The forward continuous map is the existing coordinatewise based map. -/
@[simp]
theorem pointMapHomeomorph_toContinuousMap (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i) :
    (pointMapHomeomorph b c e he : C(PointProduct b, PointProduct c)) =
      pointMap b c (fun i ↦ (e i : C(X i, Y i))) he := by
  rfl

/-- The inverse continuous map is the existing based map of the inverse coordinates;
its basedness follows from that of the forward family. -/
@[simp]
theorem pointMapHomeomorph_symm_toContinuousMap (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i) :
    ((pointMapHomeomorph b c e he).symm : C(PointProduct c, PointProduct b)) =
      pointMap c b (fun i ↦ ((e i).symm : C(Y i, X i)))
        (fun i ↦ (congrArg (e i).symm (he i)).symm.trans
          ((e i).symm_apply_apply (b i))) := by
  rfl

/-- Forward evaluation is the given coordinate homeomorphism at each index. -/
@[simp]
theorem pointMapHomeomorph_apply (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i)
    (x : PointProduct b) (i : ι) :
    pointMapHomeomorph b c e he x i = e i (x i) := by
  exact (congrArg (fun f : C(PointProduct b, PointProduct c) ↦ f x i)
    (pointMapHomeomorph_toContinuousMap b c e he)).trans
      (pointMap_apply b c (fun i ↦ (e i : C(X i, Y i))) he x i)

/-- Inverse evaluation is the inverse coordinate homeomorphism at each index. -/
@[simp]
theorem pointMapHomeomorph_symm_apply (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i)
    (y : PointProduct c) (i : ι) :
    (pointMapHomeomorph b c e he).symm y i = (e i).symm (y i) := by
  exact (congrArg (fun f : C(PointProduct c, PointProduct b) ↦ f y i)
    (pointMapHomeomorph_symm_toContinuousMap b c e he)).trans
      (pointMap_apply c b (fun i ↦ ((e i).symm : C(Y i, X i)))
        (inverse_based b c e he) y i)

/-- The forward homeomorphism preserves the canonical chosen points. -/
@[simp]
theorem pointMapHomeomorph_base (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i) :
    pointMapHomeomorph b c e he (RestrictedProduct.singletonBasepoint b) =
      RestrictedProduct.singletonBasepoint c := by
  exact (congrArg (fun f : C(PointProduct b, PointProduct c) ↦
    f (RestrictedProduct.singletonBasepoint b))
      (pointMapHomeomorph_toContinuousMap b c e he)).trans
        (pointMap_base b c (fun i ↦ (e i : C(X i, Y i))) he)

/-- The inverse homeomorphism preserves the canonical chosen points. -/
@[simp]
theorem pointMapHomeomorph_symm_base (b : ∀ i, X i) (c : ∀ i, Y i)
    (e : ∀ i, X i ≃ₜ Y i) (he : ∀ i, e i (b i) = c i) :
    (pointMapHomeomorph b c e he).symm (RestrictedProduct.singletonBasepoint c) =
      RestrictedProduct.singletonBasepoint b := by
  exact (congrArg (fun f : C(PointProduct c, PointProduct b) ↦
    f (RestrictedProduct.singletonBasepoint c))
      (pointMapHomeomorph_symm_toContinuousMap b c e he)).trans
        (pointMap_base c b (fun i ↦ ((e i).symm : C(Y i, X i)))
          (inverse_based b c e he))

end RestrictedProduct.SingletonNaturality
