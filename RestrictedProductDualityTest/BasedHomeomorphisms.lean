/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.NormNum

/-!
# Dilation on the real finite-support product

Mathlib's homeomorphism given by multiplication by two fixes zero and has inverse
halving. Applying it at every natural-number coordinate gives a homeomorphism of
the full singleton-cofinite restricted product. The point with coordinate zero
equal to one and every other coordinate zero is sent to a point with coordinate
zero equal to two; its inverse image has coordinate zero equal to one half.
These are statements about points and maps, not about nonzero homotopy classes.

The examples use the characteristic API without unfolding the product
homeomorphism. The empty-index boundary uses the same construction.
-/

-- The examples in this module are intentionally private.

set_option warningAsError true

noncomputable section

namespace RestrictedProductTest.BasedHomeomorphisms

open RestrictedProduct RestrictedProduct.SingletonPathComponents
open RestrictedProduct.SingletonNaturality

private def realBase : ℕ → ℝ := fun _ ↦ 0

private def dilation : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ (2 : ℝ) (by norm_num)

private theorem dilation_apply (x : ℝ) : dilation x = 2 * x := rfl

private theorem dilation_symm_apply (x : ℝ) : dilation.symm x = x / 2 := by
  change (2 : ℝ)⁻¹ * x = x / 2
  rw [div_eq_mul_inv, mul_comm]

private theorem dilation_based : dilation 0 = 0 := by
  exact (dilation_apply 0).trans (mul_zero 2)

private def productDilation : PointProduct realBase ≃ₜ PointProduct realBase :=
  pointMapHomeomorph realBase realBase (fun _ ↦ dilation) (fun _ ↦ dilation_based)

/-- A point of the full restricted product supported on the singleton coordinate zero. -/
private def oneAtZero : PointProduct realBase :=
  singletonFinsetInsert realBase ({0} : Finset ℕ) (fun _ ↦ (1 : ℝ))

private theorem oneAtZero_zero : oneAtZero 0 = 1 :=
  singletonFinsetInsert_apply_of_mem realBase {0} (fun _ ↦ (1 : ℝ)) 0
    (Finset.mem_singleton.mpr rfl)

private theorem oneAtZero_of_ne_zero (n : ℕ) (hn : n ≠ 0) : oneAtZero n = 0 :=
  singletonFinsetInsert_apply_of_notMem realBase {0} (fun _ ↦ (1 : ℝ)) n
    (fun h ↦ hn (Finset.mem_singleton.mp h))

private theorem productDilation_apply (x : PointProduct realBase) (n : ℕ) :
    productDilation x n = 2 * x n :=
  (pointMapHomeomorph_apply realBase realBase (fun _ ↦ dilation)
    (fun _ ↦ dilation_based) x n).trans (dilation_apply (x n))

private theorem productDilation_symm_apply (x : PointProduct realBase) (n : ℕ) :
    productDilation.symm x n = x n / 2 :=
  (pointMapHomeomorph_symm_apply realBase realBase (fun _ ↦ dilation)
    (fun _ ↦ dilation_based) x n).trans (dilation_symm_apply (x n))

/-- The same finite-support input distinguishes both directions from the identity. -/
private theorem model_coordinates :
    productDilation oneAtZero 0 = 2 ∧ productDilation.symm oneAtZero 0 = 1 / 2 := by
  constructor
  · rw [productDilation_apply, oneAtZero_zero, mul_one]
  · rw [productDilation_symm_apply, oneAtZero_zero]

private theorem model_nonconstant :
    productDilation oneAtZero ≠ productDilation (singletonBasepoint realBase) := by
  intro h
  have hzero := congrArg (fun x : PointProduct realBase ↦ x 0) h
  rw [model_coordinates.1, productDilation_apply, singletonBasepoint_apply] at hzero
  change (2 : ℝ) = 2 * 0 at hzero
  norm_num at hzero

/-- Both directions preserve the zero family under the usual real topologies. -/
private theorem model_based :
    productDilation (singletonBasepoint realBase) = singletonBasepoint realBase ∧
      productDilation.symm (singletonBasepoint realBase) = singletonBasepoint realBase :=
  ⟨pointMapHomeomorph_base realBase realBase (fun _ ↦ dilation) (fun _ ↦ dilation_based),
    pointMapHomeomorph_symm_base realBase realBase (fun _ ↦ dilation)
      (fun _ ↦ dilation_based)⟩

/-- No nonempty-index hypothesis is needed, even when the source and target
chosen points differ. -/
private theorem empty_index_based :
    pointMapHomeomorph (fun _ : Empty ↦ (0 : ℝ)) (fun _ : Empty ↦ (1 : ℝ))
        (fun _ ↦ Homeomorph.refl ℝ) (fun i ↦ nomatch i)
        (singletonBasepoint (fun _ : Empty ↦ (0 : ℝ))) =
      singletonBasepoint (fun _ : Empty ↦ (1 : ℝ)) :=
  pointMapHomeomorph_base (fun _ : Empty ↦ (0 : ℝ)) (fun _ : Empty ↦ (1 : ℝ))
    (fun _ ↦ Homeomorph.refl ℝ) (fun i ↦ nomatch i)

end RestrictedProductTest.BasedHomeomorphisms
