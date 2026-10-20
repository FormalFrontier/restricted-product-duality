/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Real finite-support contractions

The straight-line contraction of the usual real line to zero fixes zero. Its
coordinatewise contraction on the natural-number singleton-cofinite restricted
product takes the finite insertion of one at zero to the canonical zero point.
The same construction includes the empty index type.

The real homotopy is Mathlib's `ContinuousMap.Homotopy.affine`, whose value is
`Path.segment x 0 t`, or equivalently `(1 - (t : ℝ)) * x`.
-/

noncomputable section

open scoped unitInterval

namespace RestrictedProductTest.Contractibility

open RestrictedProduct RestrictedProduct.SingletonPathComponents
open RestrictedProduct.SingletonNaturality

private def realBase : ℕ → ℝ := fun _ ↦ 0

private def realContraction :
    ContinuousMap.HomotopyRel (ContinuousMap.id ℝ) (ContinuousMap.const ℝ (0 : ℝ))
      ({0} : Set ℝ) :=
  ContinuousMap.HomotopyWith.mk
    (ContinuousMap.Homotopy.affine (ContinuousMap.id ℝ) (ContinuousMap.const ℝ (0 : ℝ)))
    (by
      intro t x hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst x
      change Path.segment (0 : ℝ) 0 t = 0
      simp)

private theorem realContraction_apply (t : I) (x : ℝ) :
    realContraction (t, x) = (1 - (t : ℝ)) * x := by
  change AffineMap.lineMap x (0 : ℝ) (t : ℝ) = _
  simp only [AffineMap.lineMap_apply_ring, mul_zero, add_zero]

private def productContraction :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PointProduct realBase))
      (ContinuousMap.const (PointProduct realBase) (singletonBasepoint realBase))
      ({singletonBasepoint realBase} : Set (PointProduct realBase)) :=
  pointContraction realBase (fun _ ↦ realContraction)

/-- The finite insertion has value one at zero and default value zero elsewhere. -/
private def oneAtZero : PointProduct realBase :=
  singletonFinsetInsert realBase ({0} : Finset ℕ) (fun _ ↦ (1 : ℝ))

private theorem oneAtZero_apply (n : ℕ) :
    oneAtZero n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · rw [if_pos hn]
    exact singletonFinsetInsert_apply_of_mem realBase {0} (fun _ ↦ (1 : ℝ)) n
      (Finset.mem_singleton.mpr hn)
  · rw [if_neg hn]
    exact singletonFinsetInsert_apply_of_notMem realBase {0} (fun _ ↦ (1 : ℝ)) n
      (fun hn' ↦ hn (Finset.mem_singleton.mp hn'))

private theorem productContraction_apply (t : I) (x : PointProduct realBase) (n : ℕ) :
    productContraction (t, x) n = (1 - (t : ℝ)) * x n := by
  exact (pointContraction_apply realBase (fun _ ↦ realContraction) t x n).trans
    (realContraction_apply t (x n))

private theorem oneAtZero_contraction (t : I) :
    productContraction (t, oneAtZero) 0 = 1 - (t : ℝ) ∧
      ∀ n : ℕ, n ≠ 0 → productContraction (t, oneAtZero) n = 0 := by
  constructor
  · rw [productContraction_apply, oneAtZero_apply, if_pos rfl, mul_one]
  · intro n hn
    rw [productContraction_apply, oneAtZero_apply, if_neg hn, mul_zero]

private theorem oneAtZero_endpoints :
    productContraction (0, oneAtZero) 0 = 1 ∧
      productContraction (1, oneAtZero) 0 = 0 := by
  constructor
  · calc
      productContraction (0, oneAtZero) 0 = oneAtZero 0 :=
        congrArg (fun x : PointProduct realBase ↦ x 0) (productContraction.apply_zero oneAtZero)
      _ = 1 := by rw [oneAtZero_apply, if_pos rfl]
  · simpa only [ContinuousMap.const_apply, singletonBasepoint_apply, realBase] using
      congrArg (fun x : PointProduct realBase ↦ x 0) (productContraction.apply_one oneAtZero)

private theorem productContraction_fixed (t : I) :
    productContraction (t, singletonBasepoint realBase) = singletonBasepoint realBase := by
  exact productContraction.eq_fst t (by rfl)

private theorem realProduct_contractibleSpace : ContractibleSpace (PointProduct realBase) := by
  exact contractibleSpace_of_basedContractions realBase (fun _ ↦ realContraction)

private def emptyBase : Empty → ℝ := fun _ ↦ 0

private def emptyContraction :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PointProduct emptyBase))
      (ContinuousMap.const (PointProduct emptyBase) (singletonBasepoint emptyBase))
      ({singletonBasepoint emptyBase} : Set (PointProduct emptyBase)) :=
  pointContraction emptyBase (fun _ ↦ realContraction)

private theorem emptyContraction_fixed (t : I) :
    emptyContraction (t, singletonBasepoint emptyBase) = singletonBasepoint emptyBase := by
  exact emptyContraction.eq_fst t (by rfl)

private theorem emptyProduct_contractibleSpace : ContractibleSpace (PointProduct emptyBase) := by
  exact contractibleSpace_of_basedContractions emptyBase (fun _ ↦ realContraction)

end RestrictedProductTest.Contractibility
