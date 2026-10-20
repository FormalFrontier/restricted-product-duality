/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Ring

/-!
# Dilation and halving on finite-support real families

At zero-based real coordinates, doubling and halving have constant-time identity
inverse homotopies. The induced homotopy equivalence acts on the full
singleton-cofinite restricted product over the natural numbers. On the point one
at coordinate zero and zero elsewhere, the forward coordinate is two and the
backward coordinate is one half. The same inputs also give the empty-index case.
All real topology and algebra instances are the usual ones.
-/

@[expose] public section

-- The examples in this module are intentionally private.
set_option linter.privateModule false

set_option warningAsError true

noncomputable section

open Set

universe u

namespace RestrictedProductTest.HomotopyEquivalences

open RestrictedProduct RestrictedProduct.SingletonPathComponents
open RestrictedProduct.SingletonNaturality

private def realBase (ι : Type u) : ι → ℝ := fun _ ↦ 0

private def doublingMap : C(ℝ, ℝ) := ContinuousMap.mulLeft (2 : ℝ)

private def halvingMap : C(ℝ, ℝ) where
  toFun := fun x ↦ x / 2
  continuous_toFun := by fun_prop

private theorem doubling_based : doublingMap 0 = 0 := by
  change (2 : ℝ) * 0 = 0
  exact mul_zero 2

private theorem halving_based : halvingMap 0 = 0 := by
  change (0 : ℝ) / 2 = 0
  exact zero_div 2

/-- The coordinate left inverse homotopy is the identity, constant in time. -/
private def halveDoubleHomotopy :
    ContinuousMap.HomotopyRel (halvingMap.comp doublingMap)
      (ContinuousMap.id ℝ) ({0} : Set ℝ) where
  toHomotopy :=
    { toFun := fun p ↦ p.2
      continuous_toFun := continuous_snd
      map_zero_left := by
        intro x
        change x = (2 * x) / 2
        ring
      map_one_left := fun _ ↦ rfl }
  prop' := by
    intro _ x _
    change x = (2 * x) / 2
    ring

/-- The coordinate right inverse homotopy is the identity, constant in time. -/
private def doubleHalveHomotopy :
    ContinuousMap.HomotopyRel (doublingMap.comp halvingMap)
      (ContinuousMap.id ℝ) ({0} : Set ℝ) where
  toHomotopy :=
    { toFun := fun p ↦ p.2
      continuous_toFun := continuous_snd
      map_zero_left := by
        intro x
        change x = 2 * (x / 2)
        ring
      map_one_left := fun _ ↦ rfl }
  prop' := by
    intro _ x _
    change x = 2 * (x / 2)
    ring

private def dilationEquiv (ι : Type u) :
    ContinuousMap.HomotopyEquiv (PointProduct (realBase ι)) (PointProduct (realBase ι)) :=
  pointMapHomotopyEquiv (realBase ι) (realBase ι)
    (fun _ ↦ doublingMap) (fun _ ↦ halvingMap)
    (fun _ ↦ doubling_based) (fun _ ↦ halving_based)
    (fun _ ↦ halveDoubleHomotopy) (fun _ ↦ doubleHalveHomotopy)

private def oneAtZero : PointProduct (realBase ℕ) :=
  singletonFinsetInsert (realBase ℕ) ({0} : Finset ℕ) (fun _ ↦ (1 : ℝ))

private theorem oneAtZero_zero : oneAtZero 0 = 1 :=
  singletonFinsetInsert_apply_of_mem (realBase ℕ) {0} (fun _ ↦ (1 : ℝ)) 0
    (Finset.mem_singleton.mpr rfl)

/-- A downstream coordinate computation using the public forward API. -/
private theorem dilation_coordinate (x : PointProduct (realBase ℕ)) (n : ℕ) :
    dilationEquiv ℕ x n = 2 * x n :=
  pointMapHomotopyEquiv_apply (realBase ℕ) (realBase ℕ)
    (fun _ ↦ doublingMap) (fun _ ↦ halvingMap)
    (fun _ ↦ doubling_based) (fun _ ↦ halving_based)
    (fun _ ↦ halveDoubleHomotopy) (fun _ ↦ doubleHalveHomotopy) x n

/-- A downstream coordinate computation using the public inverse API. -/
private theorem halving_coordinate (x : PointProduct (realBase ℕ)) (n : ℕ) :
    (dilationEquiv ℕ).symm x n = x n / 2 :=
  pointMapHomotopyEquiv_symm_apply (realBase ℕ) (realBase ℕ)
    (fun _ ↦ doublingMap) (fun _ ↦ halvingMap)
    (fun _ ↦ doubling_based) (fun _ ↦ halving_based)
    (fun _ ↦ halveDoubleHomotopy) (fun _ ↦ doubleHalveHomotopy) x n

/-- One finite-support input distinguishes the two nonconstant coordinate maps. -/
private theorem dilation_values :
    dilationEquiv ℕ oneAtZero 0 = 2 ∧ (dilationEquiv ℕ).symm oneAtZero 0 = 1 / 2 := by
  constructor
  · rw [dilation_coordinate, oneAtZero_zero, mul_one]
  · rw [halving_coordinate, oneAtZero_zero]

/-- The same closed coordinate data supplies the empty-index boundary. -/
private theorem empty_index_based :
    dilationEquiv Empty (singletonBasepoint (realBase Empty)) =
      singletonBasepoint (realBase Empty) :=
  pointMapHomotopyEquiv_base (realBase Empty) (realBase Empty)
    (fun _ ↦ doublingMap) (fun _ ↦ halvingMap)
    (fun _ ↦ doubling_based) (fun _ ↦ halving_based)
    (fun _ ↦ halveDoubleHomotopy) (fun _ ↦ doubleHalveHomotopy)

end RestrictedProductTest.HomotopyEquivalences
