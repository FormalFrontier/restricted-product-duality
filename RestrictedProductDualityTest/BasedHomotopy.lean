/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A real based homotopy on the full finite-support product

At every natural-number coordinate, the straight-line homotopy from the identity
to doubling fixes zero. On the singleton-cofinite restricted product, the point
with value one at coordinate zero and zero elsewhere has endpoint values one and
two at that coordinate. This distinguishes the endpoint maps, not homotopy classes.

The coordinate homotopy is Mathlib's affine homotopy, evaluated through its
straight-line formula. All real topology and algebra instances are the usual ones.
-/

-- The examples in this module are intentionally private.
set_option linter.privateModule false

set_option warningAsError true

noncomputable section

open Set
open scoped unitInterval

namespace RestrictedProductTest.BasedHomotopy

open RestrictedProduct RestrictedProduct.SingletonPathComponents
open RestrictedProduct.SingletonNaturality

private def realBase : ℕ → ℝ := fun _ ↦ 0

private def identityMap : C(ℝ, ℝ) := ContinuousMap.id ℝ

private def doublingMap : C(ℝ, ℝ) := ContinuousMap.mulLeft (2 : ℝ)

private theorem identity_based : identityMap 0 = 0 := rfl

private theorem doubling_based : doublingMap 0 = 0 := by
  change (2 : ℝ) * 0 = 0
  exact mul_zero 2

/-- The closed coordinate input is the stock affine homotopy, fixing zero all the time. -/
private def coordinateHomotopy :
    ContinuousMap.HomotopyRel identityMap doublingMap ({0} : Set ℝ) where
  toHomotopy := ContinuousMap.Homotopy.affine identityMap doublingMap
  prop' := by
    intro t x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    change Path.segment (0 : ℝ) ((2 : ℝ) * 0) t = 0
    simp

/-- The stock straight-line formula is the scalar formula at every time and input. -/
private theorem coordinateHomotopy_apply (t : I) (x : ℝ) :
    coordinateHomotopy (t, x) = (1 + (t : ℝ)) * x := by
  change AffineMap.lineMap x ((2 : ℝ) * x) (t : ℝ) = _
  rw [AffineMap.lineMap_apply_ring]
  ring

private def productHomotopy :
    ContinuousMap.HomotopyRel
      (pointMap realBase realBase (fun _ ↦ identityMap) (fun _ ↦ identity_based))
      (pointMap realBase realBase (fun _ ↦ doublingMap) (fun _ ↦ doubling_based))
      ({singletonBasepoint realBase} : Set (PointProduct realBase)) :=
  pointMapHomotopyRel realBase realBase (fun _ ↦ identityMap) (fun _ ↦ doublingMap)
    (fun _ ↦ identity_based) (fun _ ↦ doubling_based) (fun _ ↦ coordinateHomotopy)

/-- A closed point of the full restricted product, not the unsupported constant-one family. -/
private def oneAtZero : PointProduct realBase :=
  singletonFinsetInsert realBase ({0} : Finset ℕ) (fun _ ↦ (1 : ℝ))

private theorem oneAtZero_zero : oneAtZero 0 = 1 :=
  singletonFinsetInsert_apply_of_mem realBase {0} (fun _ ↦ (1 : ℝ)) 0
    (Finset.mem_singleton.mpr rfl)

/-- The global evaluation API computes every coordinate, not only the chosen witness. -/
private theorem productHomotopy_apply (t : I) (x : PointProduct realBase) (n : ℕ) :
    productHomotopy (t, x) n = (1 + (t : ℝ)) * x n :=
  (pointMapHomotopyRel_apply realBase realBase (fun _ ↦ identityMap) (fun _ ↦ doublingMap)
    (fun _ ↦ identity_based) (fun _ ↦ doubling_based) (fun _ ↦ coordinateHomotopy) t x n).trans
    (coordinateHomotopy_apply t (x n))

private theorem model_coordinate (t : I) :
    productHomotopy (t, oneAtZero) 0 = 1 + (t : ℝ) := by
  rw [productHomotopy_apply, oneAtZero_zero, mul_one]

/-- The same closed finite-support input has coordinate-zero endpoint values one and two. -/
private theorem model_endpoints :
    productHomotopy (0, oneAtZero) 0 = 1 ∧ productHomotopy (1, oneAtZero) 0 = 2 := by
  exact ⟨(model_coordinate (0 : I)).trans (by norm_num),
    (model_coordinate (1 : I)).trans (by norm_num)⟩

private theorem model_nonconstant :
    productHomotopy (0, oneAtZero) 0 ≠ productHomotopy (1, oneAtZero) 0 := by
  rw [model_endpoints.1, model_endpoints.2]
  norm_num

/-- The model uses the same canonical point at every time. -/
private theorem productHomotopy_based (t : I) :
    productHomotopy (t, singletonBasepoint realBase) = singletonBasepoint realBase :=
  pointMapHomotopyRel_base realBase realBase (fun _ ↦ identityMap) (fun _ ↦ doublingMap)
    (fun _ ↦ identity_based) (fun _ ↦ doubling_based) (fun _ ↦ coordinateHomotopy) t

private theorem model_pathMap_eq :
    pathMap (pointMap realBase realBase (fun _ ↦ identityMap) (fun _ ↦ identity_based)) =
      pathMap (pointMap realBase realBase (fun _ ↦ doublingMap) (fun _ ↦ doubling_based)) :=
  pathMap_pointMap_eq_of_homotopyRel realBase realBase
    (fun _ ↦ identityMap) (fun _ ↦ doublingMap)
    (fun _ ↦ identity_based) (fun _ ↦ doubling_based) (fun _ ↦ coordinateHomotopy)

private theorem model_homotopyGroup_map_eq :
    HomotopyGroup.map (Fin 1)
        (pointMap realBase realBase (fun _ ↦ identityMap) (fun _ ↦ identity_based))
        (pointMap_base realBase realBase (fun _ ↦ identityMap) (fun _ ↦ identity_based)) =
      HomotopyGroup.map (Fin 1)
        (pointMap realBase realBase (fun _ ↦ doublingMap) (fun _ ↦ doubling_based))
        (pointMap_base realBase realBase (fun _ ↦ doublingMap) (fun _ ↦ doubling_based)) :=
  homotopyGroup_map_pointMap_eq_of_homotopyRel (Fin 1) realBase realBase
    (fun _ ↦ identityMap) (fun _ ↦ doublingMap)
    (fun _ ↦ identity_based) (fun _ ↦ doubling_based) (fun _ ↦ coordinateHomotopy)

/-- The construction also accepts an empty family, without a nonempty-index hypothesis. -/
private theorem empty_index_based (t : I) :
    pointMapHomotopyRel (fun _ : Empty ↦ (0 : ℝ)) (fun _ : Empty ↦ (0 : ℝ))
        (fun _ ↦ identityMap) (fun _ ↦ doublingMap)
        (fun _ ↦ identity_based) (fun _ ↦ doubling_based) (fun _ ↦ coordinateHomotopy)
        (t, singletonBasepoint (fun _ : Empty ↦ (0 : ℝ))) =
      singletonBasepoint (fun _ : Empty ↦ (0 : ℝ)) :=
  pointMapHomotopyRel_base (fun _ : Empty ↦ (0 : ℝ)) (fun _ : Empty ↦ (0 : ℝ))
    (fun _ ↦ identityMap) (fun _ ↦ doublingMap)
    (fun _ ↦ identity_based) (fun _ ↦ doubling_based) (fun _ ↦ coordinateHomotopy) t

end RestrictedProductTest.BasedHomotopy
