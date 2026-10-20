/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.FiniteSupport
public import RestrictedProductDuality.HomotopyGroups

/-!
# Homotopy groups in finite-support coordinates

Compose the singleton restricted-product homotopy comparison directly with
`botMulEquivDFinsupp` on the bottom-subgroup restricted product, using its
original pointwise group operations. The cube index is an arbitrary nonempty
type with its given decidable equality, independent of the index and fiber universes.
The original singleton restricted product, its topology and basepoint, and its
T1 hypothesis are unchanged.

The group conventions are those of Mathlib's `HomotopyGroup`: the product of
classes of `p` and `q` is represented by `GenLoop.transAt j q p`. The inverse
comparison is characterized by coordinate classes, not by a definitional
finite-insertion formula. Class support need not equal the pointwise support
of any representative. No homotopy-group functoriality or classification is asserted.

## References

J. P. May, *A Concise Course in Algebraic Topology*, supplies the finite-support
product viewpoint. This module reuses the singleton comparison in
`RestrictedProductDuality.HomotopyGroups`, Mathlib's homotopy groups by Roberto
Alvarez, restricted products by Anatole Dedecker, dependent finitely supported
functions by Johannes Hölzl and Kenny Lau, and type tags by Mario Carneiro.
-/

@[expose] public section

noncomputable section

open Filter
open scoped RestrictedProduct

universe u v w

namespace RestrictedProduct

variable {ι : Type u} {R : ι → Type v} [∀ i, TopologicalSpace (R i)]
variable (N : Type w) [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
variable [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]

/-- Coordinate classes identify the homotopy group of a T1 singleton cofinite restricted
product with the multiplicative form of dependent finitely supported additive classes.
The construction composes the singleton comparison with `botMulEquivDFinsupp`
on the original bottom-subgroup restricted product. -/
def homotopyGroupSingletonMulEquivDFinsupp :
    HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b) ≃*
      Multiplicative (DFinsupp (fun i ↦ Additive (HomotopyGroup N (R i) (b i)))) :=
  (homotopyGroupSingletonMulEquiv N b).trans
    (botMulEquivDFinsupp (fun i ↦ HomotopyGroup N (R i) (b i)))

/-- On a representative the finite-support coordinates are its coordinate loop classes. -/
@[simp]
theorem homotopyGroupSingletonMulEquivDFinsupp_apply
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) (i : ι) :
    (homotopyGroupSingletonMulEquivDFinsupp N b
      (⟦p⟧ : HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b))).toAdd i =
      Additive.ofMul
        (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) := by
  exact (botMulEquivDFinsupp_apply
    (fun i ↦ HomotopyGroup N (R i) (b i))
    (homotopyGroupSingletonMulEquiv N b ⟦p⟧) i).trans
      (congrArg Additive.ofMul (homotopyGroupSingletonMulEquiv_apply N b p i))

/-- The inverse is determined by the coordinate classes, using the singleton comparison's
inverse characterization rather than a choice of coordinate representatives. -/
theorem homotopyGroupSingletonMulEquivDFinsupp_symm_eq_iff
    (d : Multiplicative (DFinsupp (fun i ↦ Additive (HomotopyGroup N (R i) (b i)))))
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) :
    (homotopyGroupSingletonMulEquivDFinsupp N b).symm d =
        (⟦p⟧ : HomotopyGroup N
          (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
          (singletonBasepoint b)) ↔
      ∀ i, (d.toAdd i).toMul =
        (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) := by
  have h := homotopyGroupSingletonMulEquiv_symm_eq_iff N b
    ((botMulEquivDFinsupp (fun i ↦ HomotopyGroup N (R i) (b i))).symm d) p
  simpa only [homotopyGroupSingletonMulEquivDFinsupp, MulEquiv.symm_trans_apply,
    botMulEquivDFinsupp_symm_apply] using h

/-- The coordinate-class formula uniquely characterizes the finite-support comparison. -/
theorem homotopyGroupSingletonMulEquivDFinsupp_unique
    (e : HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b) ≃*
      Multiplicative (DFinsupp (fun i ↦ Additive (HomotopyGroup N (R i) (b i)))))
    (he : ∀ (p : GenLoop N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b)) (i : ι),
      (e (⟦p⟧ : HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b))).toAdd i =
          Additive.ofMul
            (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i))) :
    e = homotopyGroupSingletonMulEquivDFinsupp N b := by
  have h := homotopyGroupSingletonMulEquiv_unique N b
    (e.trans (botMulEquivDFinsupp
      (fun i ↦ HomotopyGroup N (R i) (b i))).symm) (by
        intro p i
        exact (botMulEquivDFinsupp_symm_apply
          (fun i ↦ HomotopyGroup N (R i) (b i)) (e ⟦p⟧) i).trans
            ((congrArg Additive.toMul (he p i)).trans
              (toMul_ofMul
                (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)))))
  apply MulEquiv.ext
  intro a
  apply (botMulEquivDFinsupp (fun i ↦ HomotopyGroup N (R i) (b i))).symm.injective
  simpa only [homotopyGroupSingletonMulEquivDFinsupp, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] using DFunLike.congr_fun h a

/-- The support set records nonidentity coordinate classes, not nonconstant coordinate maps. -/
theorem homotopyGroupSingletonMulEquivDFinsupp_support
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) :
    {i | (homotopyGroupSingletonMulEquivDFinsupp N b
        (⟦p⟧ : HomotopyGroup N
          (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
          (singletonBasepoint b))).toAdd i ≠ 0} =
      {i | (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) ≠
        (1 : HomotopyGroup N (R i) (b i))} := by
  apply Set.ext
  intro i
  simp only [Set.mem_ofPred_eq, homotopyGroupSingletonMulEquivDFinsupp_apply]
  exact not_congr (ofMul_eq_zero (A := HomotopyGroup N (R i) (b i))
    (x := (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i))))

end RestrictedProduct
