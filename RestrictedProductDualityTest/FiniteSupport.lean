/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.FiniteSupport
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Sparse integer coordinates and the empty-index boundary

The sparse values on the two sides are built independently with Mathlib's
restricted-product `mulSingle` and `DFinsupp.single`. They use the additive group
of integers through `Multiplicative`, not any homotopy-group classification.
The empty-index use supplies the original empty coordinate function directly.
-/

@[expose] public section

noncomputable section

open scoped RestrictedProduct

namespace RestrictedProductTest.FiniteSupport

/-- The integer-family restricted-product value with entries three and minus five
at coordinates two and seven, constructed by the stock pointwise product. -/
def sparseIntegers :
    Πʳ _i : ℕ, [Multiplicative ℤ, (⊥ : Subgroup (Multiplicative ℤ))] :=
  RestrictedProduct.mulSingle (fun _ : ℕ ↦ (⊥ : Subgroup (Multiplicative ℤ)))
      2 (Multiplicative.ofAdd (3 : ℤ)) *
    RestrictedProduct.mulSingle (fun _ : ℕ ↦ (⊥ : Subgroup (Multiplicative ℤ)))
      7 (Multiplicative.ofAdd (-5 : ℤ))

/-- The independently constructed finite-support integer value at the same two coordinates. -/
def sparseIntegerCoordinates :
    Multiplicative (DFinsupp (fun _ : ℕ ↦ Additive (Multiplicative ℤ))) :=
  Multiplicative.ofAdd
    (DFinsupp.single (β := fun _ : ℕ ↦ Additive (Multiplicative ℤ)) 2
      (Additive.ofMul (Multiplicative.ofAdd (3 : ℤ))) +
      DFinsupp.single (β := fun _ : ℕ ↦ Additive (Multiplicative ℤ)) 7
        (Additive.ofMul (Multiplicative.ofAdd (-5 : ℤ))))

/-- The generic comparison sends the bottom-subgroup value to the independently supplied
sparse integer coordinates. -/
theorem sparseIntegers_image :
    RestrictedProduct.botMulEquivDFinsupp (fun _ : ℕ ↦ Multiplicative ℤ)
      sparseIntegers = sparseIntegerCoordinates := by
  apply Multiplicative.toAdd.injective
  apply DFinsupp.ext
  intro i
  rw [RestrictedProduct.botMulEquivDFinsupp_apply]
  by_cases h₂ : i = 2
  · subst i
    simp [sparseIntegers, sparseIntegerCoordinates]
  · by_cases h₇ : i = 7
    · subst i
      simp [sparseIntegers, sparseIntegerCoordinates]
    · simp [sparseIntegers, sparseIntegerCoordinates, h₂, h₇, Ne.symm h₂, Ne.symm h₇]

/-- Both sparse values have precisely the prescribed two-element support set. -/
theorem sparseIntegers_support :
    {i | sparseIntegers i ≠ 1} = ({2, 7} : Set ℕ) ∧
      {i | sparseIntegerCoordinates.toAdd i ≠ 0} = ({2, 7} : Set ℕ) := by
  have hthree : Multiplicative.ofAdd (3 : ℤ) ≠ 1 := by decide
  have hsupport : {i | sparseIntegers i ≠ 1} = ({2, 7} : Set ℕ) := by
    ext i
    by_cases h₂ : i = 2
    · subst i
      simp [sparseIntegers, hthree]
    · by_cases h₇ : i = 7
      · subst i
        simp [sparseIntegers]
      · simp [sparseIntegers, h₂, h₇]
  refine ⟨hsupport, ?_⟩
  rw [← sparseIntegers_image, RestrictedProduct.botMulEquivDFinsupp_support]
  exact hsupport

/-- The sparse use is not the identity element. -/
theorem sparseIntegers_ne_one : sparseIntegers ≠ 1 := by
  intro h
  have htwo : (2 : ℕ) ∈ {i | sparseIntegers i ≠ 1} := by
    rw [sparseIntegers_support.1]
    simp
  simp [h] at htwo

/-- On the empty index type, the empty coordinate function maps to the zero finite-support
function, viewed multiplicatively. No nonempty-index hypothesis is required. -/
theorem emptyCoordinates :
    RestrictedProduct.botMulEquivDFinsupp (fun _ : Empty ↦ Multiplicative ℤ)
      (RestrictedProduct.mk (fun i : Empty ↦ nomatch i)
        (Filter.Eventually.of_forall fun i : Empty ↦ nomatch i)) =
      Multiplicative.ofAdd (0 : DFinsupp (fun _ : Empty ↦ Additive (Multiplicative ℤ))) := by
  apply Multiplicative.toAdd.injective
  apply DFinsupp.ext
  intro i
  exact nomatch i

end RestrictedProductTest.FiniteSupport
