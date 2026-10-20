/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Finite-support coordinates for bottom restricted products

The cofinite restricted product at the bottom submonoids consists of the dependent
functions equal to one outside a finite set. Changing one to zero by `Additive`
identifies it multiplicatively with `Multiplicative (DFinsupp (fun i ↦ Additive (G i)))`.
The index and fiber universes are independent, and the index type may be empty.

The comparison needs only `MulOneClass` on the factors: the source uses the stock
separate `One` and `Mul` instances. Bundled evaluation and family-map identities
use monoids. For groups, the bottom subgroup extends the bottom submonoid,
so the same comparison and coordinate equations apply directly to the
bottom-subgroup restricted product, with its original pointwise group operations.
Inversion uses `MulEquiv.map_inv` and `RestrictedProduct.inv_apply`.
No commutativity is needed. In particular, this is not a categorical coproduct
of noncommutative groups.

## References

The construction uses Mathlib's restricted products by Anatole Dedecker,
dependent finitely supported functions by Johannes Hölzl and Kenny Lau, and
additive/multiplicative type tags by Mario Carneiro. The support certificate is
the existing `DFinsupp` certificate; no additional support structure is introduced.
-/

@[expose] public section

noncomputable section

open Filter
open scoped RestrictedProduct

universe u v w

namespace RestrictedProduct

variable {ι : Type u} (G : ι → Type v)

section MulOneClass

variable [∀ i, MulOneClass (G i)]

/-- A bottom cofinite restricted-product element has finitely many nonunit coordinates. -/
theorem finite_ne_one (x : Πʳ i, [G i, (⊥ : Submonoid (G i))]) :
    Set.Finite {i | x i ≠ 1} := by
  have hx : ∀ᶠ i in cofinite, x i = 1 :=
    (RestrictedProduct.eventually G (fun i ↦ (⊥ : Submonoid (G i))) x).mono
      fun _ hi ↦ Submonoid.mem_bot.mp hi
  exact Filter.eventually_cofinite.mp hx

/-- Coordinate-preserving multiplicative equivalence from the bottom cofinite restricted
product to the multiplicative form of dependent finitely supported additive coordinates. -/
def botMulEquivDFinsupp :
    (Πʳ i, [G i, (⊥ : Submonoid (G i))]) ≃*
      Multiplicative (DFinsupp (fun i ↦ Additive (G i))) where
  toFun x := Multiplicative.ofAdd
    (DFinsupp.mk' (fun i ↦ Additive.ofMul (x i))
      (Trunc.mk ⟨(finite_ne_one G x).toFinset.val, by
        classical
        intro i
        by_cases hi : x i = 1
        · exact Or.inr (ofMul_eq_zero.mpr hi)
        · exact Or.inl ((finite_ne_one G x).mem_toFinset.mpr hi)⟩))
  invFun d := RestrictedProduct.mk (fun i ↦ (d.toAdd i).toMul) (by
    have hd : ∀ᶠ i in cofinite, d.toAdd i = 0 :=
      Filter.eventually_cofinite.mpr d.toAdd.finite_support
    exact hd.mono fun _ hi ↦ Submonoid.mem_bot.mpr (toMul_eq_one.mpr hi))
  left_inv := by
    intro x
    apply RestrictedProduct.ext
    intro i
    rfl
  right_inv := by
    intro d
    apply Multiplicative.ext
    apply DFinsupp.ext
    intro i
    rfl
  map_mul' := by
    intro x y
    apply Multiplicative.ext
    apply DFinsupp.ext
    intro i
    rfl

/-- Forward evaluation changes only the multiplicative/additive tag. -/
@[simp]
theorem botMulEquivDFinsupp_apply
    (x : Πʳ i, [G i, (⊥ : Submonoid (G i))]) (i : ι) :
    (botMulEquivDFinsupp G x).toAdd i = Additive.ofMul (x i) := by
  rfl

/-- Inverse evaluation recovers the original coordinate. -/
@[simp]
theorem botMulEquivDFinsupp_symm_apply
    (d : Multiplicative (DFinsupp (fun i ↦ Additive (G i)))) (i : ι) :
    (botMulEquivDFinsupp G).symm d i = (d.toAdd i).toMul := by
  rfl

/-- The comparison sends the constant-one family to the multiplicative identity. -/
@[simp]
theorem botMulEquivDFinsupp_one :
    botMulEquivDFinsupp G 1 = 1 := by
  apply Multiplicative.ext
  apply DFinsupp.ext
  intro i
  simpa only [botMulEquivDFinsupp_apply, RestrictedProduct.one_apply, toAdd_one,
    DFinsupp.zero_apply] using (ofMul_eq_zero.mpr (rfl : (1 : G i) = 1))

/-- The inverse comparison sends the multiplicative identity to the constant-one family. -/
@[simp]
theorem botMulEquivDFinsupp_symm_one :
    (botMulEquivDFinsupp G).symm 1 = 1 := by
  apply (botMulEquivDFinsupp G).injective
  rw [(botMulEquivDFinsupp G).apply_symm_apply, botMulEquivDFinsupp_one]

/-- The dependent nonzero-coordinate set is exactly the original nonunit-coordinate set.
This set formulation requires no decidability assumptions on the index or fibers. -/
theorem botMulEquivDFinsupp_support
    (x : Πʳ i, [G i, (⊥ : Submonoid (G i))]) :
    {i | (botMulEquivDFinsupp G x).toAdd i ≠ 0} = {i | x i ≠ 1} := by
  ext i
  simp only [Set.mem_ofPred_eq, botMulEquivDFinsupp_apply]
  exact not_congr (ofMul_eq_zero (x := x i))

end MulOneClass

section Monoid

variable [∀ i, Monoid (G i)]

/-- The comparison intertwines the existing bundled evaluations. -/
theorem botMulEquivDFinsupp_eval (i : ι) :
    ((DFinsupp.evalAddMonoidHom (β := fun i ↦ Additive (G i)) i).toMultiplicativeLeft).comp
        (botMulEquivDFinsupp G).toMonoidHom =
      RestrictedProduct.evalMonoidHom G
        (B := fun i ↦ (⊥ : Submonoid (G i))) (𝓕 := cofinite) i := by
  apply MonoidHom.ext
  intro x
  exact congrArg Additive.toMul (botMulEquivDFinsupp_apply G x i)

variable (H : ι → Type w) [∀ i, Monoid (H i)]

/-- Fixed-index family maps commute with the comparison. Both sides use the existing
bundled maps: identity reindexing for restricted products and tagged `DFinsupp.mapRange`. -/
theorem botMulEquivDFinsupp_mapAlongMonoidHom (φ : ∀ i, G i →* H i)
    (x : Πʳ i, [G i, (⊥ : Submonoid (G i))]) :
    botMulEquivDFinsupp H
        (RestrictedProduct.mapAlongMonoidHom G H id Filter.tendsto_id
          (B₁ := fun i ↦ (⊥ : Submonoid (G i)))
          (B₂ := fun i ↦ (⊥ : Submonoid (H i))) φ
          (Filter.Eventually.of_forall fun i _g hg ↦
            Submonoid.mem_bot.mpr
              ((congrArg (φ i) (Submonoid.mem_bot.mp hg)).trans (map_one (φ i)))) x) =
      (DFinsupp.mapRange.addMonoidHom (fun i ↦ (φ i).toAdditive)).toMultiplicative
        (botMulEquivDFinsupp G x) := by
  apply Multiplicative.ext
  apply DFinsupp.ext
  intro i
  exact (botMulEquivDFinsupp_apply H _ i).trans
    (congrArg (fun a : Additive (G i) ↦ (φ i).toAdditive a)
      (botMulEquivDFinsupp_apply G x i)).symm

end Monoid

end RestrictedProduct
