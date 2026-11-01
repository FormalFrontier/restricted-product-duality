/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality.Analysis.UnitaryWeight

/-! A non-group source: nonnegative iterates of a nonidentity unitary operator. -/

private theorem nonnegative_iterates_detect
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E ≃ₗᵢ[ℂ] E) (hU : U ≠ 1) :
    ∃ χ : Multiplicative ℕ →* Circle, χ (Multiplicative.ofAdd 1) ≠ 1 := by
  let ρ : Multiplicative ℕ →* (E ≃ₗᵢ[ℂ] E) :=
    { toFun := fun n => U ^ n.toAdd
      map_one' := by simp
      map_mul' := fun m n => pow_add U m.toAdd n.toAdd }
  have hρ : ρ (Multiplicative.ofAdd 1) ≠ 1 := by simpa [ρ] using hU
  obtain ⟨χ, hχ, _⟩ := MonoidHom.exists_circle_weight_ne_one ρ hρ
  exact ⟨χ, hχ⟩
