/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Analysis.UnitaryWeight
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Detecting weights in an invariant eigenspace

A commuting isometric action restricts to the original eigenspace of a linear
endomorphism. If that eigenspace is finite dimensional, a vector moved by the
action yields a detecting Circle weight with a nonzero vector in the same
ambient eigenspace. The ambient inner-product space need not be finite
dimensional or complete, and the acting commutative monoid need not be a group.

The inverse restriction uses the inverse of each original isometry, not an
inverse element of the monoid. Finite dimensionality is used only for
`MonoidHom.exists_circle_weight_ne_one` after the restriction is constructed.
-/

@[expose] public section

universe uG uH

section Restriction

variable {G : Type uG} [CommMonoid G]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (S : Module.End ℂ H) («λ₀» : ℂ)

private theorem eigenspace_map_mem
    (hcomm : ∀ g z, S (ρ g z) = ρ g (S z)) (g : G)
    {a : H} (ha : a ∈ Module.End.eigenspace S «λ₀») :
    ρ g a ∈ Module.End.eigenspace S «λ₀» := by
  apply Module.End.mem_eigenspace_iff.mpr
  rw [hcomm, Module.End.mem_eigenspace_iff.mp ha, map_smul]

private theorem eigenspace_symm_mem
    (hcomm : ∀ g z, S (ρ g z) = ρ g (S z)) (g : G)
    {a : H} (ha : a ∈ Module.End.eigenspace S «λ₀») :
    (ρ g).symm a ∈ Module.End.eigenspace S «λ₀» := by
  apply Module.End.mem_eigenspace_iff.mpr
  apply (ρ g).injective
  calc
    ρ g (S ((ρ g).symm a)) = S (ρ g ((ρ g).symm a)) := (hcomm g _).symm
    _ = S a := by rw [(ρ g).apply_symm_apply]
    _ = «λ₀» • a := Module.End.mem_eigenspace_iff.mp ha
    _ = ρ g («λ₀» • (ρ g).symm a) := by rw [map_smul, (ρ g).apply_symm_apply]

private def eigenspaceEquiv
    (hcomm : ∀ g z, S (ρ g z) = ρ g (S z)) (g : G) :
    Module.End.eigenspace S «λ₀» ≃ₗᵢ[ℂ] Module.End.eigenspace S «λ₀» where
  toLinearEquiv :=
    { toFun := fun a => ⟨ρ g (a : H), eigenspace_map_mem ρ S «λ₀» hcomm g a.property⟩
      invFun := fun a => ⟨(ρ g).symm (a : H), eigenspace_symm_mem ρ S «λ₀» hcomm g a.property⟩
      left_inv := fun a => Subtype.ext ((ρ g).symm_apply_apply (a : H))
      right_inv := fun a => Subtype.ext ((ρ g).apply_symm_apply (a : H))
      map_add' := fun a b => Subtype.ext (map_add (ρ g) (a : H) (b : H))
      map_smul' := fun c a => Subtype.ext (map_smul (ρ g) c (a : H)) }
  norm_map' a := (ρ g).norm_map (a : H)

private theorem eigenspaceEquiv_coe_apply
    (hcomm : ∀ g z, S (ρ g z) = ρ g (S z)) (g : G)
    (a : Module.End.eigenspace S «λ₀») :
    (eigenspaceEquiv ρ S «λ₀» hcomm g a : H) = ρ g (a : H) := rfl

private def eigenspaceAction
    (hcomm : ∀ g z, S (ρ g z) = ρ g (S z)) :
    G →* (Module.End.eigenspace S «λ₀» ≃ₗᵢ[ℂ] Module.End.eigenspace S «λ₀») where
  toFun := eigenspaceEquiv ρ S «λ₀» hcomm
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro a
    apply Subtype.ext
    simp only [eigenspaceEquiv_coe_apply, map_one, LinearIsometryEquiv.coe_one, id_eq]
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro a
    apply Subtype.ext
    simp only [eigenspaceEquiv_coe_apply, map_mul, LinearIsometryEquiv.coe_mul,
      Function.comp_apply]

private theorem eigenspaceAction_coe_apply
    (hcomm : ∀ g z, S (ρ g z) = ρ g (S z)) (g : G)
    (a : Module.End.eigenspace S «λ₀») :
    (eigenspaceAction ρ S «λ₀» hcomm g a : H) = ρ g (a : H) := rfl

end Restriction

/-- A moved vector in a finite-dimensional eigenspace gives a Circle character
that detects the moving element and a nonzero common weight vector in that
same eigenspace. Only the eigenspace, not the ambient space, must be finite
dimensional; the endomorphism is merely linear and its eigenvalue may be zero. -/
theorem MonoidHom.exists_circle_weight_ne_one_of_mem_eigenspace
    {G : Type uG} [CommMonoid G]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (S : Module.End ℂ H) («λ₀» : ℂ)
    [FiniteDimensional ℂ (Module.End.eigenspace S «λ₀»)]
    (hcomm : ∀ (g : G) (z : H), S (ρ g z) = ρ g (S z))
    {x : G} {v₀ : H} (hv : v₀ ∈ Module.End.eigenspace S «λ₀»)
    (hmove : ρ x v₀ ≠ v₀) :
    ∃ χ : G →* Circle, χ x ≠ 1 ∧
      ∃ w : H, w ≠ 0 ∧ w ∈ Module.End.eigenspace S «λ₀» ∧
        ∀ g : G, ρ g w = (χ g : ℂ) • w := by
  let E := Module.End.eigenspace S «λ₀»
  let τ := eigenspaceAction ρ S «λ₀» hcomm
  have hx : τ x ≠ 1 := by
    intro h
    apply hmove
    have he := congrArg (fun U : E ≃ₗᵢ[ℂ] E => (U ⟨v₀, hv⟩ : H)) h
    calc
      ρ x v₀ = (τ x ⟨v₀, hv⟩ : H) :=
        (eigenspaceAction_coe_apply ρ S «λ₀» hcomm x ⟨v₀, hv⟩).symm
      _ = ((1 : E ≃ₗᵢ[ℂ] E) ⟨v₀, hv⟩ : H) := he
      _ = v₀ := rfl
  obtain ⟨χ, hχ, w, hw, hweight⟩ := MonoidHom.exists_circle_weight_ne_one τ hx
  refine ⟨χ, hχ, (w : H), ?_, w.property, ?_⟩
  · intro hzero
    exact hw (Subtype.ext hzero)
  · intro g
    calc
      ρ g (w : H) = (τ g w : H) :=
        (eigenspaceAction_coe_apply ρ S «λ₀» hcomm g w).symm
      _ = (χ g : ℂ) • (w : H) := congrArg (fun a : E => (a : H)) (hweight g)
