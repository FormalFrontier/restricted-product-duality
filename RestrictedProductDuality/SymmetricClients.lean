/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Clients
public import RestrictedProductDuality.SymmetricDuality

/-!
# Cyclic local perfectness and symmetric restricted-product duality

The standard cyclic bicharacter is perfect in its left variable for every nonzero
modulus. This supplies the local perfectness used by the symmetric restricted-product
duality construction. Private constructions retain the empty PUnit, finite nontrivial
cyclic, and infinite PUnit index cases.

The cyclic bicharacter reuses Mathlib's `AddChar.zmod`, through the API in
`RestrictedProductDuality.Clients`.
-/

public section

set_option warningAsError true

noncomputable section

open Set
open scoped RestrictedProduct

namespace RestrictedProduct

/-- The discrete topology for symmetric cyclic clients, scoped to this file. -/
private local instance zmodTwoTopologicalSpaceSymmetricClients :
    TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
/-- The discrete-topology witness for symmetric cyclic clients. -/
private local instance zmodTwoDiscreteTopologySymmetricClients :
    DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

private theorem punitBicharacter_leftPerfect : Function.Bijective punitBicharacter := by
  constructor
  · intro x x' _
    exact Subsingleton.elim x x'
  · intro χ
    refine ⟨1, ?_⟩
    apply MonoidHom.ext
    intro y
    cases y
    exact χ.map_one.symm

private theorem punit_leftAnnihilator :
    (⊤ : Subgroup PUnit) = leftAnnihilator (⊤ : Subgroup PUnit) punitBicharacter := by
  ext x
  simp [leftAnnihilator, punitBicharacter, mem_rightAnnihilator]

/-- The standard cyclic bicharacter is bijective onto its circle-valued algebraic
character group in the left variable. Together with `zmodBicharacter_perfect`, this
provides local perfectness in both variables and supplies the left-perfectness
hypothesis of `symmetricPontryaginDualEquiv`. -/
theorem zmodBicharacter_leftPerfect (n : ℕ) [NeZero n] :
    Function.Bijective (zmodBicharacter n) := by
  have hsymm : zmodBicharacter n = rightCharacter (zmodBicharacter n) := by
    apply MonoidHom.ext
    intro x
    apply MonoidHom.ext
    intro y
    simp [zmodBicharacter_apply, AddChar.zmod, mul_comm]
  rw [hsymm]
  exact zmodBicharacter_perfect n

/-- Symmetric duality also handles an empty index type and trivial groups. -/
private noncomputable def punitSymmetricDuality_emptyIndex :
    (Πʳ _i : Empty, [PUnit, (⊤ : Subgroup PUnit)]) ≃ₜ*
      PontryaginDual (Πʳ _i : Empty, [PUnit, (⊤ : Subgroup PUnit)]) := by
  apply symmetricPontryaginDualEquiv (e := fun _ ↦ punitBicharacter)
  · simp [punitBicharacter]
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ punitBicharacter_leftPerfect
  · exact fun _ ↦ punit_leftAnnihilator

/-- Symmetric duality for a nontrivial finite-index cyclic pairing. -/
private noncomputable def zmodSymmetricDuality_finiteIndex :
    (Πʳ _i : Fin 3,
      [Multiplicative (ZMod 2), (⊤ : Subgroup (Multiplicative (ZMod 2)))]) ≃ₜ*
      PontryaginDual (Πʳ _i : Fin 3,
        [Multiplicative (ZMod 2), (⊥ : Subgroup (Multiplicative (ZMod 2)))]) := by
  apply symmetricPontryaginDualEquiv (e := fun _ ↦ zmodBicharacter 2)
  · intro i x hx y hy
    rw [Subgroup.mem_bot] at hy
    subst y
    simp
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ zmodBicharacter_leftPerfect 2
  · intro i
    ext x
    simp [leftAnnihilator, mem_rightAnnihilator]

/-- An infinite-index edge case with trivial coordinate groups. -/
private noncomputable def punitSymmetricDuality_infiniteIndex :
    (Πʳ _i : ℕ, [PUnit, (⊤ : Subgroup PUnit)]) ≃ₜ*
      PontryaginDual (Πʳ _i : ℕ, [PUnit, (⊤ : Subgroup PUnit)]) := by
  apply symmetricPontryaginDualEquiv (e := fun _ ↦ punitBicharacter)
  · simp [punitBicharacter]
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ punitBicharacter_leftPerfect
  · exact fun _ ↦ punit_leftAnnihilator

end RestrictedProduct
