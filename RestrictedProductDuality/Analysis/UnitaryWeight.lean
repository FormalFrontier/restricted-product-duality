/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Detecting weights of commuting unitary actions

A nonidentity operator in a finite-dimensional complex unitary action of a commutative
monoid is detected by a common Circle weight. No topology or inverses on the source monoid
are required. The proof uses the full span of joint eigenspaces, rather than selecting an
arbitrary common eigenvector, which might belong to the trivial weight.

## References

The simultaneous-diagonalization input is Mathlib's
`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`. This finite-unitary argument is a step
in compact abelian character separation; the broader context is Neukirch--Schmidt--Wingberg,
*Cohomology of Number Fields*, corrected second edition, Theorem (1.1.11).
-/

@[expose] public section

open scoped InnerProductSpace

universe uG uV

variable {E : Type uV} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The real and imaginary symmetric parts, without dividing by two. -/
private def unitaryPart (U : E ≃ₗᵢ[ℂ] E) (b : Bool) : E →ₗ[ℂ] E :=
  if b then (-Complex.I) • (U.toLinearEquiv.toLinearMap - U.symm.toLinearEquiv.toLinearMap)
  else U.toLinearEquiv.toLinearMap + U.symm.toLinearEquiv.toLinearMap

private theorem unitaryPart_symmetric (U : E ≃ₗᵢ[ℂ] E) (b : Bool) :
    (unitaryPart U b).IsSymmetric := by
  intro v w
  cases b with
  | false =>
    change ⟪U v + U.symm v, w⟫_ℂ = ⟪v, U w + U.symm w⟫_ℂ
    rw [inner_add_left, inner_add_right, U.inner_map_eq_flip, U.symm.inner_map_eq_flip]
    simp only [LinearIsometryEquiv.symm_symm]
    exact add_comm _ _
  | true =>
    change ⟪(-Complex.I) • (U v - U.symm v), w⟫_ℂ =
      ⟪v, (-Complex.I) • (U w - U.symm w)⟫_ℂ
    simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      U.inner_map_eq_flip, U.symm.inner_map_eq_flip, LinearIsometryEquiv.symm_symm,
      map_neg, Complex.conj_I, neg_neg]
    ring

private theorem commute_toLinearMap {U V : E ≃ₗᵢ[ℂ] E} (h : Commute U V) :
    Commute U.toLinearEquiv.toLinearMap V.toLinearEquiv.toLinearMap := by
  change U.toLinearEquiv.toLinearMap * V.toLinearEquiv.toLinearMap =
    V.toLinearEquiv.toLinearMap * U.toLinearEquiv.toLinearMap
  ext v
  exact congrArg (fun W : E ≃ₗᵢ[ℂ] E => W v) h.eq

private theorem commute_smul_right {A B : E →ₗ[ℂ] E} (h : Commute A B) (c : ℂ) :
    Commute A (c • B) := by
  change A * (c • B) = (c • B) * A
  rw [mul_smul_comm, smul_mul_assoc, h.eq]

private theorem unitaryPart_commute {U V : E ≃ₗᵢ[ℂ] E} (h : Commute U V)
    (b c : Bool) : Commute (unitaryPart U b) (unitaryPart V c) := by
  have h00 := commute_toLinearMap h
  have h01 := commute_toLinearMap h.inv_right
  have h10 := commute_toLinearMap h.inv_left
  have h11 := commute_toLinearMap h.inv_left.inv_right
  cases b <;> cases c
  · exact (h00.add_right h01).add_left (h10.add_right h11)
  · exact commute_smul_right ((h00.sub_right h01).add_left (h10.sub_right h11)) _
  · exact (commute_smul_right ((h00.add_right h01).sub_left
      (h10.add_right h11)).symm _).symm
  · exact (commute_smul_right (commute_smul_right ((h00.sub_right h01).sub_left
      (h10.sub_right h11)) _).symm _).symm

/-- A nonidentity action in a finite-dimensional commuting unitary representation is
 detected by a common Circle weight. The full joint-eigenspace span ensures detection of
 the specified action, not just existence of an arbitrary weight. -/
theorem MonoidHom.exists_circle_weight_ne_one
    {G : Type uG} [CommMonoid G]
    {E : Type uV} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (ρ : G →* (E ≃ₗᵢ[ℂ] E))
    {x : G} (hx : ρ x ≠ 1) :
    ∃ χ : G →* Circle, χ x ≠ 1 ∧
      ∃ v : E, v ≠ 0 ∧ ∀ g : G, ρ g v = (χ g : ℂ) • v := by
  classical
  let T : G × Bool → E →ₗ[ℂ] E := fun i => unitaryPart (ρ i.1) i.2
  have hcomm (g h : G) : Commute (ρ g) (ρ h) := by
    change ρ g * ρ h = ρ h * ρ g
    rw [← ρ.map_mul, ← ρ.map_mul, mul_comm g h]
  let S : (G × Bool → ℂ) → Submodule ℂ E := fun μ =>
    ⨅ i, Module.End.eigenspace (T i) (μ i)
  have hspan : ⨆ μ, S μ = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (T := T)
      (fun i => unitaryPart_symmetric (ρ i.1) i.2)
      (fun i j _ => unitaryPart_commute (hcomm i.1 j.1) i.2 j.2)
  have hdetect : ∃ μ v, v ∈ S μ ∧ ρ x v ≠ v := by
    by_contra! h
    apply hx
    ext w
    change ρ x w = w
    have hw : w ∈ ⨆ μ, S μ := by rw [hspan]; trivial
    exact Submodule.iSup_induction S (motive := fun v => ρ x v = v) hw
      (fun μ v hv => h μ v hv) (by simp)
      (fun v w hv hw => by rw [map_add, hv, hw])
  obtain ⟨μ, v, hv, hnot⟩ := hdetect
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hnot (by simp)
  have heig (i : G × Bool) : T i v = μ i • v :=
    Module.End.mem_eigenspace_iff.mp
      ((iInf_le (fun j => Module.End.eigenspace (T j) (μ j)) i) hv)
  let a : G → ℂ := fun g => (μ (g, false) + Complex.I * μ (g, true)) / 2
  have hweight (g : G) : ρ g v = a g • v := by
    have hA := heig (g, false)
    have hB := heig (g, true)
    change ρ g v + (ρ g).symm v = μ (g, false) • v at hA
    change (-Complex.I) • (ρ g v - (ρ g).symm v) = μ (g, true) • v at hB
    have hB' : ρ g v - (ρ g).symm v = (Complex.I * μ (g, true)) • v := by
      calc
        _ = Complex.I • ((-Complex.I) • (ρ g v - (ρ g).symm v)) := by
          simp [smul_smul]
        _ = Complex.I • (μ (g, true) • v) := by rw [hB]
        _ = _ := smul_smul _ _ _
    have hsum : (ρ g v + (ρ g).symm v) + (ρ g v - (ρ g).symm v) =
        (2 : ℂ) • ρ g v := by
      rw [two_smul ℂ]
      abel
    calc
      ρ g v = (2 : ℂ)⁻¹ • ((ρ g v + (ρ g).symm v) +
          (ρ g v - (ρ g).symm v)) := by
        rw [hsum, smul_smul]
        norm_num
      _ = (2 : ℂ)⁻¹ • (μ (g, false) • v + (Complex.I * μ (g, true)) • v) := by
        rw [hA, hB']
      _ = a g • v := by
        rw [← add_smul, smul_smul]
        congr 1
        dsimp only [a]
        ring
  have hnorm (g : G) : ‖a g‖ = 1 := by
    have hn := congrArg norm (hweight g)
    rw [(ρ g).norm_map, norm_smul] at hn
    apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hv0)
    simpa only [one_mul] using hn.symm
  have hone : a 1 = 1 := by
    apply smul_left_injective ℂ hv0
    calc
      a 1 • v = ρ 1 v := (hweight 1).symm
      _ = (1 : ℂ) • v := by simp
  have hmul (g h : G) : a (g * h) = a g * a h := by
    apply smul_left_injective ℂ hv0
    calc
      a (g * h) • v = ρ (g * h) v := (hweight _).symm
      _ = ρ g (ρ h v) := by rw [ρ.map_mul]; rfl
      _ = ρ g (a h • v) := by rw [hweight h]
      _ = a h • (a g • v) := by rw [map_smul, hweight g]
      _ = (a g * a h) • v := by rw [smul_smul, mul_comm]
  let χ : G →* Circle :=
    { toFun := fun g => ⟨a g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := by apply Circle.ext; exact hone
      map_mul' := fun g h => by apply Circle.ext; exact hmul g h }
  refine ⟨χ, ?_, v, hv0, fun g => hweight g⟩
  intro hχ
  apply hnot
  have ha : a x = 1 := congrArg (fun z : Circle => (z : ℂ)) hχ
  rw [hweight x, ha, one_smul]
