/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Analysis.HaarLpAction
public import RestrictedProductDuality.Analysis.CharacterContinuity
import RestrictedProductDuality.Analysis.HaarConvolution
import RestrictedProductDuality.Analysis.EigenspaceWeight
import ComplexAnalysis.Analysis.InnerProductSpace.CompactOperator

/-!
# Haar L² weights and compact-group character separation

A nonzero continuous complex-valued weight for the canonical Haar right-translation
action makes its Circle-valued function continuous. The translation/toLp equality
criterion converts each fixed translation separately to a pointwise weight identity;
continuity then follows from `Function.continuous_of_continuous_weight`.

For a compact Hausdorff commutative topological group,
`exists_continuous_character_ne_one` separates every nonidentity element by a
continuous Circle character. A convolution detecting the prescribed element gives
a compact operator `T`; a nonzero eigenspace of `T T*` contains a moved vector.
A detecting weight in that same eigenspace has a continuous representative, so
the Haar weight continuity criterion applies to the same algebraic character.

## References

The compact-Haar convolution and spectral argument follows the exposition
*Pontryagin bidual reflexivity*, §§1–2 and 9.1. The source context is
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
edition, electronic version 2.3, Definition (1.1.10) and Theorem (1.1.11).
Only compact-group character separation is established here, not the full
locally compact duality theorem.
-/

@[expose] public section

open scoped ENNReal

universe u

namespace Function

/-- The Borel measurable structure used by Haar L² weights. -/
local instance haarWeightMeasurableSpace
    (K : Type u) [TopologicalSpace K] : MeasurableSpace K := borel K

/-- The measurable structure for Haar L² weights is the Borel structure. -/
local instance haarWeightBorelSpace (K : Type u) [TopologicalSpace K] :
    BorelSpace K := ⟨rfl⟩

/-- The L² exponent satisfies the lower bound required by the continuous-to-Lp map. -/
local instance twoLpExponentAtLeastOne : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩

/-- A Circle-valued function with a nonzero continuous weight for the canonical Haar
L² right-translation action is continuous. No homomorphism laws are assumed. -/
theorem continuous_of_toLp_haarRightTranslation_weight
    {K : Type u} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K]
    (χ : K → Circle) (w : C(K, ℂ)) (hw : w ≠ 0)
    (hweight :
      let μ := MeasureTheory.Measure.haarMeasure
        (⊤ : TopologicalSpace.PositiveCompacts K)
      let J := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
      let ρ := MeasureTheory.Lp.haarRightTranslation K
      ∀ g : K, ρ g (J w) = (χ g : ℂ) • J w) :
    Continuous χ := by
  let μ := MeasureTheory.Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts K)
  let J := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let ρ := MeasureTheory.Lp.haarRightTranslation K
  change ∀ g : K, ρ g (J w) = (χ g : ℂ) • J w at hweight
  apply Function.continuous_of_continuous_weight χ w hw
  intro s g
  have htranslated : ρ g (J w) = J ((χ g : ℂ) • w) := by
    rw [map_smul]
    exact hweight g
  have hs :=
    (MeasureTheory.Lp.haarRightTranslation_toLp_eq_iff
      K g w ((χ g : ℂ) • w)).mp htranslated s
  simpa only [ContinuousMap.smul_apply, smul_eq_mul] using hs

end Function

/-- A nonidentity element of a compact Hausdorff commutative topological group is
detected by a continuous circle-valued character. The proof follows the compact-Haar
convolution and spectral argument in *Pontryagin bidual reflexivity*, §9.1. -/
theorem exists_continuous_character_ne_one
    {K : Type u} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    {x : K} (hx : x ≠ 1) :
    ∃ χ : K →ₜ* Circle, χ x ≠ 1 := by
  classical
  let _ : MeasurableSpace K := borel K
  let _ : BorelSpace K := ⟨rfl⟩
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  let _ : SecondCountableTopologyEither K ℂ := inferInstance
  let μ := MeasureTheory.Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts K)
  let H := MeasureTheory.Lp ℂ 2 μ
  let J := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let ρ := MeasureTheory.Lp.haarRightTranslation K
  let U (g : K) : H →L[ℂ] H :=
    (ρ g).toLinearIsometry.toContinuousLinearMap
  obtain ⟨f, hf⟩ :=
    ContinuousMap.exists_haarRightTranslation_sub_id_comp_kernelOperator_toLp_ne_zero K x hx
  let κ_f : C(K × K, ℂ) := f.comp
    ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
  let C_f := ContinuousMap.kernelOperator μ κ_f
  let T_f := J.comp C_f
  let S_f := T_f.comp T_f.adjoint
  let B_x := U x - ContinuousLinearMap.id ℂ H
  have hBT : B_x.comp T_f ≠ 0 := hf
  have hC : IsCompactOperator C_f :=
    ContinuousMap.isCompactOperator_kernelOperator μ κ_f
  have hT : IsCompactOperator T_f := hC.clm_comp J
  obtain ⟨eigenvalue, heigenvalue, hfinite, v_detect, hv_detect_eigen, hdetect⟩ :=
    ContinuousLinearMap.exists_eigenvector_comp_adjoint_detected T_f B_x hT hBT
  let S : Module.End ℂ H := S_f.toLinearMap
  let _ : FiniteDimensional ℂ (Module.End.eigenspace S eigenvalue) := hfinite
  have hcomm (g : K) (z : H) : S (ρ g z) = ρ g (S z) := by
    change S_f (ρ g z) = ρ g (S_f z)
    have hcov : S_f.comp (U g) = (U g).comp S_f :=
      ContinuousMap.kernelOperator_toLp_comp_adjoint_haarRightTranslation_comm K f g
    simpa only [ContinuousLinearMap.comp_apply, U,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] using
      congrArg (fun A : H →L[ℂ] H => A z) hcov
  have hv_detect : v_detect ∈ Module.End.eigenspace S eigenvalue :=
    Module.End.mem_eigenspace_iff.mpr hv_detect_eigen
  have hmove : ρ x v_detect ≠ v_detect := by
    intro hfix
    apply hdetect
    change ρ x v_detect - v_detect = 0
    exact sub_eq_zero.mpr hfix
  obtain ⟨χ_alg, hχx, v_weight, hv_weight_ne, hv_weight, hweight⟩ :=
    MonoidHom.exists_circle_weight_ne_one_of_mem_eigenspace
      ρ S eigenvalue hcomm hv_detect hmove
  have hv_weight_eigen : S v_weight = eigenvalue • v_weight :=
    Module.End.mem_eigenspace_iff.mp hv_weight
  let w : C(K, ℂ) := eigenvalue⁻¹ • C_f (T_f.adjoint v_weight)
  have hJw : J w = v_weight := by
    calc
      J w = eigenvalue⁻¹ • J (C_f (T_f.adjoint v_weight)) :=
        J.map_smul eigenvalue⁻¹ (C_f (T_f.adjoint v_weight))
      _ = eigenvalue⁻¹ • S v_weight := rfl
      _ = eigenvalue⁻¹ • (eigenvalue • v_weight) := by rw [hv_weight_eigen]
      _ = v_weight := by
        rw [smul_smul, inv_mul_cancel₀ heigenvalue, one_smul]
  have hw : w ≠ 0 := by
    intro hw_zero
    apply hv_weight_ne
    calc
      v_weight = J w := hJw.symm
      _ = J 0 := congrArg J hw_zero
      _ = 0 := map_zero J
  have hL2weight : ∀ g : K, ρ g (J w) = (χ_alg g : ℂ) • J w := by
    intro g
    rw [hJw]
    exact hweight g
  have hχcont : Continuous (χ_alg : K → Circle) :=
    Function.continuous_of_toLp_haarRightTranslation_weight
      (χ_alg : K → Circle) w hw hL2weight
  let χ_cont : K →ₜ* Circle := ⟨χ_alg, hχcont⟩
  exact ⟨χ_cont, hχx⟩
