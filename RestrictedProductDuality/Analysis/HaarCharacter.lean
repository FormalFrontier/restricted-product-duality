/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Analysis.HaarLpAction
public import RestrictedProductDuality.Analysis.CharacterContinuity

/-!
# Continuity from Haar L² weights

A nonzero continuous complex-valued weight for the canonical Haar right-translation
action makes its Circle-valued function continuous. The translation/toLp equality
criterion converts each fixed translation separately to a pointwise weight identity;
continuity then follows from `Function.continuous_of_continuous_weight`.
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
