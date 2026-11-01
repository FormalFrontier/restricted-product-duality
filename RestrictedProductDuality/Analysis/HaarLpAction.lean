/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Right translation on Haar L²

For a compact Hausdorff commutative topological group, `MeasureTheory.Lp.haarRightTranslation`
is the complex-linear isometric action obtained by pulling back along `s ↦ s * g`. The
measurable space is the Borel space of the original topology, and the measure is
`MeasureTheory.Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)`.

The construction reuses the measure-preserving pullback on `Lp` and
`LinearIsometryEquiv.ofLinearIsometry`. Its covariance with `ContinuousMap.toLp` identifies
translated continuous functions in L² and recovers their pointwise equalities.

## Implementation notes

Commutativity is used to deduce right invariance from left Haar invariance. This is a
specialization to commutative groups, not an obstruction to right regular actions for
noncommutative compact groups. No countability assumption on the group, simultaneous
conull set of translation formulas, or continuity of the action in the L² norm is used.
Character separation is not proved here.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

universe u

namespace MeasureTheory.Lp

variable (K : Type u) [CommGroup K]

private def rightMul (g : K) : K → K := fun s => s * g

private theorem rightMul_one : rightMul K 1 = id := by
  funext s
  exact mul_one s

private theorem rightMul_mul (a b : K) :
    rightMul K (a * b) = rightMul K b ∘ rightMul K a := by
  funext s
  exact (mul_assoc s a b).symm

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]

omit [T2Space K]

-- Fix the measurable dictionary, without changing the group or its topology.
/-- The canonical Borel measurable space used for Haar L² on `K`. -/
local instance haarBorelMeasurableSpace : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
local instance : SecondCountableTopologyEither K ℂ := inferInstance

local notation "μ" => Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
local notation "H" => Lp ℂ (2 : ℝ≥0∞) μ

private theorem haarRightPreserving (g : K) :
    MeasurePreserving (rightMul K g) μ μ := by
  have hL := MeasureTheory.measurePreserving_mul_left μ g
  have c : (fun s : K => g * s) = rightMul K g := by
    funext s
    exact mul_comm g s
  exact c ▸ hL

private theorem haarPullback_congr {f g : K → K}
    (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ) (hfg : f = g) :
    compMeasurePreserving (E := ℂ) (p := (2 : ℝ≥0∞)) f hf =
      compMeasurePreserving g hg := by
  cases hfg
  rfl

private theorem haarPullback_one :
    compMeasurePreserving (E := ℂ) (p := (2 : ℝ≥0∞))
      (rightMul K 1) (haarRightPreserving K 1) = AddMonoidHom.id H := by
  exact (haarPullback_congr K (haarRightPreserving K 1)
    (MeasurePreserving.id μ) (rightMul_one K)).trans
    (compMeasurePreserving_id (E := ℂ) (p := (2 : ℝ≥0∞)) (μb := μ))

private theorem haarPullback_mul (a b : K) :
    compMeasurePreserving (E := ℂ) (p := (2 : ℝ≥0∞))
      (rightMul K (a * b)) (haarRightPreserving K (a * b)) =
      (compMeasurePreserving (rightMul K a) (haarRightPreserving K a)).comp
        (compMeasurePreserving (rightMul K b) (haarRightPreserving K b)) := by
  exact (haarPullback_congr K (haarRightPreserving K (a * b))
    ((haarRightPreserving K b).comp (haarRightPreserving K a))
    (rightMul_mul K a b)).trans
    (compMeasurePreserving_comp (E := ℂ) (p := (2 : ℝ≥0∞))
      (haarRightPreserving K b) (haarRightPreserving K a))

private noncomputable def rightTranslationIsometry (g : K) : H →ₗᵢ[ℂ] H :=
  compMeasurePreservingₗᵢ ℂ (rightMul K g) (haarRightPreserving K g)

private noncomputable def rightTranslationInverse (g : K) : H →ₗ[ℂ] H :=
  compMeasurePreservingₗ ℂ (rightMul K g⁻¹) (haarRightPreserving K g⁻¹)

private theorem rightTranslationIsometry_apply (g : K) (u : H) :
    (rightTranslationIsometry K g).toLinearMap u =
      compMeasurePreserving (rightMul K g) (haarRightPreserving K g) u := rfl

private theorem rightTranslationInverse_apply (g : K) (u : H) :
    rightTranslationInverse K g u =
      compMeasurePreserving (rightMul K g⁻¹) (haarRightPreserving K g⁻¹) u := rfl

private theorem rightTranslation_comp_inverse (g : K) :
    (rightTranslationIsometry K g).toLinearMap.comp (rightTranslationInverse K g) =
      LinearMap.id := by
  ext u : 1
  rw [LinearMap.comp_apply, rightTranslationIsometry_apply,
    rightTranslationInverse_apply, LinearMap.id_apply]
  have h := congrArg (fun f : H →+ H => f u) (haarPullback_mul K g g⁻¹).symm
  simpa only [mul_inv_cancel, haarPullback_one, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] using h

private theorem rightTranslation_inverse_comp (g : K) :
    (rightTranslationInverse K g).comp (rightTranslationIsometry K g).toLinearMap =
      LinearMap.id := by
  ext u : 1
  rw [LinearMap.comp_apply, rightTranslationInverse_apply,
    rightTranslationIsometry_apply, LinearMap.id_apply]
  have h := congrArg (fun f : H →+ H => f u) (haarPullback_mul K g⁻¹ g).symm
  simpa only [inv_mul_cancel, haarPullback_one, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] using h

private noncomputable def rightTranslationEquiv (g : K) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofLinearIsometry (rightTranslationIsometry K g)
    (rightTranslationInverse K g) (rightTranslation_comp_inverse K g)
    (rightTranslation_inverse_comp K g)

private theorem rightTranslationEquiv_coe (g : K) :
    (rightTranslationEquiv K g : H → H) = (rightTranslationIsometry K g : H → H) :=
  LinearIsometryEquiv.coe_ofLinearIsometry _ _ _ _

private theorem rightTranslationEquiv_symm_coe (g : K) :
    ((rightTranslationEquiv K g).symm : H → H) =
      (rightTranslationInverse K g : H → H) :=
  LinearIsometryEquiv.coe_ofLinearIsometry_symm _ _ _ _

private theorem rightTranslationEquiv_apply (g : K) (u : H) :
    rightTranslationEquiv K g u =
      compMeasurePreserving (rightMul K g) (haarRightPreserving K g) u :=
  congrFun (rightTranslationEquiv_coe K g) u

/-- Right translation on complex L² for the Haar measure of a compact Hausdorff commutative
topological group, with its canonical Borel measurable space. The value at `g` pulls back
along `s ↦ s * g`; its inverse pulls back along `s ↦ s * g⁻¹`. -/
noncomputable def haarRightTranslation :
    K →*
      (Lp ℂ (2 : ℝ≥0∞) (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) ≃ₗᵢ[ℂ]
        Lp ℂ (2 : ℝ≥0∞) (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K))) where
  toFun g := LinearIsometryEquiv.ofLinearIsometry
    (compMeasurePreservingₗᵢ ℂ (fun s : K => s * g)
      (by simpa only [mul_comm] using (measurePreserving_mul_left μ g)))
    (compMeasurePreservingₗ ℂ (fun s : K => s * g⁻¹)
      (by simpa only [mul_comm] using (measurePreserving_mul_left μ g⁻¹)))
    (by exact rightTranslation_comp_inverse K g)
    (by exact rightTranslation_inverse_comp K g)
  map_one' := by
    ext u : 1
    change rightTranslationEquiv K 1 u = u
    rw [rightTranslationEquiv_apply]
    exact congrArg (fun f : H →+ H => f u) (haarPullback_one K)
  map_mul' a b := by
    ext u : 1
    change rightTranslationEquiv K (a * b) u =
      rightTranslationEquiv K a (rightTranslationEquiv K b u)
    simp only [rightTranslationEquiv_apply]
    exact congrArg (fun f : H →+ H => f u) (haarPullback_mul K a b)

/-- The action is the stock linear-isometric measure-preserving pullback. -/
theorem coe_haarRightTranslation (g : K) :
    (haarRightTranslation K g : H → H) =
      (compMeasurePreservingₗᵢ ℂ (fun s : K => s * g)
        (by simpa only [mul_comm] using (measurePreserving_mul_left μ g)) : H → H) :=
  rightTranslationEquiv_coe K g

/-- Applying right translation agrees with the stock additive pullback. -/
theorem haarRightTranslation_apply (g : K) (u : H) :
    haarRightTranslation K g u =
      compMeasurePreserving (fun s : K => s * g)
        (by simpa only [mul_comm] using (measurePreserving_mul_left μ g)) u :=
  congrFun (coe_haarRightTranslation K g) u

/-- The inverse action is the stock linear pullback along right multiplication by `g⁻¹`. -/
theorem coe_haarRightTranslation_inv (g : K) :
    ⇑((haarRightTranslation K g)⁻¹) =
      (compMeasurePreservingₗ ℂ (fun s : K => s * g⁻¹)
        (by simpa only [mul_comm] using (measurePreserving_mul_left μ g⁻¹)) : H → H) := by
  rw [LinearIsometryEquiv.coe_inv]
  exact rightTranslationEquiv_symm_coe K g

/-- Each fixed translation has the expected almost-everywhere value. -/
theorem coeFn_haarRightTranslation (g : K) (u : H) :
    (haarRightTranslation K g u : K → ℂ) =ᵐ[μ] fun s => u (s * g) := by
  rw [haarRightTranslation_apply]
  exact coeFn_compMeasurePreserving u (haarRightPreserving K g)

/-- Each fixed inverse translation has the expected almost-everywhere value. -/
theorem coeFn_haarRightTranslation_inv (g : K) (u : H) :
    ((haarRightTranslation K g)⁻¹ u : K → ℂ) =ᵐ[μ] fun s => u (s * g⁻¹) := by
  rw [congrFun (coe_haarRightTranslation_inv K g) u]
  exact coeFn_compMeasurePreserving u (haarRightPreserving K g⁻¹)

/-- The identity law is the stock monoid-homomorphism identity law. -/
theorem haarRightTranslation_one : haarRightTranslation K 1 = 1 :=
  (haarRightTranslation K).map_one

/-- Right pullback has the order `ρ a * ρ b = ρ (a * b)`. -/
theorem haarRightTranslation_mul (a b : K) :
    haarRightTranslation K a * haarRightTranslation K b = haarRightTranslation K (a * b) :=
  ((haarRightTranslation K).map_mul a b).symm

/-- The inverse law is the stock group-homomorphism inverse law. -/
theorem haarRightTranslation_inv (g : K) :
    (haarRightTranslation K g)⁻¹ = haarRightTranslation K g⁻¹ :=
  ((haarRightTranslation K).map_inv g).symm

/-- Right translation preserves the L² norm. -/
theorem norm_haarRightTranslation (g : K) (u : H) :
    ‖haarRightTranslation K g u‖ = ‖u‖ :=
  (haarRightTranslation K g).norm_map u

/-- The stock continuous-to-L² map intertwines continuous right translation and the Haar
L² action. The continuous function on the left has value `s ↦ w (s * g)`. -/
theorem haarRightTranslation_toLp (g : K) (w : C(K, ℂ)) :
    ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ
      { toFun := fun s => w (s * g)
        continuous_toFun := w.continuous.comp (continuous_id.mul continuous_const) } =
      haarRightTranslation K g (ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ w) := by
  apply Lp.ext
  have hw := (haarRightPreserving K g).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ w)
  filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ
      { toFun := fun s => w (s * g)
        continuous_toFun := w.continuous.comp (continuous_id.mul continuous_const) },
    hw, coeFn_haarRightTranslation K g (ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ w)]
    with s hs hw' ht
  exact hs.trans (hw'.symm.trans ht.symm)

/-- Equality of a translated continuous L² vector with another continuous L² vector is
exactly their pointwise translation identity. This uses injectivity of the stock `toLp`
map for Haar measure, which is positive on nonempty open sets. -/
theorem haarRightTranslation_toLp_eq_iff (g : K) (w z : C(K, ℂ)) :
    haarRightTranslation K g (ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ w) =
      ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ z ↔ ∀ s, w (s * g) = z s := by
  rw [← haarRightTranslation_toLp K g w, ContinuousMap.toLp_inj]
  constructor
  · intro h s
    exact congrArg (fun f : C(K, ℂ) => f s) h
  · intro h
    ext s
    exact h s

end MeasureTheory.Lp
