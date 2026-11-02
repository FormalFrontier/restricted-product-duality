/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Analysis.HaarLpAction
public import RestrictedProductDuality.Analysis.CompactConvolution
public import ComplexAnalysis.MeasureTheory.Integral.Kernel
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Haar convolution and right translation

Convolution with the kernel `f (s * t⁻¹)` intertwines the right translations
on the original Haar `L²` space. Its continuous-to-`L²` realization, its
adjoint, and its product with that adjoint commute with right translation.

The kernel evaluation is the inner product with the embedded conjugated
kernel section. Translating this section by `g⁻¹` translates its parameter
by `g`; unitarity then gives covariance without an integral substitution.

For every nonidentity group element, some continuous kernel gives a nonzero
right-translation defect after the continuous-function embedding into Haar L².
The convolution evaluation witness and the pointwise translation eliminator
keep the same group, measure and continuous functions.

## References

The proof follows the right-translation and positive-square argument in
*Right translations and continuous convolution*, §§3–6. Its source context
is Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
edition, electronic version 2.3, Definition (1.1.10) and Theorem (1.1.11).
The embedding, kernel operator and unitary/adjoint identities are those of
Mathlib and ComplexAnalysis.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ContinuousMap

variable (K : Type u) [CommGroup K] [TopologicalSpace K]
  [IsTopologicalGroup K] [CompactSpace K]

/-- The Borel measurable structure of the given topology. -/
local instance haarConvolutionBorelMeasurableSpace : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
local instance : SecondCountableTopologyEither K ℂ := inferInstance

local notation "μ" => Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
local notation "H" => Lp ℂ (2 : ℝ≥0∞) μ

/-- The continuous Haar convolution output is covariant under right translation. -/
theorem kernelOperator_haarRightTranslation_apply
    (f : C(K, ℂ)) (g : K)
    (u : Lp ℂ (2 : ℝ≥0∞)
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K))) (s : K) :
    let κ : C(K × K, ℂ) := f.comp
      ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
    kernelOperator (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) κ
        (Lp.haarRightTranslation K g u) s =
      kernelOperator (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) κ
        u (s * g) := by
  let κ : C(K × K, ℂ) := f.comp
    ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
  let Γ : K → H := fun a => toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry a))
  have hq :
      ({ toFun := fun t => (star (κ.curry s)) (t * g⁻¹)
         continuous_toFun := (star (κ.curry s)).continuous.comp
           (continuous_id.mul continuous_const) } : C(K, ℂ)) =
        star (κ.curry (s * g)) := by
    ext t
    change star (f (s * (t * g⁻¹)⁻¹)) = star (f ((s * g) * t⁻¹))
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hΓ : (Lp.haarRightTranslation K g).symm (Γ s) = Γ (s * g) := by
    simpa only [map_inv, LinearIsometryEquiv.coe_inv, hq] using
      (Lp.haarRightTranslation_toLp K (g⁻¹) (star (κ.curry s))).symm
  calc
    kernelOperator μ κ (Lp.haarRightTranslation K g u) s =
        inner ℂ (Γ s) (Lp.haarRightTranslation K g u) :=
      kernelOperator_apply_eq_inner μ κ _ s
    _ = inner ℂ ((Lp.haarRightTranslation K g).symm (Γ s)) u := by
      simpa only [LinearIsometryEquiv.symm_symm] using
        ((Lp.haarRightTranslation K g).symm.inner_map_eq_flip (Γ s) u).symm
    _ = inner ℂ (Γ (s * g)) u := congrArg (fun v => inner ℂ v u) hΓ
    _ = kernelOperator μ κ u (s * g) :=
      (kernelOperator_apply_eq_inner μ κ u (s * g)).symm

/-- The Haar convolution operator on `L²` commutes with right translation. -/
theorem kernelOperator_toLp_haarRightTranslation_comm
    (f : C(K, ℂ)) (g : K) :
    let κ : C(K × K, ℂ) := f.comp
      ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
    let T := (toLp (E := ℂ) (2 : ℝ≥0∞)
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) ℂ).comp
        (kernelOperator
          (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) κ)
    T.comp (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap =
      (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap.comp T := by
  let κ : C(K × K, ℂ) := f.comp
    ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
  let C := kernelOperator μ κ
  apply ContinuousLinearMap.ext
  intro u
  have hC : C (Lp.haarRightTranslation K g u) =
      ({ toFun := fun s => C u (s * g)
         continuous_toFun := (C u).continuous.comp
           (continuous_id.mul continuous_const) } : C(K, ℂ)) := by
    ext s
    exact kernelOperator_haarRightTranslation_apply K f g u s
  calc
    toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (C (Lp.haarRightTranslation K g u)) =
        toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ
          { toFun := fun s => C u (s * g)
            continuous_toFun := (C u).continuous.comp
              (continuous_id.mul continuous_const) } :=
      congrArg (toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ) hC
    _ = Lp.haarRightTranslation K g (toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (C u)) :=
      Lp.haarRightTranslation_toLp K g (C u)

private theorem haarRightTranslation_inv_adjoint (g : K) :
    (Lp.haarRightTranslation K (g⁻¹)).toLinearIsometry.toContinuousLinearMap.adjoint =
      (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  simpa only [LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, map_inv, LinearIsometryEquiv.coe_inv] using
    (Lp.haarRightTranslation K g).inner_map_eq_flip x y

/-- The adjoint Haar convolution operator commutes with right translation. -/
theorem kernelOperator_toLp_adjoint_haarRightTranslation_comm
    (f : C(K, ℂ)) (g : K) :
    let κ : C(K × K, ℂ) := f.comp
      ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
    let T := (toLp (E := ℂ) (2 : ℝ≥0∞)
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) ℂ).comp
        (kernelOperator
          (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) κ)
    T.adjoint.comp
        (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap =
      (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap.comp
        T.adjoint := by
  have h := congrArg (fun A : H →L[ℂ] H => A.adjoint)
    (kernelOperator_toLp_haarRightTranslation_comm K f (g⁻¹))
  simpa only [ContinuousLinearMap.adjoint_comp,
    haarRightTranslation_inv_adjoint K g] using h.symm

/-- The product of Haar convolution with its adjoint commutes with right translation. -/
theorem kernelOperator_toLp_comp_adjoint_haarRightTranslation_comm
    (f : C(K, ℂ)) (g : K) :
    let κ : C(K × K, ℂ) := f.comp
      ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
    let T := (toLp (E := ℂ) (2 : ℝ≥0∞)
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) ℂ).comp
        (kernelOperator
          (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) κ)
    (T.comp T.adjoint).comp
        (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap =
      (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap.comp
        (T.comp T.adjoint) := by
  let κ : C(K × K, ℂ) := f.comp
    ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
  let T := (toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ).comp (kernelOperator μ κ)
  have hT :
      T.comp (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap =
        (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap.comp T :=
    kernelOperator_toLp_haarRightTranslation_comm K f g
  have hA :
      T.adjoint.comp
          (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap =
        (Lp.haarRightTranslation K g).toLinearIsometry.toContinuousLinearMap.comp
          T.adjoint :=
    kernelOperator_toLp_adjoint_haarRightTranslation_comm K f g
  apply ContinuousLinearMap.ext
  intro u
  calc
    T (T.adjoint (Lp.haarRightTranslation K g u)) =
        T (Lp.haarRightTranslation K g (T.adjoint u)) :=
      congrArg T (congrArg (fun A : H →L[ℂ] H => A u) hA)
    _ = Lp.haarRightTranslation K g (T (T.adjoint u)) :=
      congrArg (fun A : H →L[ℂ] H => A (T.adjoint u)) hT

variable [T2Space K]

/-- At every nonidentity point, some continuous convolution kernel has a nonzero
right-translation defect as an operator on Haar L². -/
theorem exists_haarRightTranslation_sub_id_comp_kernelOperator_toLp_ne_zero
    (x : K) (hx : x ≠ 1) :
    ∃ f : C(K, ℂ),
      let κ : C(K × K, ℂ) := f.comp
        ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
      let T := (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞)
        (MeasureTheory.Measure.haarMeasure
          (⊤ : TopologicalSpace.PositiveCompacts K)) ℂ).comp
          (ContinuousMap.kernelOperator
            (MeasureTheory.Measure.haarMeasure
              (⊤ : TopologicalSpace.PositiveCompacts K)) κ)
      ((MeasureTheory.Lp.haarRightTranslation K x).toLinearIsometry.toContinuousLinearMap -
        ContinuousLinearMap.id ℂ
          (MeasureTheory.Lp ℂ (2 : ℝ≥0∞)
            (MeasureTheory.Measure.haarMeasure
              (⊤ : TopologicalSpace.PositiveCompacts K)))).comp T ≠ 0 := by
  let nu : Measure K := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
  obtain ⟨f, h, hfh⟩ := exists_kernelOperator_comp_mul_inv_ne nu hx
  refine ⟨f, ?_⟩
  dsimp only
  intro hzero
  let κ : C(K × K, ℂ) := f.comp
    ⟨(fun p : K × K => p.1 * p.2⁻¹), continuous_fst.mul continuous_snd.inv⟩
  let J : C(K, ℂ) →L[ℂ] Lp ℂ (2 : ℝ≥0∞) nu :=
    ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) nu ℂ
  let y : C(K, ℂ) := kernelOperator nu κ (J h)
  have hzero_apply := congrArg
    (fun A : Lp ℂ (2 : ℝ≥0∞) nu →L[ℂ] Lp ℂ (2 : ℝ≥0∞) nu => A (J h)) hzero
  have hfixed : Lp.haarRightTranslation K x (J y) = J y := by
    apply sub_eq_zero.mp
    simpa only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      ContinuousLinearMap.id_apply, _root_.zero_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] using hzero_apply
  have hpoint : ∀ s : K, y (s * x) = y s :=
    (Lp.haarRightTranslation_toLp_eq_iff K x y y).mp hfixed
  exact hfh (by simpa only [one_mul] using hpoint (1 : K))

end ContinuousMap
