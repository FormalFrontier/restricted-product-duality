module

/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/
public import GroupTheory.Topology.PontryaginDual.Discrete.Surjective
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Lemmas
public import RestrictedProductDuality.Analysis.HaarCharacter

/-!
# Compact Pontryagin biduality

For a compact Hausdorff commutative topological group, evaluation is a
continuous multiplicative equivalence with the entire compact-open Pontryagin
bidual. Its inverse reconstructs every character value, and evaluation and
reconstruction commute with continuous multiplicative morphisms.

This is the compact Hausdorff abelian case of the Pontryagin–van Kampen
duality theorem; see E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*,
Vol. I, second edition, Springer, 1979.

The proof uses the discrete evaluation-surjectivity and triangle API from
Group Theory, Mathlib's compact-open dual and quotient topology, and this
library's compact character separation. Discrete biduality makes restriction
along evaluation injective; separation in the quotient by its closed image
then gives surjectivity. This direct argument proves the supporting
`evalHom_surjective_of_compact` for a group with only a compact Hausdorff
topology: it requires neither commutativity nor continuous group operations.
-/

@[expose] public section

universe u v

namespace PontryaginDual

/-- Evaluation onto the entire bidual is surjective for a compact Hausdorff group.
No continuity of the source group operations is needed. -/
theorem evalHom_surjective_of_compact (A : Type u) [Group A]
    [TopologicalSpace A] [CompactSpace A] [T2Space A] :
    Function.Surjective (PontryaginDual.evalHom A) := by
  classical
  let D := PontryaginDual A
  let B := PontryaginDual D
  let _ : DiscreteTopology D := inferInstance
  let _ : LocallyCompactSpace A := inferInstance
  let _ : LocallyCompactSpace D := inferInstance
  let _ : LocallyCompactPair A Circle := inferInstance
  let _ : LocallyCompactPair D Circle := inferInstance
  let _ : CompactSpace B := inferInstance
  let _ : T2Space B := inferInstance
  let _ : IsTopologicalGroup B := inferInstance
  let e : A →ₜ* B := PontryaginDual.eval A
  let t : D →ₜ* PontryaginDual B := PontryaginDual.eval D
  let r : PontryaginDual B →ₜ* D := PontryaginDual.map e
  have ht_surjective : Function.Surjective t :=
    PontryaginDual.eval_surjective_of_discrete D
  have htri (χ : D) : r (t χ) = χ :=
    congrArg (fun F : D →ₜ* D => F χ)
      (PontryaginDual.map_eval_comp_eval (A := A))
  have hr_injective : Function.Injective r := by
    intro Ξ₁ Ξ₂ h
    obtain ⟨χ₁, h₁⟩ := ht_surjective Ξ₁
    obtain ⟨χ₂, h₂⟩ := ht_surjective Ξ₂
    have hχ : χ₁ = χ₂ := by
      calc
        χ₁ = r (t χ₁) := (htri χ₁).symm
        _ = r Ξ₁ := congrArg r h₁
        _ = r Ξ₂ := h
        _ = r (t χ₂) := congrArg r h₂.symm
        _ = χ₂ := htri χ₂
    exact h₁.symm.trans ((congrArg t hχ).trans h₂)
  have hrestrict (Ξ : PontryaginDual B) (a : A) :
      (r Ξ) a = Ξ (e a) := by
    obtain ⟨χ, hχ⟩ := ht_surjective Ξ
    calc
      (r Ξ) a = (r (t χ)) a :=
        congrArg (fun Z : PontryaginDual B => (r Z) a) hχ.symm
      _ = χ a := congrArg (fun η : D => η a) (htri χ)
      _ = (e a) χ :=
        (PontryaginDual.eval_apply (A := A) a χ).symm
      _ = (t χ) (e a) :=
        (PontryaginDual.eval_apply (A := D) χ (e a)).symm
      _ = Ξ (e a) :=
        congrArg (fun Z : PontryaginDual B => Z (e a)) hχ
  let H : Subgroup B := e.toMonoidHom.range
  have hHcompact : IsCompact (H : Set B) := by
    change IsCompact (Set.range e)
    exact isCompact_range e.continuous
  have hHclosed : IsClosed (H : Set B) := hHcompact.isClosed
  let _ : IsClosed (H : Set B) := hHclosed
  let _ : H.Normal := inferInstance
  let Q := B ⧸ H
  let _ : CompactSpace Q := inferInstance
  let _ : IsTopologicalGroup Q := inferInstance
  let _ : T3Space Q := QuotientGroup.instT3Space H
  let _ : T2Space Q := inferInstance
  let q : B →ₜ* Q :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := by
        apply QuotientGroup.continuous_mk }
  have hq_mem (b : B) : q b = 1 ↔ b ∈ H := by
    change (QuotientGroup.mk' H) b = 1 ↔ b ∈ H
    exact QuotientGroup.eq_one_iff b
  have he_surjective : Function.Surjective e := by
    intro Φ
    by_contra hΦ
    have hΦ_not_mem : Φ ∉ H := by
      intro hmem
      exact hΦ hmem
    have hqΦ : q Φ ≠ 1 := by
      intro h
      exact hΦ_not_mem ((hq_mem Φ).mp h)
    obtain ⟨θ, hθ⟩ :=
      _root_.exists_continuous_character_ne_one (K := Q) (x := q Φ) hqΦ
    let Ξ : PontryaginDual B := θ.comp q
    have hΞkills (a : A) : Ξ (e a) = 1 := by
      change θ (q (e a)) = 1
      rw [(hq_mem (e a)).mpr ⟨a, rfl⟩]
      exact _root_.map_one θ
    have hrΞ : r Ξ = 1 := by
      apply DFunLike.ext
      intro a
      calc
        (r Ξ) a = Ξ (e a) := hrestrict Ξ a
        _ = 1 := hΞkills a
        _ = (1 : D) a := rfl
    have hr_one : r (1 : PontryaginDual B) = 1 := by
      apply DFunLike.ext
      intro a
      calc
        (r (1 : PontryaginDual B)) a =
            (1 : PontryaginDual B) (e a) := hrestrict 1 a
        _ = (1 : D) a := rfl
    have hΞ : Ξ = 1 := hr_injective (hrΞ.trans hr_one.symm)
    apply hθ
    calc
      θ (q Φ) = Ξ Φ := rfl
      _ = (1 : PontryaginDual B) Φ :=
        congrArg (fun Z : PontryaginDual B => Z Φ) hΞ
      _ = 1 := rfl
  intro Φ
  obtain ⟨a, ha⟩ := he_surjective Φ
  have hbridge : e a = PontryaginDual.evalHom A a :=
    congrArg (fun f : A →* B => f a)
      (PontryaginDual.eval_toMonoidHom A)
  exact ⟨a, hbridge.symm.trans ha⟩

/-- Evaluation as a continuous multiplicative equivalence between a compact
Hausdorff commutative topological group and its entire compact-open Pontryagin bidual.

This is the compact Hausdorff abelian case of the Pontryagin–van Kampen duality
theorem (Hewitt and Ross, *Abstract Harmonic Analysis*, Vol. I, second edition,
Springer, 1979). -/
noncomputable def evalEquivOfCompact (A : Type u) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [T2Space A] :
    A ≃ₜ* PontryaginDual (PontryaginDual A) := by
  classical
  let hSURJK : Function.Surjective (PontryaginDual.evalHom A) :=
    PontryaginDual.evalHom_surjective_of_compact A
  have h_inj : Function.Injective (PontryaginDual.evalHom A) := by
    classical
    intro a b hab
    by_contra hne
    have hne_one : a * b⁻¹ ≠ 1 := by
      intro h
      apply hne
      calc
        a = (a * b⁻¹) * b := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = 1 * b := congrArg (fun t : A => t * b) h
        _ = b := one_mul b
    obtain ⟨χ, hχ⟩ :
        ∃ χ : A →ₜ* Circle, χ (a * b⁻¹) ≠ 1 :=
      _root_.exists_continuous_character_ne_one hne_one
    have hχab : χ a = χ b := by
      have hpoint :
          PontryaginDual.evalHom A a χ =
            PontryaginDual.evalHom A b χ :=
        congrArg
          (fun z : PontryaginDual (PontryaginDual A) => z χ) hab
      calc
        χ a = PontryaginDual.evalHom A a χ :=
          (PontryaginDual.evalHom_apply (A := A) a χ).symm
        _ = PontryaginDual.evalHom A b χ := hpoint
        _ = χ b := PontryaginDual.evalHom_apply (A := A) b χ
    apply hχ
    calc
      χ (a * b⁻¹) = χ a * (χ b)⁻¹ := by
        rw [_root_.map_mul, _root_.map_inv]
      _ = χ b * (χ b)⁻¹ := by rw [hχab]
      _ = 1 := mul_inv_cancel (χ b)
  have h_preimage_unique
      (hs : Function.Surjective (PontryaginDual.evalHom A))
      (Φ : PontryaginDual (PontryaginDual A))
      (a : A) (ha : PontryaginDual.evalHom A a = Φ) :
      Classical.choose (hs Φ) = a := by
    apply h_inj
    exact (Classical.choose_spec (hs Φ)).trans ha.symm
  let e : A ≃* PontryaginDual (PontryaginDual A) :=
    { toFun := PontryaginDual.evalHom A
      invFun := fun Φ => Classical.choose (hSURJK Φ)
      left_inv := fun a =>
        h_preimage_unique hSURJK (PontryaginDual.evalHom A a) a rfl
      right_inv := fun Φ => Classical.choose_spec (hSURJK Φ)
      map_mul' := fun a b => (PontryaginDual.evalHom A).map_mul a b }
  have h_forward : Continuous (PontryaginDual.evalHom A) := by
    have h_eval : Continuous
        ((PontryaginDual.eval A).toMonoidHom :
          A → PontryaginDual (PontryaginDual A)) :=
      (PontryaginDual.eval A).continuous
    rw [PontryaginDual.eval_toMonoidHom A] at h_eval
    exact h_eval
  have h_e : Continuous
      (e.toEquiv : A → PontryaginDual (PontryaginDual A)) := by
    exact h_forward
  have h_inverse : Continuous
      (e.toEquiv.symm : PontryaginDual (PontryaginDual A) → A) :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := e.toEquiv) h_e
  exact
    { toMulEquiv := e
      continuous_toFun := h_e
      continuous_invFun := h_inverse }

/-- The multiplicative morphism underlying compact bidual evaluation is
 the original evaluation morphism. -/
@[simp] theorem evalEquivOfCompact_toMonoidHom (A : Type u) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [T2Space A] :
    (PontryaginDual.evalEquivOfCompact A :
      A →* PontryaginDual (PontryaginDual A)) = PontryaginDual.evalHom A := by
  rfl

/-- Compact bidual evaluation evaluates each character at the given point. -/
@[simp] theorem evalEquivOfCompact_apply (A : Type u) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [T2Space A]
    (a : A) (χ : PontryaginDual A) :
    PontryaginDual.evalEquivOfCompact A a χ = χ a := by
  exact PontryaginDual.evalHom_apply a χ

/-- The inverse of compact bidual evaluation reconstructs every character
 value of the bidual element. -/
@[simp] theorem evalEquivOfCompact_symm_apply (A : Type u) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [T2Space A]
    (Φ : PontryaginDual (PontryaginDual A)) (χ : PontryaginDual A) :
    χ ((PontryaginDual.evalEquivOfCompact A).symm Φ) = Φ χ := by
  have h_eval :
      (PontryaginDual.evalEquivOfCompact A
        ((PontryaginDual.evalEquivOfCompact A).symm Φ)) χ = Φ χ :=
    congrArg (fun z : PontryaginDual (PontryaginDual A) => z χ)
      ((PontryaginDual.evalEquivOfCompact A).apply_symm_apply Φ)
  simpa only [PontryaginDual.evalEquivOfCompact_apply] using h_eval

/-- Inverse compact bidual evaluation commutes with a continuous morphism,
 as tested against every character of its target. -/
theorem evalEquivOfCompact_symm_naturality
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A]
    {B : Type v} [Monoid B] [TopologicalSpace B]
    (f : A →ₜ* B) (Φ : PontryaginDual (PontryaginDual A))
    (ψ : PontryaginDual B) :
    ψ (f ((PontryaginDual.evalEquivOfCompact A).symm Φ)) =
      Φ (ψ.comp f) := by
  exact PontryaginDual.evalEquivOfCompact_symm_apply A Φ (ψ.comp f)

/-- Compact bidual evaluation commutes with a continuous morphism,
 as tested against every character of its target. -/
theorem evalEquivOfCompact_naturality
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A]
    {B : Type v} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B]
    (f : A →ₜ* B) (a : A) (ψ : PontryaginDual B) :
    (PontryaginDual.evalEquivOfCompact B (f a)) ψ =
      (PontryaginDual.evalEquivOfCompact A a) (ψ.comp f) := by
  exact
    (PontryaginDual.evalEquivOfCompact_apply B (f a) ψ).trans
      (PontryaginDual.evalEquivOfCompact_apply A a (ψ.comp f)).symm

end PontryaginDual
