/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.PontryaginDual.Compact
public import GroupTheory.Topology.PontryaginDual.Discrete.Surjective
public import GroupTheory.Topology.PontryaginDual.Restriction
public import GroupTheory.Topology.ContinuousMonoidHom.Quotient
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Surjectivity and openness of evaluation with a compact open subgroup

For a Hausdorff abelian topological group with a compact open subgroup, evaluation onto the
Circle-valued compact-open bidual is surjective and open. The restriction kernel in
the dual is compact; its annihilator is an open subgroup of the bidual. Evaluation
identifies the given compact subgroup homeomorphically with that annihilator.

These are the compact-open subgroup cases of the surjectivity and openness
assertions in classical Pontryagin–van Kampen duality; see Hewitt and Ross below.

The proofs combine Mathlib's Circle-valued compact-open dual and topology APIs,
GroupTheory's discrete evaluation, subgroup restriction and quotient-pullback APIs,
and this library's compact evaluation theorem. Reconstruction descends a character
along restriction after removing evaluation at a quotient lift; openness follows
from the compact subgroup and translations.

## References

- E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, second edition,
  Springer, 1979: the Pontryagin–van Kampen duality theorem.
-/

@[expose] public section

open Set Topology

universe u v

namespace PontryaginDual

private theorem exists_compact_preimage_of_discrete
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] (f : X → Y) (hf : Function.Surjective f)
    (s : Set Y) (hs : IsCompact s) :
    ∃ l : Set X, IsCompact l ∧ f '' l = s := by
  classical
  have hsfin : s.Finite :=
    hs.finite (isDiscrete_iff_discreteTopology.mpr inferInstance)
  let _ : Finite s := hsfin.to_subtype
  let g : s → X := fun y => Classical.choose (hf y.val)
  have hg (y : s) : f (g y) = y.val := Classical.choose_spec (hf y.val)
  refine ⟨Set.range g, (Set.finite_range g).isCompact, ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, hxy⟩
    rw [← hxy, hg]
    exact z.property
  · intro hy
    exact ⟨g ⟨y, hy⟩, Set.mem_range_self _, hg ⟨y, hy⟩⟩

private theorem evalHom_compactOpen_properties
    (A : Type u) [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T0Space A]
    (H : Subgroup A) (hHc : IsCompact (H : Set A))
    (hHo : IsOpen (H : Set A)) :
    Function.Surjective (evalHom A) ∧ IsOpenMap (evalHom A) := by
  classical
  let _ : LocallyCompactSpace A :=
    hHc.locallyCompactSpace_of_mem_nhds_of_group
      (hHo.mem_nhds H.one_mem)
  let _ : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  let Q := A ⧸ H
  let _ : DiscreteTopology Q := QuotientGroup.discreteTopology_iff.mpr hHo
  let i : H →ₜ* A := ⟨H.subtype, continuous_subtype_val⟩
  have hi (h : H) : i h = (h : A) := by
    calc
      i h = i.toMonoidHom h :=
        (DFunLike.congr_fun (ContinuousMonoidHom.coe_toMonoidHom i) h).symm
      _ = (h : A) := by simp only [i, Subgroup.coe_subtype]
  let q : A →ₜ* Q := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  let r : PontryaginDual A →ₜ* PontryaginDual H := map i
  let j : PontryaginDual Q →ₜ* PontryaginDual A := map q
  have hr : Function.Surjective r := map_subtype_surjective_of_isOpen H hHo
  have hq : IsQuotientMap q := QuotientGroup.isQuotientMap_mk H
  have hqsurj : Function.Surjective q := hq.surjective
  have hqcover := exists_compact_preimage_of_discrete q hqsurj
  have hropen : IsOpenMap r := fun _ _ => isOpen_discrete _
  have hrq : IsQuotientMap r := hropen.isQuotientMap r.continuous hr
  have hrcover := exists_compact_preimage_of_discrete r hr
  let Eq := ContinuousMonoidHom.quotientPullbackHomeomorph (K := Circle) q hq hqcover
  let Er := ContinuousMonoidHom.quotientPullbackHomeomorph (K := Circle) r hrq hrcover
  have hEq (ξ : PontryaginDual Q) (a : A) : (Eq ξ).val a = ξ (q a) :=
    ContinuousMonoidHom.quotientPullbackHomeomorph_apply_apply q hq hqcover ξ a
  have hEr (θ : PontryaginDual (PontryaginDual H)) (χ : PontryaginDual A) :
      (Er θ).val χ = θ (r χ) :=
    ContinuousMonoidHom.quotientPullbackHomeomorph_apply_apply r hrq hrcover θ χ
  let N : Subgroup (PontryaginDual A) := r.toMonoidHom.ker
  have hjN (ξ : PontryaginDual Q) : j ξ ∈ N := by
    change r (j ξ) = 1
    apply PontryaginDual.ext
    intro h
    have hqh : q (h : A) = 1 :=
      (QuotientGroup.eq_one_iff (h : A)).mpr h.property
    simp only [r, j, map_apply, hi, hqh, _root_.map_one, one_apply]
  have hjpre (χ : PontryaginDual A) (hχ : χ ∈ N) :
      ∃ ξ : PontryaginDual Q, j ξ = χ := by
    have hχr : r χ = 1 := hχ
    have hf : Function.FactorsThrough χ q := by
      intro a b hab
      have hqab : q (a / b) = 1 := by
        rw [_root_.map_div q, hab]
        exact div_eq_one.mpr rfl
      have habH : a / b ∈ H :=
        (QuotientGroup.eq_one_iff (a / b)).mp hqab
      have hval : χ (a / b) = 1 := by
        have he := DFunLike.congr_fun hχr (⟨a / b, habH⟩ : H)
        simpa only [r, map_apply, hi, one_apply] using he
      exact div_eq_one.mp (by simpa only [_root_.map_div χ] using hval)
    obtain ⟨ξ, hξ⟩ := Eq.surjective ⟨χ, hf⟩
    refine ⟨ξ, ?_⟩
    apply PontryaginDual.ext
    intro a
    calc
      j ξ a = ξ (q a) := map_apply q ξ a
      _ = (Eq ξ).val a := (hEq ξ a).symm
      _ = χ a := DFunLike.congr_fun (congrArg Subtype.val hξ) a
  have hNrange : Set.range j = (N : Set (PontryaginDual A)) := by
    ext χ
    constructor
    · rintro ⟨ξ, rfl⟩
      exact hjN ξ
    · exact hjpre χ
  have hNcompact : IsCompact (N : Set (PontryaginDual A)) := by
    rw [← hNrange]
    simpa only [Set.image_univ] using
      (isCompact_univ.image (ContinuousMapClass.map_continuous j))
  let _ : CompactSpace N := isCompact_iff_compactSpace.mp hNcompact
  let k : N →ₜ* PontryaginDual A := ⟨N.subtype, continuous_subtype_val⟩
  have hk (n : N) : k n = (n : PontryaginDual A) := by
    calc
      k n = k.toMonoidHom n :=
        (DFunLike.congr_fun (ContinuousMonoidHom.coe_toMonoidHom k) n).symm
      _ = (n : PontryaginDual A) := by simp only [k, Subgroup.coe_subtype]
  let s : PontryaginDual (PontryaginDual A) →ₜ* PontryaginDual N := map k
  let U : Subgroup (PontryaginDual (PontryaginDual A)) := s.toMonoidHom.ker
  have hUopen : IsOpen (U : Set (PontryaginDual (PontryaginDual A))) := by
    change IsOpen (s ⁻¹' ({1} : Set (PontryaginDual N)))
    exact (isOpen_discrete _).preimage s.continuous
  have hU (Φ : PontryaginDual (PontryaginDual A)) :
      Φ ∈ U ↔ ∀ χ : PontryaginDual A, χ ∈ N → Φ χ = 1 := by
    constructor
    · intro hΦ χ hχ
      have hΦs : s Φ = 1 := hΦ
      have he := DFunLike.congr_fun hΦs (⟨χ, hχ⟩ : N)
      simpa only [s, map_apply, hk, one_apply] using he
    · intro hΦ
      change s Φ = 1
      apply PontryaginDual.ext
      intro n
      simpa only [s, map_apply, hk, one_apply] using hΦ n.val n.property
  have descend (ρ : PontryaginDual (PontryaginDual A))
      (hρ : ∀ χ : PontryaginDual A, χ ∈ N → ρ χ = 1) :
      ∃ θ : PontryaginDual (PontryaginDual H), ∀ χ : PontryaginDual A, θ (r χ) = ρ χ := by
    have hf : Function.FactorsThrough ρ r := by
      intro χ ψ hχψ
      have hmem : χ / ψ ∈ N := by
        change r (χ / ψ) = 1
        rw [_root_.map_div r, hχψ]
        exact div_eq_one.mpr rfl
      exact div_eq_one.mp (by simpa only [_root_.map_div ρ] using hρ (χ / ψ) hmem)
    obtain ⟨θ, hθ⟩ := Er.surjective ⟨ρ, hf⟩
    refine ⟨θ, ?_⟩
    intro χ
    calc
      θ (r χ) = (Er θ).val χ := (hEr θ χ).symm
      _ = ρ χ := DFunLike.congr_fun (congrArg Subtype.val hθ) χ
  have hraw : Function.Surjective (evalHom A) := by
    intro Φ
    obtain ⟨d, hd⟩ := eval_surjective_of_discrete Q (map j Φ)
    obtain ⟨a₀, ha₀⟩ := hqsurj d
    let ρ : PontryaginDual (PontryaginDual A) := Φ / evalHom A a₀
    have hρ_apply (χ : PontryaginDual A) : ρ χ = Φ χ / χ a₀ := by
      simpa only [ρ, evalHom_apply] using
        _root_.map_div (evalHom (PontryaginDual A) χ) Φ (evalHom A a₀)
    have hρ : ∀ χ : PontryaginDual A, χ ∈ N → ρ χ = 1 := by
      intro χ hχ
      obtain ⟨ξ, rfl⟩ := hjpre χ hχ
      have hpoint : ξ d = Φ (j ξ) := by
        simpa only [eval_apply, map_apply] using DFunLike.congr_fun hd ξ
      rw [hρ_apply, map_apply, ha₀, ← hpoint]
      exact div_eq_one.mpr rfl
    obtain ⟨θ, hθ⟩ := descend ρ hρ
    obtain ⟨h, hh⟩ := evalHom_surjective_of_compact H θ
    refine ⟨a₀ * (h : A), ?_⟩
    apply PontryaginDual.ext
    intro χ
    have hres : ρ χ = χ (h : A) := by
      calc
        ρ χ = θ (r χ) := (hθ χ).symm
        _ = (r χ) h := by
          simpa only [evalHom_apply] using (DFunLike.congr_fun hh (r χ)).symm
        _ = χ (h : A) := by simpa only [hi] using map_apply i χ h
    have hpoint : Φ χ / χ a₀ = χ (h : A) := (hρ_apply χ).symm.trans hres
    calc
      evalHom A (a₀ * (h : A)) χ = χ (a₀ * (h : A)) := evalHom_apply _ _
      _ = χ a₀ * χ (h : A) := _root_.map_mul χ _ _
      _ = χ (h : A) * χ a₀ := mul_comm _ _
      _ = (Φ χ / χ a₀) * χ a₀ := by rw [hpoint]
      _ = Φ χ := div_mul_cancel _ _
  have hlocal_surj (Φ : PontryaginDual (PontryaginDual A)) (hΦ : Φ ∈ U) :
      ∃ h : H, evalHom A (h : A) = Φ := by
    obtain ⟨θ, hθ⟩ := descend Φ ((hU Φ).mp hΦ)
    obtain ⟨h, hh⟩ := evalHom_surjective_of_compact H θ
    refine ⟨h, ?_⟩
    apply PontryaginDual.ext
    intro χ
    calc
      evalHom A (h : A) χ = χ (h : A) := evalHom_apply _ _
      _ = (r χ) h := by simpa only [hi] using (map_apply i χ h).symm
      _ = θ (r χ) := by
        simpa only [evalHom_apply] using DFunLike.congr_fun hh (r χ)
      _ = Φ χ := hθ χ
  have hEvalH (h : H) : evalHom A (h : A) ∈ U := by
    apply (hU _).mpr
    intro χ hχ
    have hχr : r χ = 1 := hχ
    have he := DFunLike.congr_fun hχr h
    simpa only [evalHom_apply, r, map_apply, hi, one_apply] using he
  let eH : H → U := fun h => ⟨evalHom A (h : A), hEvalH h⟩
  have heHsurj : Function.Surjective eH := by
    intro Φ
    obtain ⟨h, hh⟩ := hlocal_surj Φ.val Φ.property
    exact ⟨h, Subtype.ext hh⟩
  have heHinj : Function.Injective eH := by
    intro h h' heq
    have hh : evalHom H h = evalHom H h' := by
      apply PontryaginDual.ext
      intro η
      obtain ⟨χ, rfl⟩ := hr η
      have he := congrArg (fun u : U => u.val χ) heq
      simpa only [evalHom_apply, r, map_apply, hi, eH] using he
    apply (evalEquivOfCompact H).injective
    change evalHom H h = evalHom H h'
    exact hh
  have heval : Continuous (evalHom A) := by
    rw [← eval_toMonoidHom A]
    exact (eval A).continuous
  have heHcont : Continuous eH :=
    (heval.comp continuous_subtype_val).subtype_mk (fun h => hEvalH h)
  let e : H ≃ U :=
    { toFun := eH
      invFun := fun Φ => Classical.choose (heHsurj Φ)
      left_inv := fun h => heHinj (Classical.choose_spec (heHsurj (eH h)))
      right_inv := fun Φ => Classical.choose_spec (heHsurj Φ) }
  have hecont : Continuous e := heHcont
  let L : H ≃ₜ U :=
    { toEquiv := e
      continuous_toFun := hecont
      continuous_invFun := hecont.continuous_symm_of_equiv_compact_to_t2 }
  refine ⟨hraw, ?_⟩
  intro V hV
  let W : A → Set H := fun a => {h : H | a * (h : A) ∈ V}
  let S : A → Set (PontryaginDual (PontryaginDual A)) := fun a =>
    Homeomorph.mulLeft (evalHom A a) ''
      ((Subtype.val : U → PontryaginDual (PontryaginDual A)) '' (L '' W a))
  have hW (a : A) : IsOpen (W a) :=
    hV.preimage (continuous_const.mul continuous_subtype_val)
  have hS (a : A) : IsOpen (S a) :=
    (Homeomorph.mulLeft (evalHom A a)).isOpenMap _
      (hUopen.isOpenMap_subtype_val _ (L.isOpenMap _ (hW a)))
  have himage : evalHom A '' V = ⋃ a : A, S a := by
    ext Φ
    constructor
    · rintro ⟨a, ha, rfl⟩
      apply Set.mem_iUnion.mpr
      refine ⟨a, ?_⟩
      refine ⟨(L (1 : H) : PontryaginDual (PontryaginDual A)), ?_, ?_⟩
      · refine ⟨L 1, ?_, rfl⟩
        refine ⟨1, ?_, rfl⟩
        simpa only [W, Set.mem_ofPred_eq, Subgroup.coe_one, mul_one] using ha
      · change evalHom A a * evalHom A (1 : A) = evalHom A a
        rw [_root_.map_one (evalHom A), mul_one]
    · intro hΦ
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hΦ
      rcases ha with ⟨z, hz, hΦ⟩
      rcases hz with ⟨u, hu, rfl⟩
      rcases hu with ⟨h, hh, rfl⟩
      refine ⟨a * (h : A), hh, ?_⟩
      calc
        evalHom A (a * (h : A)) = evalHom A a * evalHom A (h : A) :=
          _root_.map_mul (evalHom A) _ _
        _ = Φ := hΦ
  rw [himage]
  exact isOpen_iUnion hS

/-- Evaluation on a Hausdorff abelian topological group with a compact open subgroup is surjective.

This is the compact-open subgroup case of the surjectivity assertion in Pontryagin–van Kampen
duality (Hewitt and Ross, *Abstract Harmonic Analysis*, Vol. I, 1979). The proof combines Mathlib's
Circle-valued compact-open dual and topology APIs, GroupTheory's discrete evaluation, restriction
and quotient-pullback APIs, and this library's compact evaluation theorem. -/
theorem evalHom_surjective_of_compactOpen
    (A : Type u) [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T0Space A]
    (H : Subgroup A) (hHc : IsCompact (H : Set A))
    (hHo : IsOpen (H : Set A)) :
    Function.Surjective (evalHom A) :=
  (evalHom_compactOpen_properties A H hHc hHo).1

/-- Evaluation on a Hausdorff abelian topological group with a compact open subgroup is an open map.

This is the compact-open subgroup case of the openness assertion in Pontryagin–van Kampen duality
(Hewitt and Ross, *Abstract Harmonic Analysis*, Vol. I, 1979). The proof combines Mathlib's
Circle-valued compact-open dual and topology APIs, GroupTheory's discrete evaluation, restriction
and quotient-pullback APIs, and this library's compact evaluation theorem. -/
theorem isOpenMap_evalHom_of_compactOpen
    (A : Type u) [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T0Space A]
    (H : Subgroup A) (hHc : IsCompact (H : Set A))
    (hHo : IsOpen (H : Set A)) :
    IsOpenMap (evalHom A) :=
  (evalHom_compactOpen_properties A H hHc hHo).2

end PontryaginDual
