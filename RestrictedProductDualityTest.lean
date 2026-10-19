/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-!
# Public-import clients for restricted-product duality

These private audit handles compile using only the public umbrella import. In
particular, the cyclic examples have nontrivial coordinate groups and infinite
index type; the exceptional map deliberately fails subgroup preservation at zero.
-/

set_option warningAsError true

noncomputable section

open Set
open scoped RestrictedProduct

namespace RestrictedProductTest

universe u v w

/-- An arbitrary-universe downstream use of the exported evaluation API. -/
private theorem pairingCharacter_generic
    {ι : Type u} {X : ι → Type v} {Y : ι → Type w}
    [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))
    (e : ∀ i, X i →* Y i →* Circle)
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i)))
    (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, V i]) :
    RestrictedProduct.toPontryaginDual U V e horth hUopen hVopen he y x =
      RestrictedProduct.pairing U V e x y := by
  exact RestrictedProduct.toPontryaginDual_apply U V e horth hUopen hVopen he y x

namespace Cyclic

open RestrictedProduct Multiplicative

private abbrev Z2 := Multiplicative (ZMod 2)

local instance : TopologicalSpace Z2 := ⊥
local instance : DiscreteTopology Z2 := ⟨rfl⟩

private def bot (ι : Type u) : ι → Subgroup Z2 := fun _ ↦ ⊥
private def top (ι : Type u) : ι → Subgroup Z2 := fun _ ↦ ⊤
private def bicharacter (ι : Type u) : ι → Z2 →* Z2 →* Circle :=
  fun _ ↦ zmodBicharacter 2

/-- Both extreme right annihilator orientations are genuine equalities. -/
private theorem rightAnnihilator_bot :
    (⊤ : Subgroup Z2) = rightAnnihilator (⊥ : Subgroup Z2) (zmodBicharacter 2) := by
  ext y
  simp [rightAnnihilator]

private theorem rightAnnihilator_top :
    (⊥ : Subgroup Z2) = rightAnnihilator (⊤ : Subgroup Z2) (zmodBicharacter 2) := by
  ext y
  constructor
  · intro hy
    have : y = 1 := by simpa using hy
    subst y
    simp [rightAnnihilator]
  · intro hy
    apply (zmodBicharacter_perfect 2).injective
    apply MonoidHom.ext
    intro x
    simpa [rightCharacter_apply] using (mem_rightAnnihilator.mp hy x (Subgroup.mem_top x))

/-- The ZMod 2 bicharacter is perfect also in the opposite direction. -/
private theorem leftPerfect : Function.Bijective (zmodBicharacter 2) := by
  have hsymm : zmodBicharacter 2 = rightCharacter (zmodBicharacter 2) := by
    apply MonoidHom.ext
    intro x
    apply MonoidHom.ext
    intro y
    simp [zmodBicharacter_apply, AddChar.zmod, mul_comm]
  rw [hsymm]
  exact zmodBicharacter_perfect 2

/-- The `⊥`/`⊤` right-annihilator orientation gives an infinite-index duality. -/
private noncomputable def dualityBotTopInfinite :
    (Πʳ _i : ℕ, [Z2, (⊤ : Subgroup Z2)]) ≃ₜ*
      PontryaginDual (Πʳ _i : ℕ, [Z2, (⊥ : Subgroup Z2)]) := by
  apply pontryaginDualEquiv (e := bicharacter ℕ)
  · intro i x hx y _hy
    have : x = 1 := by simpa using hx
    subst x
    simp
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ zmodBicharacter_perfect 2
  · exact fun _ ↦ rightAnnihilator_bot

/-- The `⊤`/`⊥` orientation requires the nontrivial opposite annihilator equality. -/
private noncomputable def dualityTopBotInfinite :
    (Πʳ _i : ℕ, [Z2, (⊥ : Subgroup Z2)]) ≃ₜ*
      PontryaginDual (Πʳ _i : ℕ, [Z2, (⊤ : Subgroup Z2)]) := by
  apply pontryaginDualEquiv (e := bicharacter ℕ)
  · intro i x _hx y hy
    have : y = 1 := by simpa using hy
    subst y
    simp
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ zmodBicharacter_perfect 2
  · exact fun _ ↦ rightAnnihilator_top

/-- The nontrivial cyclic pairing gives an infinite-index symmetric equivalence. -/
private noncomputable def symmetricInfinite :
    (Πʳ _i : ℕ, [Z2, (⊤ : Subgroup Z2)]) ≃ₜ*
      PontryaginDual (Πʳ _i : ℕ, [Z2, (⊥ : Subgroup Z2)]) := by
  apply symmetricPontryaginDualEquiv (e := bicharacter ℕ)
  · intro i x hx y hy
    have : y = 1 := by simpa using hy
    subst y
    simp
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ isOpen_discrete _
  · exact fun _ ↦ continuous_of_discreteTopology
  · exact fun _ ↦ leftPerfect
  · intro i
    ext x
    simp [leftAnnihilator, rightAnnihilator]

/-- Squaring is a nonidentity endomorphism of the nontrivial cyclic group. -/
private def square : Z2 →ₜ* Z2 :=
  ContinuousMonoidHom.mk (powMonoidHom 2) continuous_of_discreteTopology

private theorem square_nonidentity : square (Multiplicative.ofAdd 1) ≠
    (Multiplicative.ofAdd 1 : Z2) := by
  decide

private def squareFamily (ι : Type u) : ι → Z2 →ₜ* Z2 := fun _ ↦ square

private theorem bot_preserved (ι : Type u) :
    ∀ᶠ i in Filter.cofinite, MapsTo (squareFamily ι i) (bot ι i : Set Z2)
      (bot ι i : Set Z2) := by
  apply Filter.Eventually.of_forall
  intro i x hx
  have : x = 1 := by simpa [bot] using hx
  subst x
  simp [squareFamily, square, bot]

private theorem top_preserved (ι : Type u) :
    ∀ᶠ i in Filter.cofinite, MapsTo (squareFamily ι i) (top ι i : Set Z2)
      (top ι i : Set Z2) := by
  apply Filter.Eventually.of_forall
  intro i x hx
  simp [top]

private theorem bot_top_orthogonal (ι : Type u) :
    ∀ i (x : Z2), x ∈ bot ι i → ∀ y : Z2, y ∈ top ι i → bicharacter ι i x y = 1 := by
  intro i x hx y _hy
  have : x = 1 := by simpa [bot] using hx
  subst x
  simp [bicharacter]

/-- Squaring is pointwise adjoint under the nontrivial cyclic pairing. -/
private theorem square_adjoint (x y : Z2) :
    zmodBicharacter 2 x (square y) = zmodBicharacter 2 (square x) y := by
  rw [show square y = y ^ 2 by rfl, show square x = x ^ 2 by rfl]
  simp only [map_pow, MonoidHom.pow_apply]

/-- At index zero use identity, and elsewhere square to the trivial element. -/
private def exceptionalFamily (i : ℕ) : Z2 →ₜ* Z2 :=
  if i = 0 then ContinuousMonoidHom.id Z2 else square

private theorem exceptional_cofinite :
    ∀ᶠ i in Filter.cofinite,
      MapsTo (exceptionalFamily i) (↑(⊤ : Subgroup Z2) : Set Z2)
        (↑(⊥ : Subgroup Z2) : Set Z2) := by
  apply Filter.eventually_cofinite.mpr
  apply (Set.finite_singleton 0).subset
  intro i hi
  change i = 0
  by_contra hne
  apply hi
  intro x _
  have hsquare : square x = 1 := by fin_cases x <;> decide
  simpa [exceptionalFamily, hne] using
    (show square x ∈ (⊥ : Subgroup Z2) by simpa using hsquare)

private theorem exceptional_fails_at_zero :
    ¬ MapsTo (exceptionalFamily 0) (↑(⊤ : Subgroup Z2) : Set Z2)
      (↑(⊥ : Subgroup Z2) : Set Z2) := by
  intro h
  have hx := h (Subgroup.mem_top (Multiplicative.ofAdd 1 : Z2))
  simp [exceptionalFamily] at hx

/-- The map exists despite its failure to preserve the subgroup at one index. -/
private noncomputable def exceptionalRestrictedMap :
    (Πʳ _i : ℕ, [Z2, (⊤ : Subgroup Z2)]) →ₜ*
      (Πʳ _i : ℕ, [Z2, (⊥ : Subgroup Z2)]) :=
  mapContinuousMonoidHom (top ℕ) (bot ℕ) exceptionalFamily (by
    simpa only [top, bot] using exceptional_cofinite)

end Cyclic
end RestrictedProductTest

namespace RestrictedProductTest.SingleCoordinate

open Filter RestrictedProduct

private def coordinateBase : ℕ → Circle := fun _ ↦ 1

private def singleStageMap (z : Circle) : ∀ _ : ({0} : Finset ℕ), Circle := fun _ ↦ z

private def singleCoordinateMap (z : Circle) :
    RestrictedProduct (fun _ : ℕ ↦ Circle)
      (fun n ↦ ({coordinateBase n} : Set Circle)) cofinite :=
  singletonFinsetInsert coordinateBase {0} (singleStageMap z)

private theorem coordinateProductT1 :
    T1Space (RestrictedProduct (fun _ : ℕ ↦ Circle)
      (fun n ↦ ({coordinateBase n} : Set Circle)) cofinite) := inferInstance

private theorem singleStageCompact : CompactSpace (∀ _ : ({0} : Finset ℕ), Circle) :=
  inferInstance

private theorem singleton_one_not_isOpen : ¬ IsOpen ({(1 : Circle)} : Set Circle) := by
  intro h
  have hc : IsClopen (Circle.exp ⁻¹' ({1} : Set Circle)) :=
    ⟨isClosed_singleton.preimage Circle.exp.continuous, h.preimage Circle.exp.continuous⟩
  have hu : Circle.exp ⁻¹' ({1} : Set Circle) = Set.univ :=
    hc.eq_univ ⟨0, by simp⟩
  apply Circle.exp_pi_ne_one
  have hm : Real.pi ∈ Circle.exp ⁻¹' ({1} : Set Circle) := by
    rw [hu]
    exact Set.mem_univ _
  exact Set.mem_singleton_iff.mp hm

private theorem continuous_singleCoordinateMap : Continuous singleCoordinateMap := by
  exact (continuous_singletonFinsetInsert coordinateBase {0}).comp
    (continuous_pi fun _ ↦ continuous_id)

private theorem isCompact_range_singleCoordinateMap :
    IsCompact (Set.range singleCoordinateMap) := by
  let := singleStageCompact
  have hsurj : Function.Surjective singleStageMap := by
    intro y
    refine ⟨y ⟨0, by simp⟩, ?_⟩
    funext i
    apply congrArg y
    exact Subtype.ext (Finset.mem_singleton.mp i.2).symm
  have hrange : Set.range singleCoordinateMap =
      Set.range (singletonFinsetInsert coordinateBase {0}) := by
    change Set.range (singletonFinsetInsert coordinateBase {0} ∘ singleStageMap) = _
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
  rw [hrange]
  exact isCompact_range (continuous_singletonFinsetInsert coordinateBase {0})

private theorem singleCoordinateMap_zero (z : Circle) : singleCoordinateMap z 0 = z := by
  simp [singleCoordinateMap, singleStageMap]

private theorem singleCoordinateMap_of_ne_zero (z : Circle) (n : ℕ) (hn : n ≠ 0) :
    singleCoordinateMap z n = 1 := by
  exact singletonFinsetInsert_apply_of_notMem coordinateBase {0} (singleStageMap z) n
    (by simpa only [Finset.mem_singleton] using hn)

/-- The canonical circle gives a nonconstant compact range with nonopen singleton basepoints. -/
private theorem singleCoordinateUse :
    ¬ IsOpen ({(1 : Circle)} : Set Circle) ∧
      Continuous singleCoordinateMap ∧
      IsCompact (Set.range singleCoordinateMap) ∧
      (∀ z, singleCoordinateMap z 0 = z) ∧
      (∀ z n, n ≠ 0 → singleCoordinateMap z n = 1) ∧
      singleCoordinateMap (-1) ≠ singleCoordinateMap 1 ∧
      Set.range singleCoordinateMap ⊆
        cofiniteStage (R := fun _ : ℕ ↦ Circle)
          (A := fun n ↦ ({coordinateBase n} : Set Circle)) {0} ∧
      ¬ Set.range singleCoordinateMap ⊆
        cofiniteStage (R := fun _ : ℕ ↦ Circle)
          (A := fun n ↦ ({coordinateBase n} : Set Circle)) ∅ := by
  refine ⟨singleton_one_not_isOpen, continuous_singleCoordinateMap,
    isCompact_range_singleCoordinateMap, singleCoordinateMap_zero,
    singleCoordinateMap_of_ne_zero, ?_, ?_, ?_⟩
  · intro h
    apply Circle.neg_ne_self 1
    simpa only [singleCoordinateMap_zero] using congrArg (fun x ↦ x 0) h
  · rw [← range_singletonFinsetInsert coordinateBase {0}]
    rintro _ ⟨z, rfl⟩
    exact ⟨singleStageMap z, rfl⟩
  · intro h
    have hx := h ⟨(-1 : Circle), rfl⟩ 0 (by simp)
    have hzero : singleCoordinateMap (-1) 0 = 1 := Set.mem_singleton_iff.mp hx
    exact Circle.neg_ne_self 1 ((singleCoordinateMap_zero (-1)).symm.trans hzero)

/-- T1 compact containment applies to the compact single-coordinate circle itself. -/
private theorem singleCoordinate_compact_containment :
    ∃ s : Finset ℕ, Set.range singleCoordinateMap ⊆
      cofiniteStage (R := fun _ : ℕ ↦ Circle)
        (A := fun n ↦ ({coordinateBase n} : Set Circle)) s := by
  let := coordinateProductT1
  exact exists_subset_cofiniteStage_of_t1 singleCoordinateUse.2.2.1

/-- The compact circle map factors by exactly the ordinary finite coordinate restriction. -/
private theorem singleCoordinate_factorization :
    ∃ s : Finset ℕ, ∃ g : C(Circle, ∀ _ : s, Circle),
      (∀ z, g z = s.restrict (fun n ↦ singleCoordinateMap z n)) ∧
      ∀ z, singletonFinsetInsert coordinateBase s (g z) = singleCoordinateMap z := by
  let := coordinateProductT1
  exact exists_singletonFinsetInsert_factorization coordinateBase singleCoordinateUse.2.1

end RestrictedProductTest.SingleCoordinate
