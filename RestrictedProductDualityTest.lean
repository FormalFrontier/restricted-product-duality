/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Public-import clients for restricted-product duality

These private audit handles compile using only the public umbrella import. In
particular, the cyclic examples have nontrivial coordinate groups and infinite
index type; the exceptional map deliberately fails subgroup preservation at zero.
-/

-- The examples in this module are intentionally private.
set_option linter.privateModule false

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

namespace RestrictedProductTest.SingleCoordinate

open Filter RestrictedProduct

/-- The chosen subtype point, with everywhere-singleton membership. -/
private def coordinateBasepoint :
    RestrictedProduct (fun _ : ℕ ↦ Circle)
      (fun n ↦ ({coordinateBase n} : Set Circle)) cofinite :=
  ⟨coordinateBase,
    Filter.Eventually.of_forall (fun n ↦ Set.mem_singleton (coordinateBase n))⟩

/-- The chosen coordinate point is the canonical singleton basepoint. -/
private theorem coordinateBasepoint_eq_singletonBasepoint :
    coordinateBasepoint = singletonBasepoint coordinateBase :=
  rfl

private theorem singleCoordinateMap_one :
    singleCoordinateMap 1 = coordinateBasepoint := by
  apply RestrictedProduct.ext
  intro n
  by_cases hn : n = 0
  · subst n
    exact singleCoordinateMap_zero 1
  · exact singleCoordinateMap_of_ne_zero 1 n hn

private def circleAngle : C((Fin 1 → unitInterval), ℝ) where
  toFun t := (2 * Real.pi) * (t 0 : ℝ)
  continuous_toFun :=
    continuous_const.mul (continuous_subtype_val.comp (continuous_apply 0))

private def circleLoopMap : C((Fin 1 → unitInterval), Circle) :=
  Circle.exp.comp circleAngle

/-- The once-around Circle loop indexed by `Fin 1`. -/
private def circleOnceAround : GenLoop (Fin 1) Circle 1 :=
  ⟨circleLoopMap, by
    intro t ht
    rcases ht with ⟨i, hi⟩
    have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rcases hi with hi | hi
    · change Circle.exp ((2 * Real.pi) * (t 0 : ℝ)) = 1
      rw [hi]
      change Circle.exp ((2 * Real.pi) * (0 : ℝ)) = 1
      simpa only [mul_zero] using Circle.exp_zero
    · change Circle.exp ((2 * Real.pi) * (t 0 : ℝ)) = 1
      rw [hi]
      change Circle.exp ((2 * Real.pi) * (1 : ℝ)) = 1
      simpa only [mul_one] using Circle.exp_two_pi⟩

/-- Insert the once-around Circle loop in coordinate zero. -/
private def singleCoordinateOnceAround :
    GenLoop (Fin 1)
      (RestrictedProduct (fun _ : ℕ ↦ Circle)
        (fun n ↦ ({coordinateBase n} : Set Circle)) cofinite)
      coordinateBasepoint :=
  ⟨(⟨singleCoordinateMap, continuous_singleCoordinateMap⟩ :
      C(Circle, RestrictedProduct (fun _ : ℕ ↦ Circle)
        (fun n ↦ ({coordinateBase n} : Set Circle)) cofinite)).comp circleLoopMap,
    by
      intro t ht
      change singleCoordinateMap (circleLoopMap t) = coordinateBasepoint
      have hcircle : circleLoopMap t = 1 := GenLoop.boundary circleOnceAround t ht
      exact (congrArg singleCoordinateMap hcircle).trans singleCoordinateMap_one⟩

private def circleOnceAroundClass : HomotopyGroup (Fin 1) Circle 1 :=
  ⟦circleOnceAround⟧

private def singleCoordinateOnceAroundClass :
    HomotopyGroup (Fin 1)
      (RestrictedProduct (fun _ : ℕ ↦ Circle)
        (fun n ↦ ({coordinateBase n} : Set Circle)) cofinite)
      coordinateBasepoint :=
  ⟦singleCoordinateOnceAround⟧

/-- The class family supported in coordinate zero at the bottom subgroups. -/
private def onceAroundClassTuple :
    Πʳ _n : ℕ, [HomotopyGroup (Fin 1) Circle 1,
      (⊥ : Subgroup (HomotopyGroup (Fin 1) Circle 1))] :=
  RestrictedProduct.mulSingle
    (fun _ : ℕ ↦ (⊥ : Subgroup (HomotopyGroup (Fin 1) Circle 1)))
    0 circleOnceAroundClass

/-- Explicit cofinite membership with exceptional set contained in {0}. -/
private theorem onceAroundClassTuple_bottom_membership :
    ∀ᶠ n : ℕ in cofinite,
      onceAroundClassTuple n ∈
        (⊥ : Subgroup (HomotopyGroup (Fin 1) Circle 1)) := by
  filter_upwards [({0} : Finset ℕ).eventually_cofinite_notMem] with n hn
  apply Subgroup.mem_bot.mpr
  exact RestrictedProduct.mulSingle_eq_of_ne
    (fun _ : ℕ ↦ (⊥ : Subgroup (HomotopyGroup (Fin 1) Circle 1)))
    circleOnceAroundClass (by simpa only [Finset.mem_singleton] using hn)

private theorem singleCoordinateOnceAround_coordinate_zero :
    singletonCoordinateGenLoop (Fin 1) coordinateBase singleCoordinateOnceAround 0 =
      circleOnceAround := by
  apply GenLoop.ext
  intro t
  exact Eq.trans (α := Circle)
    (singletonCoordinateGenLoop_apply (Fin 1) coordinateBase singleCoordinateOnceAround 0 t)
    (singleCoordinateMap_zero (circleLoopMap t))

private theorem singleCoordinateOnceAround_coordinate_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    singletonCoordinateGenLoop (Fin 1) coordinateBase singleCoordinateOnceAround n =
      (GenLoop.const : GenLoop (Fin 1) Circle (coordinateBase n)) := by
  apply GenLoop.ext
  intro t
  exact Eq.trans (α := Circle)
    (singletonCoordinateGenLoop_apply (Fin 1) coordinateBase singleCoordinateOnceAround n t)
    (singleCoordinateMap_of_ne_zero (circleLoopMap t) n hn)

/-- The single-coordinate loop maps to the tuple of its Circle quotient class.
No nonidentity-class assertion is made. -/
private theorem homotopyGroupSingletonMulEquiv_onceAround :
    homotopyGroupSingletonMulEquiv (Fin 1) coordinateBase
        (⟦singleCoordinateOnceAround⟧ : HomotopyGroup (Fin 1)
          (RestrictedProduct (fun _ : ℕ ↦ Circle)
            (fun n ↦ ({coordinateBase n} : Set Circle)) cofinite)
          coordinateBasepoint) =
      RestrictedProduct.mulSingle
        (fun _ : ℕ ↦ (⊥ : Subgroup (HomotopyGroup (Fin 1) Circle 1)))
        0 (⟦circleOnceAround⟧ : HomotopyGroup (Fin 1) Circle 1) := by
  let := coordinateProductT1
  apply RestrictedProduct.ext
  intro n
  refine Eq.trans (α := HomotopyGroup (Fin 1) Circle (coordinateBase n))
    (homotopyGroupSingletonMulEquiv_apply (Fin 1) coordinateBase
      singleCoordinateOnceAround n) ?_
  by_cases hn : n = 0
  · subst n
    exact Eq.trans (α := HomotopyGroup (Fin 1) Circle (coordinateBase 0))
      (congrArg (fun p : GenLoop (Fin 1) Circle (coordinateBase 0) ↦
        (⟦p⟧ : HomotopyGroup (Fin 1) Circle (coordinateBase 0)))
        singleCoordinateOnceAround_coordinate_zero)
      (RestrictedProduct.mulSingle_eq_same
        (fun _ : ℕ ↦ (⊥ : Subgroup (HomotopyGroup (Fin 1) Circle 1)))
        0 circleOnceAroundClass).symm
  · exact Eq.trans (α := HomotopyGroup (Fin 1) Circle (coordinateBase n))
      (congrArg (fun p : GenLoop (Fin 1) Circle (coordinateBase n) ↦
        (⟦p⟧ : HomotopyGroup (Fin 1) Circle (coordinateBase n)))
        (singleCoordinateOnceAround_coordinate_of_ne_zero n hn))
      (Eq.trans (α := HomotopyGroup (Fin 1) Circle (coordinateBase n))
        (HomotopyGroup.one_def
          (N := Fin 1) (X := Circle) (x := coordinateBase n)).symm
        (RestrictedProduct.mulSingle_eq_of_ne
          (G := fun _ : ℕ ↦ HomotopyGroup (Fin 1) Circle 1)
          (fun _ : ℕ ↦ (⊥ : Subgroup (HomotopyGroup (Fin 1) Circle 1)))
          (i := 0) (j := n)
          (⟦circleOnceAround⟧ : HomotopyGroup (Fin 1) Circle 1) hn).symm)

end RestrictedProductTest.SingleCoordinate

namespace RestrictedProductTest.PathComponents

open RestrictedProduct.SingletonPathComponents

-- Witnesses of Mathlib's discrete Bool topology; no topology instance is introduced.
@[instance_reducible]
private def topologyWitness : TopologicalSpace Bool := inferInstance

private theorem discreteWitness : DiscreteTopology Bool := inferInstance

/-- The distinguished family for the countably infinite discrete-Bool example. -/
private def base : ℕ → Bool := fun _ ↦ false

/-- The single-coordinate point of the infinite-index restricted product, via finite insertion. -/
private def zeroTrue : PointProduct base :=
  RestrictedProduct.singletonFinsetInsert base ({0} : Finset ℕ) (fun _ ↦ true)

/-- The all-false point, using the stock structure map; no pointed-space API is needed. -/
private def allFalse : PointProduct base :=
  RestrictedProduct.structureMap (fun _ : ℕ ↦ Bool)
    (fun _ ↦ ({false} : Set Bool)) Filter.cofinite
    (fun _ ↦ ⟨false, Set.mem_singleton false⟩)

/-- The path class of the single-coordinate point. -/
private def zeroTrueClass : ZerothHomotopy (PointProduct base) := ZerothHomotopy.mk zeroTrue

private def allFalseClass : ZerothHomotopy (PointProduct base) := ZerothHomotopy.mk allFalse

/-- The target class family, true at zero and false elsewhere, with cofinite membership. -/
private def zeroTrueTuple : ComponentProduct base :=
  RestrictedProduct.mk
    (fun n : ℕ ↦ if n = 0 then ZerothHomotopy.mk true else ZerothHomotopy.mk false)
    ((({0} : Finset ℕ).eventually_cofinite_notMem).mono fun n hn ↦
      Set.mem_singleton_iff.mpr
        (ite_eq_right (fun hn0 : n = 0 ↦ hn (Finset.mem_singleton.mpr hn0))))

/-- The default target class family, via the structure map. -/
private def defaultTuple : ComponentProduct base :=
  RestrictedProduct.structureMap (fun _ : ℕ ↦ ZerothHomotopy Bool)
    (fun _ ↦ ({ZerothHomotopy.mk false} : Set (ZerothHomotopy Bool))) Filter.cofinite
    (fun _ ↦ ⟨ZerothHomotopy.mk false, Set.mem_singleton _⟩)

/-- A Bool-valued path is constant, so the two coordinate path classes differ. -/
private theorem path_classes_distinct :
    (ZerothHomotopy.mk true : ZerothHomotopy Bool) ≠ ZerothHomotopy.mk false := by
  intro h
  obtain ⟨p⟩ : Joined true false := Quotient.exact h
  have hp : p 0 = p 1 :=
    IsPreconnected.constant isPreconnected_univ p.continuous.continuousOn
      (Set.mem_univ _) (Set.mem_univ _)
  have htf : true = false := by simpa only [Path.source, Path.target] using hp
  exact Bool.noConfusion htf

/-- The comparison sends the single-coordinate point to its full prescribed tuple. -/
private theorem canonical_full_tuple : canonicalEquiv base zeroTrueClass = zeroTrueTuple := by
  apply RestrictedProduct.ext
  intro n
  rw [zeroTrueClass, representative_coordinate_apply]
  by_cases hn : n = 0
  · subst n
    simp [zeroTrue, zeroTrueTuple]
  · change ZerothHomotopy.mk (zeroTrue n) =
      (if n = 0 then ZerothHomotopy.mk true else ZerothHomotopy.mk false)
    rw [ite_eq_right hn]
    simp [zeroTrue, hn, base]

end RestrictedProductTest.PathComponents
