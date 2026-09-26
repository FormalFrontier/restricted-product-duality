/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.SymmetricDuality

/-!
# Naturality of restricted-product duality

This file bundles coordinatewise continuous homomorphisms as maps of cofinite
restricted products and proves the contravariant naturality square for the
canonical map into the Pontryagin dual.  The theorem is stated before local
perfectness: it is a property of the pairing itself, and hence also applies to
the accepted equivalence when the stronger hypotheses are available.
-/

public section

set_option warningAsError true

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X X' Y Y' : ι → Type*}
variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (X' i)]
variable [∀ i, CommGroup (Y i)] [∀ i, CommGroup (Y' i)]
variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (X' i)]
variable [∀ i, TopologicalSpace (Y i)] [∀ i, TopologicalSpace (Y' i)]

/-- A coordinatewise continuous homomorphism preserving the distinguished
subgroups at cofinitely many indices induces a continuous homomorphism of
cofinite restricted products. -/
@[expose] def mapContinuousMonoidHom
    (U : ∀ i, Subgroup (X i)) (U' : ∀ i, Subgroup (X' i))
    (f : ∀ i, X i →ₜ* X' i)
    (hf : ∀ᶠ i in cofinite, MapsTo (f i) (U i : Set (X i)) (U' i : Set (X' i))) :
    (Πʳ i, [X i, U i]) →ₜ* (Πʳ i, [X' i, U' i]) :=
  ContinuousMonoidHom.mk
    (mapAlongMonoidHom X X' id tendsto_id (fun i ↦ (f i).toMonoidHom)
      hf)
    (mapAlong_continuous X X' id tendsto_id (fun i ↦ f i)
      hf fun i ↦ (f i).continuous)

@[simp]
theorem mapContinuousMonoidHom_apply
    (U : ∀ i, Subgroup (X i)) (U' : ∀ i, Subgroup (X' i))
    (f : ∀ i, X i →ₜ* X' i)
    (hf : ∀ᶠ i in cofinite, MapsTo (f i) (U i : Set (X i)) (U' i : Set (X' i)))
    (x : Πʳ i, [X i, U i]) (i : ι) :
    mapContinuousMonoidHom U U' f hf x i = f i (x i) :=
  rfl

/-- Coordinatewise adjoint maps carry the global restricted-product pairing
to the global pairing. -/
theorem pairing_mapContinuousMonoidHom
    (U : ∀ i, Subgroup (X i)) (U' : ∀ i, Subgroup (X' i))
    (V : ∀ i, Subgroup (Y i)) (V' : ∀ i, Subgroup (Y' i))
    (e : ∀ i, X i →* Y i →* Circle) (e' : ∀ i, X' i →* Y' i →* Circle)
    (f : ∀ i, X' i →ₜ* X i) (g : ∀ i, Y i →ₜ* Y' i)
    (hf : ∀ᶠ i in cofinite, MapsTo (f i) (U' i : Set (X' i)) (U i : Set (X i)))
    (hg : ∀ᶠ i in cofinite, MapsTo (g i) (V i : Set (Y i)) (V' i : Set (Y' i)))
    (hadj : ∀ i (x : X' i) (y : Y i), e' i x (g i y) = e i (f i x) y)
    (x : Πʳ i, [X' i, U' i]) (y : Πʳ i, [Y i, V i]) :
    pairing U' V' e' x (mapContinuousMonoidHom V V' g hg y) =
      pairing U V e (mapContinuousMonoidHom U' U f hf x) y := by
  apply finprod_congr
  intro i
  exact hadj i (x i) (y i)

/-- The canonical restricted-product pairing map is natural: covariant maps on
the representing coordinates correspond to contravariant Pontryagin-dual maps
on the character-domain coordinates. -/
theorem toPontryaginDual_natural
    (U : ∀ i, Subgroup (X i)) (U' : ∀ i, Subgroup (X' i))
    (V : ∀ i, Subgroup (Y i)) (V' : ∀ i, Subgroup (Y' i))
    (e : ∀ i, X i →* Y i →* Circle) (e' : ∀ i, X' i →* Y' i →* Circle)
    (f : ∀ i, X' i →ₜ* X i) (g : ∀ i, Y i →ₜ* Y' i)
    (hf : ∀ᶠ i in cofinite, MapsTo (f i) (U' i : Set (X' i)) (U i : Set (X i)))
    (hg : ∀ᶠ i in cofinite, MapsTo (g i) (V i : Set (Y i)) (V' i : Set (Y' i)))
    (hadj : ∀ i (x : X' i) (y : Y i), e' i x (g i y) = e i (f i x) y)
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (horth' : ∀ i (x : X' i), x ∈ U' i → ∀ y : Y' i, y ∈ V' i → e' i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i)))
    (hUopen' : ∀ i, IsOpen (U' i : Set (X' i)))
    (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (hVopen' : ∀ i, IsOpen (V' i : Set (Y' i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (he' : ∀ i, Continuous fun p : X' i × Y' i ↦ e' i p.1 p.2) :
    (toPontryaginDual U' V' e' horth' hUopen' hVopen' he').comp
        (mapContinuousMonoidHom V V' g hg) =
      (PontryaginDual.map (mapContinuousMonoidHom U' U f hf)).comp
        (toPontryaginDual U V e horth hUopen hVopen he) := by
  apply ContinuousMonoidHom.ext
  intro y
  apply PontryaginDual.ext
  intro x
  exact pairing_mapContinuousMonoidHom U U' V V' e e' f g hf hg hadj x y

/-- Pointwise naturality of the restricted-product duality equivalence. -/
theorem pontryaginDualEquiv_natural_apply
    [∀ i, Finite (X i)] [∀ i, Finite (X' i)]
    [∀ i, DiscreteTopology (X i)] [∀ i, DiscreteTopology (X' i)]
    [∀ i, IsTopologicalGroup (Y i)] [∀ i, IsTopologicalGroup (Y' i)]
    (U : ∀ i, Subgroup (X i)) (U' : ∀ i, Subgroup (X' i))
    (V : ∀ i, Subgroup (Y i)) (V' : ∀ i, Subgroup (Y' i))
    (e : ∀ i, X i →* Y i →* Circle) (e' : ∀ i, X' i →* Y' i →* Circle)
    (f : ∀ i, X' i →ₜ* X i) (g : ∀ i, Y i →ₜ* Y' i)
    (hf : ∀ᶠ i in cofinite, MapsTo (f i) (U' i : Set (X' i)) (U i : Set (X i)))
    (hg : ∀ᶠ i in cofinite, MapsTo (g i) (V i : Set (Y i)) (V' i : Set (Y' i)))
    (hadj : ∀ i (x : X' i) (y : Y i), e' i x (g i y) = e i (f i x) y)
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (horth' : ∀ i (x : X' i), x ∈ U' i → ∀ y : Y' i, y ∈ V' i → e' i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i)))
    (hUopen' : ∀ i, IsOpen (U' i : Set (X' i)))
    (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (hVopen' : ∀ i, IsOpen (V' i : Set (Y' i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (he' : ∀ i, Continuous fun p : X' i × Y' i ↦ e' i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hperfect' : ∀ i, Function.Bijective (rightCharacter (e' i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i))
    (hV' : ∀ i, V' i = rightAnnihilator (U' i) (e' i))
    (y : Πʳ i, [Y i, V i]) :
    pontryaginDualEquiv U' V' e' horth' hUopen' hVopen' he' hperfect' hV'
        (mapContinuousMonoidHom V V' g hg y) =
      PontryaginDual.map (mapContinuousMonoidHom U' U f hf)
        (pontryaginDualEquiv U V e horth hUopen hVopen he hperfect hV y) := by
  rw [pontryaginDualEquiv_apply, pontryaginDualEquiv_apply]
  exact congrArg (fun F ↦ F y)
    (toPontryaginDual_natural U U' V V' e e' f g hf hg hadj horth horth'
      hUopen hUopen' hVopen hVopen' he he')

end RestrictedProduct
