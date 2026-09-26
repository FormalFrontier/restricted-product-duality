/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Pairing
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Continuous pairings of restricted products

The algebraic restricted-product pairing is jointly continuous when the distinguished subgroups
are open and the local bicharacters are jointly continuous.
-/

public section

set_option warningAsError true

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}
variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]
variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))
variable (e : ∀ i, X i →* Y i →* Circle)

/-- The pairing induced by jointly continuous local bicharacters is jointly continuous on the two
cofinite restricted products. -/
theorem continuous_pairing
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2) :
    Continuous fun p : (Πʳ i, [X i, U i]) × (Πʳ i, [Y i, V i]) ↦
      pairing U V e p.1 p.2 := by
  rw [continuous_dom_prod (R := X) (A := fun i ↦ (U i : Set (X i))) hUopen hVopen]
  intro S hS
  have hSc : Sᶜ.Finite := Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
  let s := hSc.toFinset
  have hpair :
      (fun p : (Πʳ i, [X i, U i]) × (Πʳ i, [Y i, V i]) ↦ pairing U V e p.1 p.2) ∘
          Prod.map (inclusion X (fun i ↦ (U i : Set (X i))) hS)
            (inclusion Y (fun i ↦ (V i : Set (Y i))) hS) =
        fun p ↦ ∏ i ∈ s, e i (p.1 i) (p.2 i) := by
    funext p
    apply pairing_eq_prod
    intro i hi
    have hiS : i ∈ S := by
      simpa only [s, hSc.mem_toFinset, mem_compl_iff, not_not] using hi
    exact horth i (p.1 i) (p.1.2 hiS) (p.2 i) (p.2.2 hiS)
  rw [hpair]
  apply continuous_finsetProd s
  intro i _
  exact (he i).comp
    (((continuous_eval i).comp continuous_fst).prodMk ((continuous_eval i).comp continuous_snd))

/-- The continuous character of the first restricted product determined by an element of the
second restricted product. -/
@[expose] noncomputable def pairingCharacter
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (y : Πʳ i, [Y i, V i]) : PontryaginDual (Πʳ i, [X i, U i]) :=
  ContinuousMonoidHom.mk (pairingMonoidHom U V e horth y) <|
    (continuous_pairing U V e horth hUopen hVopen he).comp (continuous_id.prodMk continuous_const)

@[simp]
theorem pairingCharacter_apply
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (y : Πʳ i, [Y i, V i]) (x : Πʳ i, [X i, U i]) :
    pairingCharacter U V e horth hUopen hVopen he y x = pairing U V e x y :=
  rfl

/-- The canonical continuous homomorphism from the second restricted product to the Pontryagin
dual of the first. This construction assumes orthogonality and continuity, but not perfectness or
exact-annihilator hypotheses. -/
@[expose] noncomputable def toPontryaginDual
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2) :
    (Πʳ i, [Y i, V i]) →ₜ* PontryaginDual (Πʳ i, [X i, U i]) := by
  refine ContinuousMonoidHom.mk
    { toFun := pairingCharacter U V e horth hUopen hVopen he
      map_one' := ContinuousMonoidHom.ext fun x ↦ pairing_one_right U V e x
      map_mul' := fun y y' ↦
        ContinuousMonoidHom.ext fun x ↦ pairing_mul_right U V e horth x y y' } ?_
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  exact (continuous_pairing U V e horth hUopen hVopen he).comp
    (continuous_snd.prodMk continuous_fst)

@[simp]
theorem toPontryaginDual_apply
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (y : Πʳ i, [Y i, V i]) (x : Πʳ i, [X i, U i]) :
    toPontryaginDual U V e horth hUopen hVopen he y x = pairing U V e x y :=
  rfl

open scoped Classical in
/-- Local separation in the second variable makes the canonical map to the Pontryagin dual
injective. -/
theorem toPontryaginDual_injective
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hsep : ∀ i (y y' : Y i), (∀ x : X i, e i x y = e i x y') → y = y') :
    Function.Injective (toPontryaginDual U V e horth hUopen hVopen he) := by
  intro y y' hyy'
  apply RestrictedProduct.ext
  intro i
  apply hsep i
  intro x
  have h := congrArg (fun f : PontryaginDual (Πʳ i, [X i, U i]) ↦ f (mulSingle U i x)) hyy'
  simpa using h

end RestrictedProduct
