/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality.HomotopyMaps
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# A two-point dimension-zero map

On Bool with its usual discrete topology, negation sends the class of false to the
class of true and the class of true to the class of false. These are distinct
classes in the generalized-loop quotient indexed by `Fin 0`, as well as distinct
path components. The chosen points are false in the source and true in the target.
The comparison with path components uses Mathlib's empty-cube equivalence and the
existing path-component map.
-/

@[expose] public section

-- The examples in this module are intentionally private.

set_option warningAsError true

noncomputable section

namespace RestrictedProductTest.HomotopyMaps

/-- Negation between the two stock discrete Bool spaces. -/
private def boolNotMap : C(Bool, Bool) :=
  ContinuousMap.equivFnOfDiscrete.symm Bool.not

private theorem boolNot_based : boolNotMap false = true := rfl

/-- The chosen source class. -/
private def sourceFalse : HomotopyGroup (Fin 0) Bool false :=
  ⟦GenLoop.const⟧

/-- The other source class, using the stock empty-cube representative. -/
private def sourceTrue : HomotopyGroup (Fin 0) Bool false :=
  ⟦(genLoopHomeoOfIsEmpty (Fin 0) false).symm true⟧

/-- The other target class, using the stock empty-cube representative. -/
private def targetFalse : HomotopyGroup (Fin 0) Bool true :=
  ⟦(genLoopHomeoOfIsEmpty (Fin 0) true).symm false⟧

/-- The chosen target class. -/
private def targetTrue : HomotopyGroup (Fin 0) Bool true :=
  ⟦GenLoop.const⟧

/-- Negation exchanges two distinct quotient classes and its dimension-zero action
agrees with the existing path-component map on the non-basepoint source class. -/
private theorem bool_not_dimension_zero :
    HomotopyGroup.mapFun (Fin 0) boolNotMap boolNot_based sourceFalse = targetTrue ∧
    HomotopyGroup.mapFun (Fin 0) boolNotMap boolNot_based sourceTrue = targetFalse ∧
    sourceFalse ≠ sourceTrue ∧ targetFalse ≠ targetTrue ∧
    (ZerothHomotopy.mk false : ZerothHomotopy Bool) ≠ ZerothHomotopy.mk true ∧
    HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false) sourceFalse =
      ZerothHomotopy.mk false ∧
    HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false) sourceTrue =
      ZerothHomotopy.mk true ∧
    HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := true) targetFalse =
      ZerothHomotopy.mk false ∧
    HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := true) targetTrue =
      ZerothHomotopy.mk true ∧
    HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := true)
        (HomotopyGroup.mapFun (Fin 0) boolNotMap boolNot_based sourceTrue) =
      RestrictedProduct.SingletonNaturality.pathMap boolNotMap
        (HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false) sourceTrue) := by
  have hpath : (ZerothHomotopy.mk false : ZerothHomotopy Bool) ≠
      ZerothHomotopy.mk true := by
    intro h
    obtain ⟨p⟩ : Joined (false : Bool) true := Quotient.exact h
    have hp : p 0 = p 1 :=
      isPreconnected_univ.constant p.continuous.continuousOn
        (Set.mem_univ _) (Set.mem_univ _)
    have hfalseTrue : (false : Bool) = true :=
      p.source.symm.trans (hp.trans p.target)
    cases hfalseTrue
  have hsourceFalse :
      HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false) sourceFalse =
        ZerothHomotopy.mk false := rfl
  have hsourceTrue :
      HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false) sourceTrue =
        ZerothHomotopy.mk true := rfl
  have htargetFalse :
      HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := true) targetFalse =
        ZerothHomotopy.mk false := rfl
  have htargetTrue :
      HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := true) targetTrue =
        ZerothHomotopy.mk true := rfl
  have hmapTrue :
      HomotopyGroup.mapFun (Fin 0) boolNotMap boolNot_based sourceTrue = targetFalse := by
    change (⟦GenLoop.map boolNotMap boolNot_based
      ((genLoopHomeoOfIsEmpty (Fin 0) false).symm true)⟧ :
        HomotopyGroup (Fin 0) Bool true) =
      ⟦(genLoopHomeoOfIsEmpty (Fin 0) true).symm false⟧
    apply congrArg (fun p : GenLoop (Fin 0) Bool true ↦
      (⟦p⟧ : HomotopyGroup (Fin 0) Bool true))
    apply GenLoop.ext
    intro t
    rfl
  refine ⟨HomotopyGroup.mapFun_const (Fin 0) boolNotMap boolNot_based,
    hmapTrue, ?_, ?_, hpath, hsourceFalse, hsourceTrue, htargetFalse, htargetTrue, ?_⟩
  · intro h
    apply hpath
    simpa only [hsourceFalse, hsourceTrue] using
      congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false)) h
  · intro h
    apply hpath
    simpa only [htargetFalse, htargetTrue] using
      congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := true)) h
  · rw [hmapTrue, htargetFalse, hsourceTrue,
      RestrictedProduct.SingletonNaturality.pathMap_mk]
    rfl

end RestrictedProductTest.HomotopyMaps
