module

public import Theory.SpecificGroups.GL2.ThreeCharacteristicTwo
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Characteristic two of SL₂(3)

The actual special linear group is isomorphic to the determinant kernel in
GL₂(3). Characteristic two passes to normal subgroups, so the established
GL₂(3) calculation gives the intrinsic two-core centralizer bound in SL₂(3).
This is the small special-unitary centralizer input for Aschbacher–Smith,
Theorem 0.1.2(4), printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

open Subgroup Matrix
namespace Matrix.SpecialLinearGroup
/-- The intrinsic two-core of the special linear group SL₂(3) is self-centralizing. -/
public theorem three_twoCore_self_centralizing :
    centralizer (pCore 2 (SpecialLinearGroup (Fin 2) (ZMod 3)) :
      Set (SpecialLinearGroup (Fin 2) (ZMod 3))) ≤
        pCore 2 (SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  let D := (GeneralLinearGroup.det : GL (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker
  let e : SpecialLinearGroup (Fin 2) (ZMod 3) ≃* D := {
    toFun A := ⟨toGL A, coeToGL_det A⟩
    invFun A := ⟨A.val.val, congrArg Units.val A.property⟩
    left_inv A := rfl
    right_inv A := Subtype.ext (Units.ext rfl)
    map_mul' A B := Subtype.ext (toGL.map_mul A B) }
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
    (normal_core_selfCentralizing GeneralLinearGroup.three_centralizer_twoCore_le D)
end Matrix.SpecialLinearGroup
