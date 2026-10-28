module

public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Solvability of GL₂(3)

SL₂(3) is the binary tetrahedral group Q₈ ⋊ C₃, hence solvable. The determinant
map expresses GL₂(3) as an extension of the abelian group of field units by
SL₂(3). This makes the inner PSL₃(3) involution centralizers in
Aschbacher–Smith 16.1.5(1), printed p.1171, solvable, as used in 16.1.7.

The proof extracts the determinant argument already used locally in
`Theory.SpecificGroups.PSL3Three.ParabolicSolvability` without importing its
parabolic calculations.
-/

namespace Matrix.GeneralLinearGroup

/-- The general linear group of degree two over the three-element field is solvable. -/
public theorem three_isSolvable : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := by
  let hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
  let : Group.IsNilpotent (QuaternionGroup 2) := hQ.isNilpotent
  let : Group.IsSolvable
      (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3)) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
    Group.isSolvable_of_surjective
      (f := GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toMonoidHom)
      GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.surjective
  let det := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod 3)
  apply Group.isSolvable_of_ker_le_range (SpecialLinearGroup.toGL (R := ZMod 3)) det
  intro g hg
  let y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod 3)), congr_arg Units.val hg⟩
  exact ⟨y, Units.ext rfl⟩

end Matrix.GeneralLinearGroup
