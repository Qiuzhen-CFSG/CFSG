module

public import Theory.SpecificGroups.PSL3Three.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Index

/-!
# The order of SL₃(3) and PSL₃(3)

The determinant maps GL₃(3) onto the two units of the field, with kernel SL₃(3).
The general linear group cardinality formula therefore gives
`(27 - 1) * (27 - 3) * (27 - 9) / 2 = 5616`. The canonical quotient equivalence
from `PSL3Three.Basic` transfers this order to PSL₃(3).

This supplies the matrix group order for the projective-plane recognition in
Wong, Theorem 6(b), printed p. 111, DOI 10.1017/S1446788700022771.
-/

namespace Matrix.PSL3Three

private def slEquivDetKer :
    SL ≃ (GeneralLinearGroup.det : GL (Fin 3) (ZMod 3) →* (ZMod 3)ˣ).ker where
  toFun A := ⟨SpecialLinearGroup.toGL A, SpecialLinearGroup.coeToGL_det A⟩
  invFun A := ⟨A.1.val, congrArg Units.val A.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)

/-- There are 5616 determinant-one matrices of degree three over the three-element field. -/
public theorem card_SL : Nat.card SL = 5616 := by
  have h := (GeneralLinearGroup.det : GL (Fin 3) (ZMod 3) →* (ZMod 3)ˣ).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr GeneralLinearGroup.det_surjective,
    Subgroup.card_top, ← Nat.card_congr slEquivDetKer, card_GL_field] at h
  have hu : Nat.card (ZMod 3)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hu] at h
  norm_num [Fin.prod_univ_succ] at h
  rw [Nat.card_eq_fintype_card]
  omega

/-- The projective special linear group PSL₃(3) has order 5616. -/
public theorem card_PSL : Nat.card PSL = 5616 := by
  rw [← Nat.card_congr equiv.toEquiv, card_SL]

end Matrix.PSL3Three
