module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.NormNum

/-!
# The order of SL₃(2)

There are 168 determinant-one binary matrices of degree three. Identify SL₃(2)
with the determinant kernel in GL₃(2), whose index is one because the unit group
of ZMod 2 is trivial, and apply the ordered-basis count `Matrix.card_GL_field`.

This common cardinality calculation supports the linear models in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), I.5.3–4, pp. 419–420, and the group-order obstruction in §10.3,
p. 757. The determinant-kernel proof is extracted from
`Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction`.
-/

namespace Matrix.PSL3Two

private abbrev SL := SpecialLinearGroup (Fin 3) (ZMod 2)

private def slEquivDetKer :
    SL ≃ (GeneralLinearGroup.det : GL (Fin 3) (ZMod 2) →* (ZMod 2)ˣ).ker where
  toFun A := ⟨SpecialLinearGroup.toGL A, SpecialLinearGroup.coeToGL_det A⟩
  invFun A := ⟨A.1.val, congrArg Units.val A.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)

/-- There are 168 determinant-one binary matrices of degree three. -/
public theorem card_SL : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  have h := (GeneralLinearGroup.det : GL (Fin 3) (ZMod 2) →* (ZMod 2)ˣ).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr GeneralLinearGroup.det_surjective,
    Subgroup.card_top, ← Nat.card_congr slEquivDetKer, card_GL_field] at h
  have hu : Nat.card (ZMod 2)ˣ = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hu] at h
  norm_num [Fin.prod_univ_succ] at h
  rw [Nat.card_eq_fintype_card]
  exact h

end Matrix.PSL3Two
