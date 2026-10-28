module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Coordinates
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The standard Sylow two-subgroup of GL₅(2)

The actual full-flag stabilizer has exactly ten free upper entries, with all
other entries forced. Its order is therefore 1024. The standard finite-field
GL order formula gives ambient order 9999360 and index 9765, which is odd.
Together with the exponent-eight argument in `Coordinates`, this constructs
the required Sylow subgroup without a flag or conjugacy assumption.

Source: the binary linear case of the characteristic-two parabolic argument
in Aschbacher--Smith, A.3.12, printed p.48 (combined manuscript, 1 March 2004).
-/

@[expose] public section

namespace BinaryLinear.FiveFlagGeometry.SylowOvergroups
open OuterCyclic

private abbrev UpperPosition := {ij : Fin 5 × Fin 5 // ij.1 < ij.2}

private def upperMatrix (f : UpperPosition → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

private theorem upperMatrix_triangular (f : UpperPosition → ZMod 2) :
    (upperMatrix f).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp only [upperMatrix, if_neg (ne_of_gt hji), dif_neg (not_lt_of_ge hji.le)]

private theorem upperMatrix_det (f : UpperPosition → ZMod 2) :
    (upperMatrix f).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (upperMatrix_triangular f)]
  simp [upperMatrix]

private def upperSL (f : UpperPosition → ZMod 2) :
    Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨upperMatrix f, upperMatrix_det f⟩

private noncomputable def fromParameters (f : UpperPosition → ZMod 2) : standardBorel :=
  ⟨slEquivLinear 5 (upperSL f), by
    apply (mem_standardBorel_iff _).mpr
    change (((slEquivLinear 5).symm ((slEquivLinear 5) (upperSL f))).val).IsUpperTriangular
    rw [MulEquiv.symm_apply_apply]
    exact upperMatrix_triangular f⟩

private theorem matrix_fromParameters (f : UpperPosition → ZMod 2) :
    matrix (fromParameters f) = upperMatrix f := by
  change (((slEquivLinear 5).symm ((slEquivLinear 5) (upperSL f))).val) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private noncomputable def parametersEquiv : standardBorel ≃ (UpperPosition → ZMod 2) where
  toFun g ij := matrix g ij.val.1 ij.val.2
  invFun := fromParameters
  left_inv g := by
    apply Subtype.ext
    apply matrix_injective
    rw [matrix_fromParameters]
    ext i j
    by_cases he : i = j
    · subst j
      simp [upperMatrix, standardBorel_diagonal g.property]
    · by_cases hij : i < j
      · simp [upperMatrix, he, hij]
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm he)
        simp [upperMatrix, he, hij, (mem_standardBorel_iff g).mp g.property hji]
  right_inv f := by
    funext ⟨⟨i, j⟩, hij⟩
    change matrix (fromParameters f) i j = f ⟨(i, j), hij⟩
    rw [matrix_fromParameters]
    simp [upperMatrix, ne_of_lt hij, hij]

/-- The ten freely chosen binary upper entries count the actual stabilizer. -/
theorem standardBorel_card : Nat.card standardBorel = 1024 := by
  rw [Nat.card_congr parametersEquiv, Nat.card_fun]
  have hpos : Nat.card UpperPosition = 10 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hpos]
  norm_num

private theorem linearGroup_card : Nat.card (LinearGroup 5) = 9999360 := by
  calc
    Nat.card (LinearGroup 5) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) :=
      (Nat.card_congr (matrixEquivLinear 5).toEquiv).symm
    _ = ∏ i : Fin 5, (Fintype.card (ZMod 2) ^ 5 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 5
    _ = 9999360 := by decide

/-- The standard full-flag stabilizer has odd index. -/
theorem standardBorel_index : standardBorel.index = 9765 := by
  have h := standardBorel.index_mul_card
  rw [standardBorel_card, linearGroup_card] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 1024 by decide)
  exact h.trans (by decide : 9999360 = 9765 * 1024)

/-- The concrete standard full-flag stabilizer as a Sylow two-subgroup. -/
noncomputable def standardSylow : Sylow 2 (LinearGroup 5) :=
  standardBorel_isPGroup.toSylow (by rw [standardBorel_index]; norm_num)

@[simp] theorem standardSylow_coe : (standardSylow : Subgroup (LinearGroup 5)) = standardBorel := rfl

end BinaryLinear.FiveFlagGeometry.SylowOvergroups
