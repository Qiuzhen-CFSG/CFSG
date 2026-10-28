module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Coordinates
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The standard Sylow two-subgroup of GL₄(2)

The actual full-flag stabilizer has exactly six free upper entries, with all
other entries forced. Its order is therefore 64. The standard finite-field
GL order formula gives ambient order 20160 and index 315, which is odd.
Together with the exponent-eight argument in `Coordinates`, this constructs
the required Sylow subgroup without a flag or conjugacy assumption.

Source: the binary linear case of the characteristic-two parabolic argument
in Aschbacher--Smith, A.3.12, printed p.48 (combined manuscript, 1 March 2004).
Adapted from this repository’s degree-five `FiveFlagGeometry.SylowOvergroups.Sylow`
proof, specialized to the degree-four branch of 15.3.49(l).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
open Chapter2.ComponentRefinement.LieType.Binary

private abbrev UpperPosition := {ij : Fin 4 × Fin 4 // ij.1 < ij.2}

private def upperMatrix (f : UpperPosition → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
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
    Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨upperMatrix f, upperMatrix_det f⟩

private noncomputable def fromParameters (f : UpperPosition → ZMod 2) : standardBorel :=
  ⟨slEquivLinear 4 (upperSL f), by
    apply (mem_standardBorel_iff _).mpr
    change (((slEquivLinear 4).symm ((slEquivLinear 4) (upperSL f))).val).IsUpperTriangular
    rw [MulEquiv.symm_apply_apply]
    exact upperMatrix_triangular f⟩

private theorem matrix_fromParameters (f : UpperPosition → ZMod 2) :
    matrix (fromParameters f) = upperMatrix f := by
  change (((slEquivLinear 4).symm ((slEquivLinear 4) (upperSL f))).val) = _
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

/-- The six freely chosen binary upper entries count the actual stabilizer. -/
theorem standardBorel_card : Nat.card standardBorel = 64 := by
  rw [Nat.card_congr parametersEquiv, Nat.card_fun]
  have hpos : Nat.card UpperPosition = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hpos]
  norm_num

private theorem linearGroup_card : Nat.card (BinaryLinear.GL (Vector 4)) = 20160 := by
  calc
    Nat.card (BinaryLinear.GL (Vector 4)) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
      (Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Vector 4))).toEquiv).symm
    _ = ∏ i : Fin 4, (Fintype.card (ZMod 2) ^ 4 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 4
    _ = 20160 := by decide

/-- The standard full-flag stabilizer has odd index. -/
theorem standardBorel_index : standardBorel.index = 315 := by
  have h := standardBorel.index_mul_card
  rw [standardBorel_card, linearGroup_card] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 64 by decide)
  exact h.trans (by decide : 20160 = 315 * 64)

/-- The concrete standard full-flag stabilizer as a Sylow two-subgroup. -/
noncomputable def standardSylow : Sylow 2 (BinaryLinear.GL (Vector 4)) :=
  standardBorel_isPGroup.toSylow (by rw [standardBorel_index]; norm_num)

@[simp] theorem standardSylow_coe : (standardSylow : Subgroup (BinaryLinear.GL (Vector 4))) = standardBorel := rfl

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
