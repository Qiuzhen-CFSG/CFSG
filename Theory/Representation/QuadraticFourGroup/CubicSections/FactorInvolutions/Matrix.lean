module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FinCases

/-!
# Inverters in characteristic-two SL₂ and PSL₂

Every determinant-one matrix over a field of characteristic two is inverted
by a determinant-one matrix whose square is one. For `[a,b;c,d]` with `b ≠ 0`,
use the lower transvection with parameter `(a+d)/b`; if `c ≠ 0`, use the upper
transvection with parameter `(a+d)/c`. The coordinate swap handles diagonal
matrices. The inverse formula is the adjugate, whose signs vanish in
characteristic two.

Both element relations pass through the actual quotient by the center.
The construction works for every lift, so no assertion about the order of a
chosen lift is needed. This supplies the local matrix fact behind the cubic
dihedral subgroup in GLS, volume 2, Theorem 25.14, Step 4
(`refs/KGroup/GLS2/ChapterG.tex`).
-/

public section

open scoped MatrixGroups CharTwo

namespace Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- Every element of SL₂ in characteristic two has an inverter whose square is one. -/
theorem SpecialLinearGroup.exists_inverter_sq_eq_one_of_charTwo (A : SL(2, F)) :
    ∃ B : SL(2, F), B * B = 1 ∧ B * A * B⁻¹ = A⁻¹ := by
  induction A using SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
    by_cases hb : b ≠ 0
    · let B : SL(2, F) := ⟨!![1, 0; (a + d) / b, 1], by simp⟩
      refine ⟨B, ?_, ?_⟩
      · apply Subtype.ext
        change !![1, 0; (a + d) / b, 1] * !![1, 0; (a + d) / b, 1] = 1
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
      · apply mul_inv_eq_iff_eq_mul.mpr
        apply Subtype.ext
        change !![1, 0; (a + d) / b, 1] * !![a, b; c, d] =
          Matrix.adjugate !![a, b; c, d] * !![1, 0; (a + d) / b, 1]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
            hb, mul_div_cancel₀, add_comm, add_left_comm, mul_comm]
    · have hb : b = 0 := not_ne_iff.mp hb
      subst b
      by_cases hc : c ≠ 0
      · let B : SL(2, F) := ⟨!![1, (a + d) / c; 0, 1], by simp⟩
        refine ⟨B, ?_, ?_⟩
        · apply Subtype.ext
          change !![1, (a + d) / c; 0, 1] * !![1, (a + d) / c; 0, 1] = 1
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
        · apply mul_inv_eq_iff_eq_mul.mpr
          apply Subtype.ext
          change !![1, (a + d) / c; 0, 1] * !![a, 0; c, d] =
            Matrix.adjugate !![a, 0; c, d] * !![1, (a + d) / c; 0, 1]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
              hc, mul_div_cancel₀, add_comm, mul_comm]
      · have hc : c = 0 := not_ne_iff.mp hc
        subst c
        let B : SL(2, F) := ⟨!![0, 1; 1, 0], by simp⟩
        refine ⟨B, ?_, ?_⟩
        · apply Subtype.ext
          change !![(0 : F), 1; 1, 0] * !![0, 1; 1, 0] = 1
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        · apply mul_inv_eq_iff_eq_mul.mpr
          apply Subtype.ext
          change !![0, 1; 1, 0] * !![a, 0; 0, d] =
            Matrix.adjugate !![a, 0; 0, d] * !![0, 1; 1, 0]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, CharTwo.neg_eq]

/-- Projecting an inverter preserves its square and its conjugation relation. -/
theorem ProjectiveSpecialLinearGroup.exists_inverter_sq_eq_one_of_charTwo (x : PSL(2, F)) :
    ∃ b : PSL(2, F), b * b = 1 ∧ b * x * b⁻¹ = x⁻¹ := by
  let q := QuotientGroup.mk' (Subgroup.center SL(2, F))
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, F)) x
  obtain ⟨B, hB, hBA⟩ := SpecialLinearGroup.exists_inverter_sq_eq_one_of_charTwo A
  refine ⟨q B, ?_, ?_⟩
  · simpa only [map_mul, map_one] using congrArg q hB
  · simpa only [map_mul, map_inv] using congrArg q hBA

end Matrix

end
