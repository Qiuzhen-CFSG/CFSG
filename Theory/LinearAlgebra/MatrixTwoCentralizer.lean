module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Centralizers of nonscalar two-dimensional matrices

Over an arbitrary field, every matrix commuting with a nonscalar two-by-two
matrix A is a linear combination of the identity and A. Consequently any two
matrices commuting with A commute with each other. No characteristic,
finiteness, or semisimplicity assumption is required.

If an offdiagonal entry of A is nonzero, the commuting equations determine
the other matrix from its two corresponding coefficients. Transposition
handles the other offdiagonal entry. Otherwise A is diagonal with distinct
diagonal entries, forcing its centralizer matrices to be diagonal as well.
The explicit linear-combination formulas complete all three cases.

This elementary matrix-centralizer fact supplies the scalar centralizer of
a noncommutative GL2 subgroup used in ABG II.3 Proposition 3(iv), article
pages 27–28.
-/

namespace Matrix
variable {F : Type*} [Field F]

private theorem eq_linear_of_commute_upper
    (A B : Matrix (Fin 2) (Fin 2) F) (hA : A 0 1 ≠ 0) (hAB : A * B = B * A) :
    ∃ a b : F, B = a • 1 + b • A := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hAB
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hAB
  simp only [mul_apply, Fin.sum_univ_two] at h00 h01
  refine ⟨B 0 0 - (B 0 1 / A 0 1) * A 0 0, B 0 1 / A 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · field_simp
  · field_simp
    linear_combination h00
  · field_simp
    linear_combination h01

public theorem exists_eq_smul_one_add_smul_of_commute_two
    (A B : Matrix (Fin 2) (Fin 2) F) (hA : ¬ ∃ a : F, A = a • 1)
    (hAB : A * B = B * A) : ∃ a b : F, B = a • 1 + b • A := by
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · have had : A 0 0 - A 1 1 ≠ 0 := by
        intro h
        apply hA
        refine ⟨A 0 0, ?_⟩
        have hdiag := sub_eq_zero.mp h
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, hdiag]
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hAB
      have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hAB
      simp only [mul_apply, Fin.sum_univ_two, hb, hc, mul_zero, zero_mul,
        add_zero, zero_add] at h01 h10
      have hB01 : B 0 1 = 0 := by
        apply (mul_eq_zero.mp (show (A 0 0 - A 1 1) * B 0 1 = 0 by
          linear_combination h01)).resolve_left had
      have hB10 : B 1 0 = 0 := by
        apply (mul_eq_zero.mp (show (A 0 0 - A 1 1) * B 1 0 = 0 by
          linear_combination -h10)).resolve_left had
      refine ⟨B 0 0 - ((B 0 0 - B 1 1) / (A 0 0 - A 1 1)) * A 0 0,
        (B 0 0 - B 1 1) / (A 0 0 - A 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hB01, hB10]
      field_simp
      ring
    · obtain ⟨a, b, he⟩ := eq_linear_of_commute_upper A.transpose B.transpose hc (by
        simpa only [transpose_mul] using congrArg Matrix.transpose hAB.symm)
      refine ⟨a, b, ?_⟩
      simpa using congrArg Matrix.transpose he
  · exact eq_linear_of_commute_upper A B hb hAB

public theorem commute_of_commute_nonscalar_two
    (A B C : Matrix (Fin 2) (Fin 2) F) (hA : ¬ ∃ a : F, A = a • 1)
    (hAB : A * B = B * A) (hAC : A * C = C * A) : B * C = C * B := by
  obtain ⟨a, b, rfl⟩ := exists_eq_smul_one_add_smul_of_commute_two A B hA hAB
  obtain ⟨c, d, rfl⟩ := exists_eq_smul_one_add_smul_of_commute_two A C hA hAC
  simp [add_mul, mul_add, smul_smul, mul_comm]
  abel

end Matrix
