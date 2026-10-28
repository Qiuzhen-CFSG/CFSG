module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.Kernel.MatrixSeparation
/-!
# Four-by-four matrices of the split B₂ factors

Conjugating the two simple root matrices by the opposite simple Weyl
permutation gives the two nonsimple positive root matrices. Multiplying the
four positive matrices in root order gives the explicit upper unitriangular
matrix used to separate the Bruhat factors.

These symbolic identities hold for every coefficient-field parameter.
Source: GLS3 §§2.3–2.4, for the Levi in Aschbacher–Smith F.1.12(I)(5), p.263.
-/

set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
variable {m : ℕ}

theorem simplePositiveMatrix_0 (t : CoefficientField m) :
    generatorMatrix m 0 t = positiveRootMatrix 0 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [positiveRootMatrix, generatorMatrix, Fin.isValue, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val_succ', Matrix.cons_val_zero',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

theorem simplePositiveMatrix_1 (t : CoefficientField m) :
    generatorMatrix m 1 t = positiveRootMatrix 1 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [positiveRootMatrix, generatorMatrix, Fin.isValue, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val_succ', Matrix.cons_val_zero',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

theorem reflectedShortMatrix (t : CoefficientField m) : weylMatrix (m := m) 0 * generatorMatrix m 1 t * weylMatrix 0 =
    positiveRootMatrix 2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [weylMatrix, positiveRootMatrix, generatorMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
      Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]

theorem reflectedLongMatrix (t : CoefficientField m) : weylMatrix (m := m) 1 * generatorMatrix m 0 t * weylMatrix 1 =
    positiveRootMatrix 3 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [weylMatrix, positiveRootMatrix, generatorMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
      Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]

theorem positiveProductMatrix (p : Fin 4 → CoefficientField m) : positiveRootMatrix 0 (p 0) * positiveRootMatrix 1 (p 1) *
    positiveRootMatrix 2 (p 2) * positiveRootMatrix 3 (p 3) = upperMatrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [positiveRootMatrix, generatorMatrix, upperMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
        Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
