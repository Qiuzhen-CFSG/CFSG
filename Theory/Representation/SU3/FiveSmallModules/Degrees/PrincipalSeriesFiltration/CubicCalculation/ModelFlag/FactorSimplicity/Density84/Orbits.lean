module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Pool08

/-!
# Checked rank-one operator and spanning orbits in dimension 84

The final pool value is the outer product of the first column and row seeds.
Both saved bases are orbits under the exact middle-quotient generators. Their
checked left inverses prove that both orbits span the whole coefficient space.
Transposing the generators is solely an arithmetic device for computing column
orbits with packed rows; the final identities use the original column action.

All finite identities are checked by kernel reduction. Arithmetic declarations
are sequential to bound memory. Source motivation: Guralnick–Malle Proposition
4.3, p.10; Aschbacher–Smith K.2, p.453. See `source/README.md`.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
open Certificate.Packed

theorem rank_one : matrix 84 p85 = Matrix.vecMulVec (vector (cols 0)) (vector (rows 0)) := by
  have h : ∀ i : Fin 84, p85 i =
      scale ((cols 0).1.testBit i.val) ((cols 0).2.testBit i.val) (rows 0) := by
    decide +kernel
  rw [funext h, rank_one_correct]

theorem generators_transpose (a : Fin 2) :
    matrix 84 (transGenerators a) = (middleMatrices a).transpose := by
  have h : ∀ (a : Fin 2) (i j : Fin 84),
      ((transGenerators a i).1.testBit j.val, (transGenerators a i).2.testBit j.val) =
        ((B a j).1.testBit i.val, (B a j).2.testBit i.val) := by decide +kernel
  exact transpose_correct (B a) (transGenerators a) (h a)

theorem column_parents : ∀ j : Fin 83, (cp j).val < j.val + 1 := by decide +kernel

theorem row_parents : ∀ j : Fin 83, (rp j).val < j.val + 1 := by decide +kernel

theorem column_recurrence (j : Fin 83) :
    vector (cols j.succ) = (middleMatrices (ca j)).mulVec (vector (cols (cp j))) := by
  have h : ∀ j : Fin 83,
      rowProduct (cols (cp j)) (transGenerators (ca j)) = cols j.succ := by decide +kernel
  rw [← Matrix.vecMul_transpose, ← generators_transpose (ca j), ← rowProduct_correct, h]

theorem row_recurrence (j : Fin 83) :
    vector (rows j.succ) = Matrix.vecMul (vector (rows (rp j))) (middleMatrices (ra j)) := by
  have h : ∀ j : Fin 83, rowProduct (rows (rp j)) (B (ra j)) = rows j.succ := by
    decide +kernel
  change vector (rows j.succ) = Matrix.vecMul (vector (rows (rp j))) (matrix 84 (B (ra j)))
  rw [← rowProduct_correct, h]

theorem column_left_inverse : matrix 84 ci * matrix 84 cols = 1 := by
  have h : ∀ i, mul ci cols i = identity 84 i := by decide +kernel
  rw [← matrix_mul, funext h, matrix_identity]

theorem row_left_inverse : matrix 84 ri * matrix 84 rows = 1 := by
  have h : ∀ i, mul ri rows i = identity 84 i := by decide +kernel
  rw [← matrix_mul, funext h, matrix_identity]

theorem column_span : Submodule.span CoefficientField (Set.range (matrix 84 cols)) = ⊤ :=
  span_rows_of_left_inverse _ _ column_left_inverse

theorem row_span : Submodule.span CoefficientField (Set.range (matrix 84 rows)) = ⊤ :=
  span_rows_of_left_inverse _ _ row_left_inverse

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
