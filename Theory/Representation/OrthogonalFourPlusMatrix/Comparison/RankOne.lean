/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The orbit of a nonzero singular two-by-two matrix

A nonzero singular matrix factors as a column times a row. Completing each
nonzero column to a determinant-one matrix puts it in the left-right orbit of
`E11`. This supplies singular-vector transport for the determinant comparison.

Adapted from `Atlas/LinearAlgebra/RankOneMatrixTwo.lean`; only the orbit
construction is retained, with private completion and factorization helpers.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.ComparisonAux.MatrixTwo
variable {F : Type*} [Field F]

private def firstColumnMatrix (u : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := by
  classical
  exact if u 0 = 0 then !![u 0, -(u 1)⁻¹; u 1, 0]
  else !![u 0, 0; u 1, (u 0)⁻¹]

private theorem firstColumnMatrix_det (u : Fin 2 → F) (hu : u ≠ 0) :
    (firstColumnMatrix u).det = 1 := by
  classical
  by_cases h : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      funext i
      fin_cases i <;> simp_all
    simp [firstColumnMatrix, h, Matrix.det_fin_two, h1]
  · simp [firstColumnMatrix, h, Matrix.det_fin_two]

private def columnCompletion (u : Fin 2 → F) (hu : u ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨firstColumnMatrix u, firstColumnMatrix_det u hu⟩

private theorem columnCompletion_first (u : Fin 2 → F) (hu : u ≠ 0) (i : Fin 2) :
    (columnCompletion u hu).val i 0 = u i := by
  classical
  by_cases h : u 0 = 0 <;> fin_cases i <;> simp [columnCompletion, firstColumnMatrix, h]

private theorem singular_nonzero_factor (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M ≠ 0) (hd : M.det = 0) :
    ∃ u v : Fin 2 → F, u ≠ 0 ∧ v ≠ 0 ∧ ∀ i j, M i j = u i * v j := by
  classical
  obtain ⟨a, b, hp⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra! h
    apply hM
    ext i j
    exact h i j
  let u : Fin 2 → F := fun i => M i b
  let v : Fin 2 → F := fun j => M a j / M a b
  have hu : u ≠ 0 := by intro h; exact hp (congrFun h a)
  have hv : v ≠ 0 := by
    intro h
    have he := congrFun h b
    change M a b / M a b = 0 at he
    rw [div_self hp] at he
    exact one_ne_zero he
  refine ⟨u, v, hu, hv, ?_⟩
  intro i j
  dsimp [u, v]
  rw [Matrix.det_fin_two] at hd
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    dsimp at hp ⊢ <;> field_simp [hp] <;> first
    | solve | ring
    | simpa only [mul_comm] using (sub_eq_zero.mp hd)
    | simpa only [mul_comm] using (sub_eq_zero.mp hd).symm

/-- The fixed rank-one matrix with sole nonzero entry at (0,0). -/
def E11 : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, 0]

theorem singular_nonzero_SL2_orbit (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M ≠ 0) (hd : M.det = 0) :
    ∃ A B : Matrix.SpecialLinearGroup (Fin 2) F,
      M = A.val * E11 * (B⁻¹).val := by
  obtain ⟨u, v, hu, hv, h⟩ := singular_nonzero_factor M hM hd
  let A := columnCompletion u hu
  let C : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨(columnCompletion v hv).val.transpose, by
      rw [Matrix.det_transpose]; exact (columnCompletion v hv).prop⟩
  refine ⟨A, C⁻¹, ?_⟩
  rw [inv_inv]
  ext i j
  rw [h i j]
  change u i * v j = (A.val * E11 (F := F) * C.val) i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, E11]
  fin_cases i <;> fin_cases j <;>
    simp [A, C, columnCompletion_first, Matrix.transpose_apply]
end ClassicalOrthogonal.FourPlusMatrix.ComparisonAux.MatrixTwo
