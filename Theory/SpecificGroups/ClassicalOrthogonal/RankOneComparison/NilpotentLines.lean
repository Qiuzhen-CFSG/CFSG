/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: Lean 4.33 modules, narrow imports, and CFSG quadratic-isometry carriers.
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-!
# Nilpotent lines in determinant-one coordinates

Adapted from ATLAS `LinearAlgebra/RankOneMatrixTwo.lean` and
`TraceZeroNilpotentMatrixTwo.lean`. A nonzero singular trace-zero matrix
is conjugate under SL₂ to a nonzero upper matrix unit. Complete a nonzero
column to a determinant-one basis, then use the trace to remove the
remaining diagonal entry. This gives the singular-line orbit needed for
the actual rank-one odd orthogonal comparison (GLS3 §2.7).
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.RankOneComparison.MatrixTwo
open Matrix
variable {F : Type*} [Field F]

def firstColumnMatrix (u : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := by
  classical
  exact if u 0 = 0 then !![u 0, -(u 1)⁻¹; u 1, 0]
  else !![u 0, 0; u 1, (u 0)⁻¹]

theorem firstColumnMatrix_det (u : Fin 2 → F) (hu : u ≠ 0) :
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

def columnCompletion (u : Fin 2 → F) (hu : u ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨firstColumnMatrix u, firstColumnMatrix_det u hu⟩

theorem columnCompletion_first (u : Fin 2 → F) (hu : u ≠ 0) (i : Fin 2) :
    (columnCompletion u hu).val i 0 = u i := by
  classical
  by_cases h : u 0 = 0 <;> fin_cases i <;> simp [columnCompletion, firstColumnMatrix, h]

theorem singular_nonzero_factor (M : Matrix (Fin 2) (Fin 2) F)
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

theorem traceZero_singular_SL2_line (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M ≠ 0) (hd : M.det = 0) (ht : M.trace = 0) :
    ∃ A : SpecialLinearGroup (Fin 2) F, ∃ c : F, c ≠ 0 ∧
      M = A.val * !![0,c;0,0] * (A⁻¹).val := by
  obtain ⟨u,v,hu,hv,h⟩ := singular_nonzero_factor M hM hd
  let A := columnCompletion u hu
  let N := (A⁻¹).val * M * A.val
  have ht' : u 0 * v 0 + u 1 * v 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, h] using ht
  have hcol (i : Fin 2) : (M * A.val) i 0 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, A, columnCompletion_first, h]
    calc
      u i * v 0 * u 0 + u i * v 1 * u 1 =
          u i * (u 0 * v 0 + u 1 * v 1) := by ring
      _ = 0 := by rw [ht',mul_zero]
  have hncol (i : Fin 2) : N i 0 = 0 := by
    dsimp [N]
    rw [Matrix.mul_assoc]
    simp [Matrix.mul_apply, hcol]
  have hntrace : N.trace = 0 := by
    change ((A⁻¹).val * M * A.val).trace = 0
    rw [Matrix.trace_mul_cycle, ← SpecialLinearGroup.coe_mul,
      mul_inv_cancel, SpecialLinearGroup.coe_one, one_mul]
    exact ht
  have h11 : N 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, hncol] using hntrace
  have hn : N = !![0,N 0 1;0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hncol,h11]
  have hrecover : A.val * N * (A⁻¹).val = M := by
    change A.val * ((A⁻¹).val * M * A.val) * (A⁻¹).val = M
    calc
      _ = (A.val * (A⁻¹).val) * M * (A.val * (A⁻¹).val) := by simp only [mul_assoc]
      _ = M := by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel,
        SpecialLinearGroup.coe_one, one_mul, mul_one]
  refine ⟨A,N 0 1,?_,?_⟩
  · intro hc
    have hz : N = 0 := by rw [hn,hc]; ext i j; fin_cases i <;> fin_cases j <;> rfl
    apply hM
    simpa [hz] using hrecover.symm
  · rw [← hn]
    exact hrecover.symm
end ClassicalOrthogonal.RankOneComparison.MatrixTwo
