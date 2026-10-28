module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/InvariantForm.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.Generators
set_option warningAsError false

@[expose] public section

/-! The symmetric bilinear form in the fixed row-vector coordinates. -/
noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def formMatrix : Mat F :=
  !![0,0,0,0,0,0,1;0,0,0,0,0,1,0;0,0,0,0,1,0,0;
     0,0,0,-1,0,0,0;0,0,1,0,0,0,0;0,1,0,0,0,0,0;1,0,0,0,0,0,0]

theorem formMatrix_square : formMatrix (F := F) * formMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [formMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem alpha_preserves_form (m : ℕ) (x : F) :
    alphaMatrix m x * formMatrix * (alphaMatrix m x).transpose = formMatrix := by
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaMatrix, formMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [hc]

theorem beta_preserves_form (m : ℕ) (x : F) :
    betaMatrix m x * formMatrix * (betaMatrix m x).transpose = formMatrix := by
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [betaMatrix, formMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [hc]

theorem gamma_preserves_form (m : ℕ) (x : F) :
    gammaMatrix m x * formMatrix * (gammaMatrix m x).transpose = formMatrix := by
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaMatrix, formMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [hc]

theorem torus_preserves_form (m : ℕ) (l : Fˣ) :
    (torus m l).val * formMatrix * (torus m l).val.transpose = formMatrix := by
  have hl : (l : F) ≠ 0 := Units.ne_zero l
  have ht : theta F m (l : F) ≠ 0 := (map_ne_zero (theta F m)).2 hl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torus, diagonalUnit, torusDiagonal, formMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, -theta_apply] <;> field_simp <;> ring

theorem upsilon_preserves_form :
    (upsilon : Ambient F).val * formMatrix * (upsilon : Ambient F).val.transpose = formMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upsilon, upsilonMatrix, formMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The full matrix-unit stabilizer of the displayed bilinear form. -/
def formStabilizer : Subgroup (Ambient F) where
  carrier := {a | a.val * formMatrix * a.val.transpose = formMatrix}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a.val * b.val) * formMatrix * (a.val * b.val).transpose = formMatrix
    calc
      _ = a.val * (b.val * formMatrix * b.val.transpose) * a.val.transpose := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = formMatrix := by rw [hb, ha]
  inv_mem' := by
    intro a ha
    change (a⁻¹).val * formMatrix * (a⁻¹).val.transpose = formMatrix
    calc
      _ = (a⁻¹).val * (a.val * formMatrix * a.val.transpose) * (a⁻¹).val.transpose := by rw [ha]
      _ = ((a⁻¹).val * a.val) * formMatrix * ((a⁻¹).val * a.val).transpose := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = formMatrix := by simp [← Units.val_mul]

theorem generated_le_formStabilizer (m : ℕ) : generated F m ≤ formStabilizer := by
  apply (Subgroup.closure_le _).mpr
  intro a ha
  rcases ha with (((ha | ha) | ha) | ha) | ha
  · obtain ⟨x,rfl⟩ := ha; exact alpha_preserves_form m x
  · obtain ⟨x,rfl⟩ := ha; exact beta_preserves_form m x
  · obtain ⟨x,rfl⟩ := ha; exact gamma_preserves_form m x
  · obtain ⟨l,rfl⟩ := ha; exact torus_preserves_form m l
  · obtain rfl := ha; exact upsilon_preserves_form
end Atlas.ReeG2
