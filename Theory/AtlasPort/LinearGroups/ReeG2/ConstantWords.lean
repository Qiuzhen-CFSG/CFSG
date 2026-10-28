module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/ConstantWords.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootGroup
public import Theory.AtlasPort.LinearGroups.ReeG2.Torus
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

private def ca : Mat F := !![1, 1, 0, 0, -1, -1, 1;
    0, 1, 1, 1, -1, 0, -1;
    0, 0, 1, 1, -1, 0, 1;
    0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 1, -1, 1;
    0, 0, 0, 0, 0, 1, -1;
    0, 0, 0, 0, 0, 0, 1]

private def cb : Mat F := !![1, 0, -1, 0, -1, 0, -1;
    0, 1, 0, 1, 0, -1, 0;
    0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

private def cc : Mat F := !![1, 0, 0, -1, 0, -1, -1;
    0, 1, 0, 0, -1, 0, 1;
    0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, -1;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

private def cw : Mat F := !![0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, -1, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0]

private def ci : Mat F := !![1, -1, 1, 0, 1, -1, 1;
    0, 1, -1, 0, 0, 0, -1;
    0, 0, 1, -1, -1, -1, -1;
    0, 0, 0, 1, -1, -1, 0;
    0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 1]

private def ch : Mat F := !![-1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, -1]

private def cw0 : Mat F := !![1, 0, 1, 0, 1, 0, -1;
    0, 1, 0, -1, 0, -1, 0;
    -1, 0, 0, 0, -1, 0, 0;
    0, -1, 0, -1, 0, 0, 0;
    -1, 0, -1, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0]

private theorem cw0_step : (cb : Mat F) * cw = cw0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cb,cw,cw0,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def cw1 : Mat F := !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    -1, 0, 1, 0, 0, 0, 0;
    0, -1, 0, 1, 0, 0, 0;
    -1, 0, 0, 0, 1, 0, 0;
    0, -1, 0, -1, 0, 1, 0;
    -1, 0, 1, 0, 1, 0, 1]

private theorem cw1_step : (cw0 : Mat F) * cb = cw1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cw0,cb,cw1,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def cw2 : Mat F := !![0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, -1, 0, 1;
    0, 0, 0, -1, 0, 1, 0;
    0, 0, -1, 0, 0, 0, 1;
    0, -1, 0, 1, 0, 1, 0;
    -1, 0, -1, 0, -1, 0, 1]

private theorem cw2_step : (cw1 : Mat F) * cw = cw2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cw1,cw,cw2,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def cw3 : Mat F := !![0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, -1, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0]

private theorem cw3_step : (cw2 : Mat F) * cb = cw3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cw2,cb,cw3,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch0 : Mat F := !![-1, 1, 1, 0, 0, -1, -1;
    1, 0, 1, -1, -1, -1, 0;
    -1, 0, 1, -1, -1, 0, 0;
    0, 0, -1, -1, 0, 0, 0;
    -1, 1, -1, 0, 0, 0, 0;
    1, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0]

private theorem ch0_step : (ca : Mat F) * cw = ch0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ca,cw,ch0,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch1 : Mat F := !![-1, -1, -1, -1, 1, -1, 1;
    1, -1, -1, 1, 0, 0, -1;
    -1, 1, 0, 1, 1, 0, 1;
    0, 0, -1, 0, -1, -1, 1;
    -1, -1, 0, 1, 0, -1, -1;
    1, 1, -1, 0, 1, -1, -1;
    -1, 1, -1, 0, -1, 1, -1]

private theorem ch1_step : (ch0 : Mat F) * ci = ch1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ch0,ci,ch1,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch2 : Mat F := !![-1, 1, -1, 1, 1, 1, 1;
    1, 0, 0, -1, 1, 1, -1;
    -1, 0, -1, -1, 0, -1, 1;
    -1, 1, 1, 0, 1, 0, 0;
    1, 1, 0, -1, 0, 1, 1;
    1, 1, -1, 0, 1, -1, -1;
    1, -1, 1, 0, 1, -1, 1]

private theorem ch2_step : (ch1 : Mat F) * cw = ch2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ch1,cw,ch2,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch3 : Mat F := !![-1, 1, 0, -1, -1, 1, -1;
    1, 0, -1, -1, 0, 0, -1;
    -1, 0, 0, -1, 1, 1, 1;
    -1, 1, -1, 1, -1, -1, 0;
    1, 1, -1, 0, -1, -1, 0;
    1, 1, 1, 1, 0, 1, 1;
    1, -1, 0, -1, 0, 0, -1]

private theorem ch3_step : (ch2 : Mat F) * cb = ch3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ch2,cb,ch3,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch4 : Mat F := !![1, -1, 1, 1, 0, -1, 1;
    1, 0, 0, 1, 1, 0, -1;
    -1, -1, -1, 1, 0, 0, 1;
    0, 1, 1, -1, 1, -1, 1;
    0, 1, 1, 0, 1, -1, -1;
    -1, -1, 0, -1, -1, -1, -1;
    1, 0, 0, 1, 0, 1, -1]

private theorem ch4_step : (ch3 : Mat F) * cw = ch4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ch3,cw,ch4,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch5 : Mat F := !![1, -1, 1, 0, 1, -1, 1;
    1, 0, 0, 0, 1, -1, 0;
    -1, -1, -1, -1, 1, 0, 0;
    0, 1, 1, -1, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0;
    -1, -1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0]

private theorem ch5_step : (ch4 : Mat F) * cc = ch5 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ch4,cc,ch5,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch6 : Mat F := !![-1, 1, -1, 0, -1, 1, -1;
    0, 1, -1, 0, 0, 0, -1;
    0, 0, -1, 1, 1, 1, 1;
    0, 0, 0, 1, -1, -1, 0;
    0, 0, 0, 0, -1, -1, 0;
    0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, -1]

private theorem ch6_step : (ch5 : Mat F) * cw = ch6 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ch5,cw,ch6,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private def ch7 : Mat F := !![-1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, -1]

private theorem ch7_step : (ch6 : Mat F) * ca = ch7 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ch6,ca,ch7,Matrix.mul_apply,Fin.sum_univ_succ] <;> reduce_mod_char!

private theorem alpha_one_constant (m : ℕ) : (alpha (F := F) m 1).val = ca := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alpha,alphaMatrix,ca,-theta_apply]
private theorem beta_one_constant (m : ℕ) : (beta (F := F) m 1).val = cb := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [beta,betaMatrix,cb,-theta_apply]
private theorem gamma_one_constant (m : ℕ) : (gamma (F := F) m 1).val = cc := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma,gammaMatrix,cc,-theta_apply]
private theorem upsilon_constant : (upsilon : Ambient F).val = cw := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upsilon,upsilonMatrix,cw]
private theorem torus_minus_one_constant (m : ℕ) : (torus (F := F) m (-1)).val = ch := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torus,diagonalUnit,torusDiagonal,ch,-theta_apply]
private theorem alpha_one_inverse_constant (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) : ((alpha (F := F) m 1)⁻¹).val = ci := by
  have he : (alpha (F := F) m 1)⁻¹ = rootElement m (-1) (-1) 1 := by
    have hh := rootElement_inv (F := F) m hcard 1 0 0
    simpa [rootElement,-theta_apply] using hh
  rw [he]
  change rootMatrix m (-1) (-1) 1 = ci
  rw [rootMatrix_expanded]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rootExpanded,ci,-theta_apply] <;> reduce_mod_char!

/-- A length-three root-conjugate word for the actual Weyl involution. -/
theorem beta_weyl_word (m : ℕ) :
    beta (F := F) m 1 * (upsilon * beta m 1 * upsilon) * beta m 1 = upsilon := by
  apply Units.ext
  simp only [Units.val_mul, beta_one_constant, upsilon_constant]
  simp only [← Matrix.mul_assoc]
  rw [cw0_step,cw1_step,cw2_step,cw3_step]
  rfl

/-- A short root-conjugate word for the minus-one torus element. -/
theorem minus_one_torus_word (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    alpha (F := F) m 1 * (upsilon * alpha m 1 * upsilon)⁻¹ * beta m 1 *
      (upsilon * gamma m 1 * upsilon) * alpha m 1 = torus m (-1) := by
  have hi : (upsilon : Ambient F)⁻¹ = upsilon := inv_eq_of_mul_eq_one_right upsilon_square
  rw [mul_inv_rev,mul_inv_rev,hi]
  apply Units.ext
  simp only [Units.val_mul,alpha_one_constant,beta_one_constant,gamma_one_constant,
    alpha_one_inverse_constant m hcard,upsilon_constant,torus_minus_one_constant]
  simp only [← Matrix.mul_assoc]
  rw [ch0_step,ch1_step,ch2_step,ch3_step,ch4_step,ch5_step,ch6_step,ch7_step]
  rfl

end Atlas.ReeG2
