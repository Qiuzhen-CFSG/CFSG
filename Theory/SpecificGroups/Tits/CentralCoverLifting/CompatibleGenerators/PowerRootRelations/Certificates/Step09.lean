module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step08

/-! Kernel-checked central word identities, chunk 9.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c2_rule480 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-7, 2, 4, 3, 5] [3, 2, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule91 [-7] [])) (holds_context c2_rule33 [] [7, 2, 9]))
  have l0 := holds_refl [-7, 2, 4, 3, 5]
  have r0 := holds_refl [3, -7, 7, 2, 9]
  have r1 := holds_trans r0 (holds_context c2_rule13 [3] [2, 9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule481 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-7, 2, 4, 3] [3, 2, 9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule480 [] [-5])) (holds_context c2_rule8 [-7, 2, 4, 3] []))
  have l0 := holds_refl [3, 2, 9, -5]
  have r0 := holds_refl [-7, 2, 4, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule489 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 2, 9, 3, -5] [3, 2, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule99 [] [3])) (holds_context c2_rule31 [7, 2, 9] []))
  have l0 := holds_refl [3, 2, 4, 3, 3]
  have l1 := holds_trans l0 (holds_context c2_rule229 [3, 2, 4] [])
  have r0 := holds_refl [7, 2, 9, 3, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule491 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, -7, 2, 4] [2, 9, 3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule489 [-7] [])) (holds_context c2_rule13 [] [2, 9, 3, -5]))
  have l0 := holds_refl [-7, 3, 2, 4]
  have l1 := holds_trans l0 (holds_context c2_rule33 [] [2, 4])
  have r0 := holds_refl [2, 9, 3, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule522 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, 3, -9, 4, 9] [7, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule229 [] [7, 7, 6])) (holds_context c2_rule75 [3] []))
  have l0 := holds_refl [7, 7, 6]
  have r0 := holds_refl [3, 4, -9, 4, 9]
  have r1 := holds_trans r0 (holds_context c2_rule30 [] [-9, 4, 9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule524 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [3, -9, 4, 9] [4, 7, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule522 [4] [])) (holds_context c2_rule230 [] [3, -9, 4, 9]))
  have l0 := holds_refl [4, 7, 7, 6]
  have r0 := holds_refl [3, -9, 4, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule525 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 9, 3, -5, 4] [3, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule229 [3, -7, 2] [])) (holds_context c2_rule98 [] [3]))
  have l0 := holds_refl [3, -7, 2]
  have r0 := holds_refl [2, 9, -5, 4, 3]
  have r1 := holds_trans r0 (holds_context c2_rule237 [2, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule526 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 3, -5, 4] [2, 3, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule525 [2] [])) (holds_context c2_rule228 [] [9, 3, -5, 4]))
  have l0 := holds_refl [2, 3, -7, 2]
  have r0 := holds_refl [9, 3, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule532 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7, 6, -5] [3, 5, 5] := by
  have h0 := c2_rule154
  have l0 := holds_refl [5, 4, 4, 3, 5]
  have l1 := holds_trans l0 (holds_context c2_rule230 [5] [3, 5])
  have l2 := holds_trans l1 (holds_context c2_rule32 [] [5])
  have r0 := holds_refl [-7, 5, 7, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule533 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7, 6] [3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule532 [] [5])) (holds_context c2_rule9 [-7, 5, 7, 6] []))
  have l0 := holds_refl [3, 5, 5, 5]
  have l1 := holds_trans l0 (holds_context c2_rule234 [3] [])
  have r0 := holds_refl [-7, 5, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule534 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 6] [3, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule533 [7] [])) (holds_context c2_rule12 [] [5, 7, 6]))
  have l0 := holds_refl [7, 3, -5]
  have l1 := holds_trans l0 (holds_context c2_rule34 [] [-5])
  have r0 := holds_refl [5, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule535 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7] [3, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule533 [] [6])) (holds_context c2_rule231 [-7, 5, 7] []))
  have l0 := holds_refl [3, -5, 6]
  have r0 := holds_refl [-7, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule536 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -5, 7, -5] [7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule534 [-5] [])) (holds_context c2_rule9 [] [7, 6]))
  have l0 := holds_refl [-5, 3, 7, -5]
  have l1 := holds_trans l0 (holds_context c2_rule31 [] [7, -5])
  have r0 := holds_refl [7, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule537 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 6, 5] [3, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule536 [] [5])) (holds_context c2_rule9 [3, -5, 7] []))
  have l0 := holds_refl [7, 6, 5]
  have r0 := holds_refl [3, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule538 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 7, -5] [3, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule536 [3] [])) (holds_context c2_rule229 [] [-5, 7, -5]))
  have l0 := holds_refl [3, 7, 6]
  have r0 := holds_refl [-5, 7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule544 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -5, 6, -7] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule535 [] [-7])) (holds_context c2_rule12 [-7, 5] []))
  have l0 := holds_refl [3, -5, 6, -7]
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule545 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 6, -7] [3, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule544 [3] [])) (holds_context c2_rule229 [] [-5, 6, -7]))
  have l0 := holds_refl [3, -7, 5]
  have r0 := holds_refl [-5, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule547 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [3, -5, 6, 3] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule535 [] [3])) (holds_context c2_rule34 [-7, 5] []))
  have l0 := holds_refl [3, -5, 6, 3]
  have r0 := holds_refl [-7, 5, 3, 7]
  have r1 := holds_trans r0 (holds_context c2_rule32 [-7] [7])
  have r2 := holds_trans r1 (holds_context c2_rule33 [] [5, 7])
  have r3 := holds_trans r2 (holds_context c2_rule535 [3] [])
  have r4 := holds_trans r3 (holds_context c2_rule229 [] [-5, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem c2_rule548 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [-5, 6, 3] [3, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule547 [3] [])) (holds_context c2_rule229 [] [-5, 6, 3]))
  have l0 := holds_refl [3, -5, 6]
  have r0 := holds_refl [-5, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule554 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 4, -5] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule537 [] [3])) (holds_context c2_rule32 [7, 6] []))
  have l0 := holds_refl [3, -5, 7, 3]
  have l1 := holds_trans l0 (holds_context c2_rule34 [3, -5] [])
  have l2 := holds_trans l1 (holds_context c2_rule31 [3] [7])
  have l3 := holds_trans l2 (holds_context c2_rule229 [] [-5, 7])
  have r0 := holds_refl [7, 6, 3, 5]
  have r1 := holds_trans r0 (holds_context c2_rule441 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule556 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 4, -5] [6, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule554 [6] [])) (holds_context c2_rule231 [] [7, 4, -5]))
  have l0 := holds_refl [6, -5, 7]
  have r0 := holds_refl [7, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule564 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s3_s5) [3, 5, -7, 5] [6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule545 [5] [])) (holds_context c2_rule8 [] [6, -7]))
  have l0 := holds_refl [5, 3, -7, 5]
  have l1 := holds_trans l0 (holds_context c2_rule32 [] [-7, 5])
  have r0 := holds_refl [6, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule566 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s3_s5) [5, -7, 5] [3, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule564 [3] [])) (holds_context c2_rule229 [] [5, -7, 5]))
  have l0 := holds_refl [3, 6, -7]
  have r0 := holds_refl [5, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule569 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [6, 3] [3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule548 [5] [])) (holds_context c2_rule8 [] [6, 3]))
  have l0 := holds_refl [5, 3, -5, 6]
  have l1 := holds_trans l0 (holds_context c2_rule32 [] [-5, 6])
  have l2 := holds_trans l1 (holds_context c2_rule8 [3] [6])
  have r0 := holds_refl [6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule581 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, -5, 7] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule556 [-7] [])) (holds_context c2_rule13 [] [4, -5]))
  have l0 := holds_refl [-7, 6, -5, 7]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule582 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, -5] [4, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule581 [] [-7])) (holds_context c2_rule12 [-7, 6, -5] []))
  have l0 := holds_refl [4, -5, -7]
  have r0 := holds_refl [-7, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule586 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [5, 2, -5, 7] [3, 6, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule566 [] [2])) (holds_context c2_rule252 [5] []))
  have l0 := holds_refl [3, 6, -7, 2]
  have r0 := holds_refl [5, 2, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule602 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7, 5] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule582 [] [5])) (holds_context c2_rule9 [-7, 6] []))
  have l0 := holds_refl [4, -5, -7, 5]
  have r0 := holds_refl [-7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule603 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 5] [4, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule602 [4] [])) (holds_context c2_rule230 [] [-5, -7, 5]))
  have l0 := holds_refl [4, -7, 6]
  have r0 := holds_refl [-5, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule612 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [3, 5, 5, -9] [-9, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule230 [] [3, 5, 5, -9])) (holds_context c2_rule138 [4] []))
  have l0 := holds_refl [3, 5, 5, -9]
  have r0 := holds_refl [4, 4, -9, 4, 6]
  have r1 := holds_trans r0 (holds_context c2_rule230 [] [-9, 4, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule613 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-9, 4, 6, 9] [3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule612 [] [9])) (holds_context c2_rule17 [3, 5, 5] []))
  have l0 := holds_refl [-9, 4, 6, 9]
  have r0 := holds_refl [3, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule614 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, -9, 4, 6] [5, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule612 [3] [])) (holds_context c2_rule229 [] [5, 5, -9]))
  have l0 := holds_refl [3, -9, 4, 6]
  have r0 := holds_refl [5, 5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule615 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [9, 3, 5, 5] [4, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule613 [9] [])) (holds_context c2_rule16 [] [4, 6, 9]))
  have l0 := holds_refl [9, 3, 5, 5]
  have r0 := holds_refl [4, 6, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule616 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 5, -9, 6] [3, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule614 [] [6])) (holds_context c2_rule231 [3, -9, 4] []))
  have l0 := holds_refl [5, 5, -9, 6]
  have r0 := holds_refl [3, -9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule618 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [4, 6, 9, 5] [9, 3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule615 [] [5])) (holds_context c2_rule234 [9, 3] []))
  have l0 := holds_refl [4, 6, 9, 5]
  have r0 := holds_refl [9, 3, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule621 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 5, -9, 4] [-5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule616 [5] [])) (holds_context c2_rule234 [] [-9, 6]))
  have l0 := holds_refl [5, 3, -9, 4]
  have l1 := holds_trans l0 (holds_context c2_rule32 [] [-9, 4])
  have r0 := holds_refl [-5, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule624 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [9, 3, -5, 2] [2, 8, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule618 [] [2])) (holds_context c2_rule256 [4, 6] []))
  have l0 := holds_refl [9, 3, -5, 2]
  have r0 := holds_refl [4, 6, 2, 7]
  have r1 := holds_trans r0 (holds_context c2_rule43 [4] [7])
  have r2 := holds_trans r1 (holds_context c2_rule42 [] [6, 7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c2_rule628 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, -9, 4, 6] [3, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule621 [] [4])) (holds_context c2_rule230 [3, 5, -9] []))
  have l0 := holds_refl [-5, -9, 6, 4]
  have l1 := holds_trans l0 (holds_context c2_rule35 [-5, -9] [])
  have r0 := holds_refl [3, 5, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule638 : Holds (normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .viii_s1) [2, 3, 2, -9, -7] [9, 4, 3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule234 [9, 4, 3] [])) (holds_context c2_rule152 [] [5]))
  have l0 := holds_refl [9, 4, 3, -5]
  have r0 := holds_refl [4, 6, 9, 4, 5]
  have r1 := holds_trans r0 (holds_context c2_rule164 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule768 : Holds ((normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 9, 8, 5, 2] [-9, 4, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule273 [-9] [])) (holds_context c2_rule44 [] [8, 5, 2]))
  have l0 := holds_refl [-9, 4, 9, 7]
  have r0 := holds_refl [2, 9, 8, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
