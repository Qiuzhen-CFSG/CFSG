module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step03

/-! Kernel-checked central word identities, chunk 4.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c1_rule396 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 6, 7, 7] [3, 4, -7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule85 [] [-7])) (holds_context c1_rule28 [5, 5, 6] []))
  have l0 := holds_refl [3, 4, -7, 6, -7]
  have r0 := holds_refl [5, 5, 6, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule397 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 6, 3, -7] [3, 4, -7, 6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule85 [] [3])) (holds_context c1_rule33 [5, 5, 6] []))
  have l0 := holds_refl [3, 4, -7, 6, 3]
  have r0 := holds_refl [5, 5, 6, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule400 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [7, 4, 6, 3, -7, 6] [6, 3, 7, 4, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule85 [7, 6] [])) (holds_context c1_rule81 [] [6, -7]))
  have l0 := holds_refl [7, 6, 3, 4, -7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule208 [7] [-7, 6])
  have r0 := holds_refl [6, 3, 7, 4, 6, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule424 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 4, 7, 2, 9] [2, 3, 8, 3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule91 [4] [])) (holds_context c1_rule30 [] [7, 2, 9]))
  have l0 := holds_refl [4, 2, 3, 4, 5]
  have l1 := holds_trans l0 (holds_context c1_rule42 [] [3, 4, 5])
  have l2 := holds_trans l1 (holds_context c1_rule209 [2] [5])
  have l3 := holds_trans l2 (holds_context c1_rule297 [2] [])
  have r0 := holds_refl [3, 4, 7, 2, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule429 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 3, 4, 5, 2] [3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule91 [] [2])) (holds_context c1_rule45 [3, 7, 2] []))
  have l0 := holds_refl [2, 3, 4, 5, 2]
  have r0 := holds_refl [3, 7, 2, 2, -9]
  have r1 := holds_trans r0 (holds_context c1_rule199 [3, 7] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule434 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 8, -9, 6] [3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule92 [8] [])) (holds_context c1_rule41 [] [3, 7, 7, 2]))
  have l0 := holds_refl [8, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule209 [] [5, 5])
  have l2 := holds_trans l1 (holds_context c1_rule297 [] [5])
  have l3 := holds_trans l2 (holds_context c1_rule9 [3, 8, 3] [])
  have r0 := holds_refl [2, 4, 3, 7, 7, 2]
  have r1 := holds_trans r0 (holds_context c1_rule30 [2] [7, 7, 2])
  have r2 := holds_trans r1 (holds_context c1_rule332 [2] [])
  have r3 := holds_trans r2 (holds_context c1_rule199 [] [9, 8, -9, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r3))) (by central_nf)

theorem c1_rule436 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 8, -9, 8] [-7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule92 [6] [])) (holds_context c1_rule43 [] [3, 7, 7, 2]))
  have l0 := holds_refl [6, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule208 [] [5, 5])
  have l2 := holds_trans l1 (holds_context c1_rule375 [] [])
  have r0 := holds_refl [2, 6, 3, 7, 7, 2]
  have r1 := holds_trans r0 (holds_context c1_rule317 [2] [])
  have r2 := holds_trans r1 (holds_context c1_rule199 [] [9, 8, -9, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule441 : Holds ((normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 4, 5, 2] [2, 3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule92 [] [-5, 2])) (holds_context c1_rule49 [2, 3, 7, 7] []))
  have l0 := holds_refl [3, 4, 5, 5, -5, 2]
  have l1 := holds_trans l0 (holds_context c1_rule8 [3, 4, 5] [2])
  have r0 := holds_refl [2, 3, 7, 7, -7, -9]
  have r1 := holds_trans r0 (holds_context c1_rule12 [2, 3, 7] [-9])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule458 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [5, 2, 9, 3] [3, 2, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule94 [] [3])) (holds_context c1_rule34 [3, 2, 8, 3] []))
  have l0 := holds_refl [5, 2, 9, 3]
  have r0 := holds_refl [3, 2, 8, 3, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule200 [3, 2, 8] [7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule464 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -7, -5, 2, 8, 3] [2, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule95 [-7] [])) (holds_context c1_rule33 [] [-5, 2, 8, 3]))
  have l0 := holds_refl [-7, 2, 9, -7]
  have l1 := holds_trans l0 (holds_context c1_rule53 [] [-7])
  have r0 := holds_refl [3, -7, -5, 2, 8, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule504 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 8, 9, 8, -9] [2, -7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule100 [] [6])) (holds_context c1_rule86 [2, 3] []))
  have l0 := holds_refl [3, 7, 7, 2, 6]
  have l1 := holds_trans l0 (holds_context c1_rule337 [] [])
  have r0 := holds_refl [2, 3, 3, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c1_rule200 [2] [-7, 6, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule522 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-7, 6, 7, 8] [3, 8, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule104 [] [8, 6])) (holds_context c1_rule60 [3, 5, 5] []))
  have l0 := holds_refl [3, 4, 5, 5, 8, 6]
  have l1 := holds_trans l0 (holds_context c1_rule309 [3, 4] [6])
  have l2 := holds_trans l1 (holds_context c1_rule201 [3] [8, 3, 6])
  have r0 := holds_refl [3, 5, 5, 4, 6, 8]
  have r1 := holds_trans r0 (holds_context c1_rule296 [3] [6, 8])
  have r2 := holds_trans r1 (holds_context c1_rule86 [3] [8])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [-7, 6, 7, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r3))) (by central_nf)

theorem c1_rule524 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -7, -5, 2, 8] [2, 3, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule105 [-7] [])) (holds_context c1_rule33 [] [-5, 2, 8]))
  have l0 := holds_refl [-7, 2, 9, 3, -7]
  have l1 := holds_trans l0 (holds_context c1_rule53 [] [3, -7])
  have l2 := holds_trans l1 (holds_context c1_rule31 [2] [-7])
  have r0 := holds_refl [3, -7, -5, 2, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule531 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, 2, 8, 3] [9, 7, 9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule106 [2] [])) (holds_context c1_rule51 [] [9, -7]))
  have l0 := holds_refl [2, 3, 2, 8, 3]
  have r0 := holds_refl [9, 7, 9, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule560 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 4, 5, 5] [-5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule115 [] [9, 9, 3])) (holds_context c1_rule112 [3, 5, 10] []))
  have l0 := holds_refl [3, -5, 4, 9, 9, 9, 9, 3]
  have l1 := holds_trans l0 (holds_context c1_rule207 [3, -5, 4] [9, 3])
  have l2 := holds_trans l1 (holds_context c1_rule17 [3, -5, 4] [3])
  have l3 := holds_trans l2 (holds_context c1_rule30 [3, -5] [])
  have l4 := holds_trans l3 (holds_context c1_rule31 [3] [4])
  have l5 := holds_trans l4 (holds_context c1_rule200 [] [-5, 4])
  have r0 := holds_refl [3, 5, 10, 10, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule204 [3, 5] [3, 4, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule32 [3] [4, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [5, 4, 5, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r3))) (by central_nf)

theorem c1_rule687 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [6, 7, 6, -9, 6] [3, -7, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule146 [7] [])) (holds_context c1_rule34 [] [4, 5, 5, -9, 6]))
  have l0 := holds_refl [7, 3, 7, 7, 6, -9]
  have l1 := holds_trans l0 (holds_context c1_rule34 [] [7, 7, 6, -9])
  have l2 := holds_trans l1 (holds_context c1_rule206 [3] [6, -9])
  have r0 := holds_refl [3, 7, 4, 5, 5, -9, 6]
  have r1 := holds_trans r0 (holds_context c1_rule355 [] [-9, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule717 : Holds (normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [4, 9, 5, 5] [6, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule149 [9, 6] [])) (holds_context c1_rule72 [] [7, 5, 5, 4]))
  have l0 := holds_refl [9, 6, 6, -9, 6, 9, 3]
  have l1 := holds_trans l0 (holds_context c1_rule202 [9] [-9, 6, 9, 3])
  have l2 := holds_trans l1 (holds_context c1_rule16 [] [6, 9, 3])
  have r0 := holds_refl [4, 9, 4, -7, 7, 5, 5, 4]
  have r1 := holds_trans r0 (holds_context c1_rule13 [4, 9, 4] [5, 5, 4])
  have r2 := holds_trans r1 (holds_context c1_rule296 [4, 9, 4] [])
  have r3 := holds_trans r2 (holds_context c1_rule201 [4, 9] [5, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r3))) (by central_nf)

theorem c1_rule719 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 4, 7, 6, 7] [-9, 6, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule150 [] [3])) (holds_context c1_rule32 [6, 3, 7, 7, 5] []))
  have l0 := holds_refl [-9, 6, 9, 3, 4, 3]
  have l1 := holds_trans l0 (holds_context c1_rule30 [-9, 6, 9, 3] [])
  have l2 := holds_trans l1 (holds_context c1_rule200 [-9, 6, 9] [4])
  have r0 := holds_refl [6, 3, 7, 7, 5, 3, 5]
  have r1 := holds_trans r0 (holds_context c1_rule32 [6, 3, 7, 7] [5])
  have r2 := holds_trans r1 (holds_context c1_rule34 [6, 3, 7] [5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [6, 3] [7, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule200 [6] [7, 7, 5, 5])
  have r5 := holds_trans r4 (holds_context c1_rule384 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule728 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [-9, 4, 6, 9, 4] [3, 4, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule152 [-9] [])) (holds_context c1_rule17 [] [3, 4, 5, 5]))
  have l0 := holds_refl [-9, 4, 6, 9, 4]
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule751 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 6, 7, 4] [7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule155 [] [3])) (holds_context c1_rule30 [5, 6, 3, 7] []))
  have l0 := holds_refl [3, 7, 5, 4, 4, 3]
  have l1 := holds_trans l0 (holds_context c1_rule201 [3, 7, 5] [3])
  have l2 := holds_trans l1 (holds_context c1_rule32 [3, 7] [])
  have l3 := holds_trans l2 (holds_context c1_rule34 [3] [5])
  have l4 := holds_trans l3 (holds_context c1_rule200 [] [7, 5])
  have r0 := holds_refl [5, 6, 3, 7, 3, 4]
  have r1 := holds_trans r0 (holds_context c1_rule34 [5, 6, 3] [4])
  have r2 := holds_trans r1 (holds_context c1_rule200 [5, 6] [7, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule764 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [4, 6, 5, 5] [3, -7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule156 [-7] [])) (holds_context c1_rule82 [] [4, 4]))
  have l0 := holds_refl [-7, 3, -5, 7, 5, 4]
  have l1 := holds_trans l0 (holds_context c1_rule33 [] [-5, 7, 5, 4])
  have l2 := holds_trans l1 (holds_context c1_rule157 [3] [])
  have l3 := holds_trans l2 (holds_context c1_rule208 [3] [5, 5])
  have l4 := holds_trans l3 (holds_context c1_rule375 [3] [])
  have r0 := holds_refl [6, 5, 5, 4, 4, 4]
  have r1 := holds_trans r0 (holds_context c1_rule296 [6] [4, 4])
  have r2 := holds_trans r1 (holds_context c1_rule35 [] [5, 5, 4, 4])
  have r3 := holds_trans r2 (holds_context c1_rule296 [4, 6] [4])
  have r4 := holds_trans r3 (holds_context c1_rule35 [4] [5, 5, 4])
  have r5 := holds_trans r4 (holds_context c1_rule201 [] [6, 5, 5, 4])
  have r6 := holds_trans r5 (holds_context c1_rule296 [6] [])
  have r7 := holds_trans r6 (holds_context c1_rule35 [] [5, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r7))) (by central_nf)

theorem c1_rule773 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 4, 7, -5, 7, 5] [-9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule158 [-9, 4, 9] [])) (holds_context c1_rule74 [] [-7, -5, 7, 5]))
  have l0 := holds_refl [-9, 4, 9, 3, 4, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c1_rule315 [] [5, 5, 4])
  have l2 := holds_trans l1 (holds_context c1_rule384 [] [4])
  have l3 := holds_trans l2 (holds_context c1_rule719 [] [4])
  have l4 := holds_trans l3 (holds_context c1_rule201 [-9, 6, 9] [])
  have r0 := holds_refl [3, 4, 7, 7, -7, -5, 7, 5]
  have r1 := holds_trans r0 (holds_context c1_rule12 [3, 4, 7] [-5, 7, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule778 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [5, 6, -7, -5] [3, 5, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule159 [] [-7])) (holds_context c1_rule12 [5, 6, -7, -5] []))
  have l0 := holds_refl [3, -5, 4, 4, -5, -7]
  have l1 := holds_trans l0 (holds_context c1_rule201 [3, -5] [-5, -7])
  have l2 := holds_trans l1 (holds_context c1_rule27 [3] [-7])
  have r0 := holds_refl [5, 6, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule789 : Holds (normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, -5, -7, 5] [3, 4, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule160 [] [5])) (holds_context c1_rule9 [3, 4, -7, 6] []))
  have l0 := holds_refl [3, 4, 4, -5, -7, 5]
  have l1 := holds_trans l0 (holds_context c1_rule201 [3] [-5, -7, 5])
  have r0 := holds_refl [3, 4, -7, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule804 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7, 5] [3, -7, 6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule161 [] [3])) (holds_context c1_rule32 [3, 4, -5, -7] []))
  have l0 := holds_refl [3, -7, 6, 3]
  have r0 := holds_refl [3, 4, -5, -7, 3, 5]
  have r1 := holds_trans r0 (holds_context c1_rule33 [3, 4, -5] [5])
  have r2 := holds_trans r1 (holds_context c1_rule31 [3, 4] [-7, 5])
  have r3 := holds_trans r2 (holds_context c1_rule30 [3] [-5, -7, 5])
  have r4 := holds_trans r3 (holds_context c1_rule200 [] [4, -5, -7, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule806 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ)) [6, 3] [3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule161 [7] [])) (holds_context c1_rule34 [] [4, -5, -7, 5]))
  have l0 := holds_refl [7, 3, -7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule34 [] [-7, 6])
  have l2 := holds_trans l1 (holds_context c1_rule12 [3] [6])
  have r0 := holds_refl [3, 7, 4, -5, -7, 5]
  have r1 := holds_trans r0 (holds_context c1_rule804 [3, 7] [])
  have r2 := holds_trans r1 (holds_context c1_rule34 [3] [-7, 6, 3])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [7, -7, 6, 3])
  have r4 := holds_trans r3 (holds_context c1_rule12 [] [6, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule813 : Holds ((normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s3_s5) [4, -5, -7, -5, 4, -7] [3, 7, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule161 [] [6, -7, 6])) (holds_context c1_rule84 [3, 4, -5, -7] []))
  have l0 := holds_refl [3, -7, 6, 6, -7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule202 [3, -7] [-7, 6])
  have l2 := holds_trans l1 (holds_context c1_rule28 [3] [6])
  have r0 := holds_refl [3, 4, -5, -7, 3, -5, 4, -7]
  have r1 := holds_trans r0 (holds_context c1_rule33 [3, 4, -5] [-5, 4, -7])
  have r2 := holds_trans r1 (holds_context c1_rule31 [3, 4] [-7, -5, 4, -7])
  have r3 := holds_trans r2 (holds_context c1_rule30 [3] [-5, -7, -5, 4, -7])
  have r4 := holds_trans r3 (holds_context c1_rule200 [] [4, -5, -7, -5, 4, -7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule923 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [8, 9, 7, -9] [7, 4, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule177 [7] [])) (holds_context c1_rule34 [] [2, 9, 3, 2, -9]))
  have l0 := holds_refl [7, 4, 5, 5, 5, 7]
  have l1 := holds_trans l0 (holds_context c1_rule205 [7, 4] [7])
  have r0 := holds_refl [3, 7, 2, 9, 3, 2, -9]
  have r1 := holds_trans r0 (holds_context c1_rule91 [] [3, 2, -9])
  have r2 := holds_trans r1 (holds_context c1_rule32 [2, 3, 4] [2, -9])
  have r3 := holds_trans r2 (holds_context c1_rule30 [2, 3] [5, 2, -9])
  have r4 := holds_trans r3 (holds_context c1_rule200 [2] [4, 5, 2, -9])
  have r5 := holds_trans r4 (holds_context c1_rule230 [] [-9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule939 : Holds ((normalizedRelatorError .i_r8) ^ (5 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 5, -9, 3] [3, -7, -9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule180 [3, 2, 3, 4] [])) (holds_context c1_rule101 [] [7, 2, -9, 3]))
  have l0 := holds_refl [3, 2, 3, 4, 2, 3, 7, 7, 9]
  have l1 := holds_trans l0 (holds_context c1_rule42 [3, 2, 3] [3, 7, 7, 9])
  have l2 := holds_trans l1 (holds_context c1_rule531 [3] [7, 7, 9])
  have l3 := holds_trans l2 (holds_context c1_rule13 [3, 9, 7, 9] [7, 9])
  have l4 := holds_trans l3 (holds_context c1_rule234 [3] [9])
  have l5 := holds_trans l4 (holds_context c1_rule220 [3, 2] [])
  have l6 := holds_trans l5 (holds_context c1_rule49 [3] [-7])
  have r0 := holds_refl [7, 2, 9, 7, 2, -9, 3]
  have r1 := holds_trans r0 (holds_context c1_rule47 [7] [2, -9, 3])
  have r2 := holds_trans r1 (holds_context c1_rule199 [7, 5] [-9, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule1033 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 7, 5, 5] [5, 5, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule192 [] [7, 7])) (holds_context c1_rule187 [7, 7] []))
  have l0 := holds_refl [3, 3, 4, 5, 5, 4, 7, 7]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [4, 5, 5, 4, 7, 7])
  have l2 := holds_trans l1 (holds_context c1_rule296 [4] [7, 7])
  have l3 := holds_trans l2 (holds_context c1_rule201 [] [5, 5, 7, 7])
  have r0 := holds_refl [7, 7, 3, 3, 4, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule34 [7] [3, 4, 4, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule34 [] [7, 3, 4, 4, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [3, 7] [4, 4, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule34 [3] [7, 4, 4, 5, 5])
  have r5 := holds_trans r4 (holds_context c1_rule200 [] [7, 7, 4, 4, 5, 5])
  have r6 := holds_trans r5 (holds_context c1_rule201 [7, 7] [5, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r6))) (by central_nf)

theorem c1_rule1047 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ)) [3, 5, 5, 7, 7] [-9, 3, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule195 [] [9])) (holds_context c1_rule17 [3, 5, 5, 7, 7] []))
  have l0 := holds_refl [3, 3, 4, 4, -9, 3, 9]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [4, 4, -9, 3, 9])
  have l2 := holds_trans l1 (holds_context c1_rule201 [] [-9, 3, 9])
  have r0 := holds_refl [3, 5, 5, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule1050 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ)) [3, -5, 7, 7, -9] [5, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule195 [5] [])) (holds_context c1_rule32 [] [5, 5, 7, 7, -9]))
  have l0 := holds_refl [5, 3, 3, 4, 4, -9, 3]
  have l1 := holds_trans l0 (holds_context c1_rule32 [] [3, 4, 4, -9, 3])
  have l2 := holds_trans l1 (holds_context c1_rule32 [3] [4, 4, -9, 3])
  have l3 := holds_trans l2 (holds_context c1_rule200 [] [5, 4, 4, -9, 3])
  have l4 := holds_trans l3 (holds_context c1_rule201 [5] [-9, 3])
  have r0 := holds_refl [3, 5, 5, 5, 7, 7, -9]
  have r1 := holds_trans r0 (holds_context c1_rule205 [3] [7, 7, -9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule1074 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 7, 2] [9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule199 [] [9, 5])) (holds_context c1_rule52 [2] []))
  have l0 := holds_refl [9, 5]
  have r0 := holds_refl [2, 7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule1078 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7) [2, 3, -7, 5, 4] [-9, 3, 2, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule199 [] [-9, 3, 2, 9])) (holds_context c1_rule182 [2] []))
  have l0 := holds_refl [-9, 3, 2, 9]
  have r0 := holds_refl [2, 3, -7, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule1083 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4) [3, -9, 6, 9, 6] [4, -9, 3, 9] := by
  have h0 := c1_rule196
  have l0 := holds_refl [3, 3, 4, -9, 3, 9]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [4, -9, 3, 9])
  have r0 := holds_refl [3, -9, 6, 9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule1096 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [4, 5, 5, 7, 7] [-9, 6, 9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule200 [] [4, 5, 5, 7, 7])) (holds_context c1_rule141 [3] []))
  have l0 := holds_refl [4, 5, 5, 7, 7]
  have r0 := holds_refl [3, 3, -9, 6, 9, 6]
  have r1 := holds_trans r0 (holds_context c1_rule200 [] [-9, 6, 9, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule1108 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [3, 4, 7, 7, 6] [-9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule201 [] [-9, 4, 9])) (holds_context c1_rule75 [4] []))
  have l0 := holds_refl [-9, 4, 9]
  have r0 := holds_refl [4, 3, 7, 7, 6]
  have r1 := holds_trans r0 (holds_context c1_rule30 [] [7, 7, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule1109 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 7, 5, 4] [3, 5, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule201 [5, 6, 3, 7] [])) (holds_context c1_rule155 [] [4]))
  have l0 := holds_refl [5, 6, 3, 7]
  have l1 := holds_trans l0 (holds_context c1_rule806 [5] [7])
  have l2 := holds_trans l1 (holds_context c1_rule32 [] [6, 7])
  have r0 := holds_refl [3, 7, 5, 4, 4, 4]
  have r1 := holds_trans r0 (holds_context c1_rule201 [3, 7, 5] [4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule1117 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [4, 8, 5] [3, 8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule203 [] [3, 8, -5])) (holds_context c1_rule64 [8] []))
  have l0 := holds_refl [3, 8, -5]
  have r0 := holds_refl [8, 3, 3, 4, 5]
  have r1 := holds_trans r0 (holds_context c1_rule200 [8] [4, 5])
  have r2 := holds_trans r1 (holds_context c1_rule36 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule1153 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ)) [6, 7, 7, 6] [4, 7, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule208 [-9, 4, 9] [])) (holds_context c1_rule74 [] [3, 4]))
  have l0 := holds_refl [-9, 4, 9, 4, 6, 3]
  have l1 := holds_trans l0 (holds_context c1_rule71 [] [6, 3])
  have l2 := holds_trans l1 (holds_context c1_rule806 [] [7, 7, 6, 3])
  have l3 := holds_trans l2 (holds_context c1_rule806 [3, 6, 7, 7] [])
  have l4 := holds_trans l3 (holds_context c1_rule34 [3, 6, 7] [6])
  have l5 := holds_trans l4 (holds_context c1_rule34 [3, 6] [7, 6])
  have l6 := holds_trans l5 (holds_context c1_rule806 [3] [7, 7, 6])
  have l7 := holds_trans l6 (holds_context c1_rule200 [] [6, 7, 7, 6])
  have r0 := holds_refl [3, 4, 7, 7, 3, 4]
  have r1 := holds_trans r0 (holds_context c1_rule34 [3, 4, 7] [4])
  have r2 := holds_trans r1 (holds_context c1_rule34 [3, 4] [7, 4])
  have r3 := holds_trans r2 (holds_context c1_rule30 [3] [7, 7, 4])
  have r4 := holds_trans r3 (holds_context c1_rule200 [] [4, 7, 7, 4])
  exact holds_factor (holds_trans (holds_symm l7) (holds_trans h0 r4)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
