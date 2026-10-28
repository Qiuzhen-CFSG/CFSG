module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step05

/-! Kernel-checked central word identities, chunk 6.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c1_rule2762 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (7 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [4, -7, 6, -7] [4, 7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule396 [] [3])) (holds_context c1_rule34 [5, 5, 6, 7] []))
  have l0 := holds_refl [3, 4, -7, 6, -7, 3]
  have l1 := holds_trans l0 (holds_context c1_rule1974 [] [3])
  have l2 := holds_trans l1 (holds_context c1_rule2516 [] [4, 3])
  have l3 := holds_trans l2 (holds_context c1_rule30 [9, 6, -9] [])
  have l4 := holds_trans l3 (holds_context c1_rule2552 [] [4])
  have l5 := holds_trans l4 (holds_context c1_rule2631 [] [])
  have r0 := holds_refl [5, 5, 6, 7, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule2761 [] [3, 7])
  have r2 := holds_trans r1 (holds_context c1_rule806 [3, 4, 7] [7])
  have r3 := holds_trans r2 (holds_context c1_rule34 [3, 4] [6, 7])
  have r4 := holds_trans r3 (holds_context c1_rule30 [3] [7, 6, 7])
  have r5 := holds_trans r4 (holds_context c1_rule200 [] [4, 7, 6, 7])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r5)) (by central_nf)

theorem c1_rule2798 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (15 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (18 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [4, 6, 7, 6] [3, 5, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule397 [6, 7, 7] [])) (holds_context c1_rule384 [] [6, 3, -7]))
  have l0 := holds_refl [6, 7, 7, 3, 4, -7, 6, 3]
  have l1 := holds_trans l0 (holds_context c1_rule34 [6, 7] [4, -7, 6, 3])
  have l2 := holds_trans l1 (holds_context c1_rule34 [6] [7, 4, -7, 6, 3])
  have l3 := holds_trans l2 (holds_context c1_rule806 [] [7, 7, 4, -7, 6, 3])
  have l4 := holds_trans l3 (holds_context c1_rule2181 [3, 6] [-7, 6, 3])
  have l5 := holds_trans l4 (holds_context c1_rule35 [3] [7, 7, -7, 6, 3])
  have l6 := holds_trans l5 (holds_context c1_rule2664 [] [-7, 6, 3])
  have l7 := holds_trans l6 (holds_context c1_rule2165 [] [6, 3])
  have l8 := holds_trans l7 (holds_context c1_rule2511 [] [3])
  have l9 := holds_trans l8 (holds_context c1_rule34 [5, 5] [])
  have l10 := holds_trans l9 (holds_context c1_rule32 [5] [7])
  have l11 := holds_trans l10 (holds_context c1_rule32 [] [5, 7])
  have r0 := holds_refl [3, 4, 7, 6, 7, 6, 3, -7]
  have r1 := holds_trans r0 (holds_context c1_rule719 [] [6, 3, -7])
  have r2 := holds_trans r1 (holds_context c1_rule2516 [] [4, 6, 3, -7])
  have r3 := holds_trans r2 (holds_context c1_rule806 [9, 6, -9, 4] [-7])
  have r4 := holds_trans r3 (holds_context c1_rule30 [9, 6, -9] [6, -7])
  have r5 := holds_trans r4 (holds_context c1_rule2552 [] [4, 6, -7])
  have r6 := holds_trans r5 (holds_context c1_rule2631 [] [6, -7])
  have r7 := holds_trans r6 (holds_context c1_rule2762 [] [6, -7])
  have r8 := holds_trans r7 (holds_context c1_rule2171 [4] [-7])
  have r9 := holds_trans r8 (holds_context c1_rule201 [] [-9, 3, 9, -7])
  have r10 := holds_trans r9 (holds_context c1_rule2502 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l11) (holds_trans h0 r10))) (by central_nf)

theorem c1_rule2824 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-7, 5, 5, -7] [7, 5, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule400 [7, 7] [])) (holds_context c1_rule206 [] [4, 6, 3, -7, 6]))
  have l0 := holds_refl [7, 7, 6, 3, 7, 4, 6, -7]
  have l1 := holds_trans l0 (holds_context c1_rule806 [7, 7] [7, 4, 6, -7])
  have l2 := holds_trans l1 (holds_context c1_rule34 [7] [6, 7, 4, 6, -7])
  have l3 := holds_trans l2 (holds_context c1_rule34 [] [7, 6, 7, 4, 6, -7])
  have l4 := holds_trans l3 (holds_context c1_rule2141 [] [7, 4, 6, -7])
  have l5 := holds_trans l4 (holds_context c1_rule206 [3, 6] [4, 6, -7])
  have l6 := holds_trans l5 (holds_context c1_rule2488 [] [-7])
  have r0 := holds_refl [-7, 4, 6, 3, -7, 6]
  have r1 := holds_trans r0 (holds_context c1_rule806 [-7, 4] [-7, 6])
  have r2 := holds_trans r1 (holds_context c1_rule30 [-7] [6, -7, 6])
  have r3 := holds_trans r2 (holds_context c1_rule33 [] [4, 6, -7, 6])
  have r4 := holds_trans r3 (holds_context c1_rule2026 [3] [6])
  have r5 := holds_trans r4 (holds_context c1_rule2798 [3, 7] [])
  have r6 := holds_trans r5 (holds_context c1_rule34 [3] [5, 5, 7])
  have r7 := holds_trans r6 (holds_context c1_rule200 [] [7, 5, 5, 7])
  exact holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r7)) (by central_nf)

theorem c1_rule2998 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 5, 7, 5] [4, 6, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule424 [] [3, 2, -9, -7])) (holds_context c1_rule176 [3, 4, 7] []))
  have l0 := holds_refl [2, 3, 8, 3, -5, 3, 2, -9, -7]
  have l1 := holds_trans l0 (holds_context c1_rule31 [2, 3, 8, 3] [2, -9, -7])
  have l2 := holds_trans l1 (holds_context c1_rule200 [2, 3, 8] [-5, 2, -9, -7])
  have l3 := holds_trans l2 (holds_context c1_rule1362 [] [-9, -7])
  have l4 := holds_trans l3 (holds_context c1_rule923 [4] [-7])
  have l5 := holds_trans l4 (holds_context c1_rule2311 [4] [7, -7])
  have l6 := holds_trans l5 (holds_context c1_rule12 [4, 6, -5, 7] [])
  have r0 := holds_refl [3, 4, 7, 3, 4, 5, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule34 [3, 4] [4, 5, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule30 [3] [7, 4, 5, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [4, 7, 4, 5, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule1737 [4] [5])
  have r5 := holds_trans r4 (holds_context c1_rule30 [] [6, 7, 6, 5])
  have r6 := holds_trans r5 (holds_context c1_rule2798 [3] [5])
  have r7 := holds_trans r6 (holds_context c1_rule200 [] [5, 5, 7, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r7))) (by central_nf)

theorem c1_rule3087 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-9, 3, 7] [5, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule429 [-5, 7] [])) (holds_context c1_rule243 [] [3, 4, 5, 2]))
  have l0 := holds_refl [-5, 7, 3, 7, -9]
  have l1 := holds_trans l0 (holds_context c1_rule34 [-5] [7, -9])
  have l2 := holds_trans l1 (holds_context c1_rule31 [] [7, 7, -9])
  have l3 := holds_trans l2 (holds_context c1_rule1050 [] [])
  have r0 := holds_refl [2, -7, 5, 3, 4, 5, 2]
  have r1 := holds_trans r0 (holds_context c1_rule32 [2, -7] [4, 5, 2])
  have r2 := holds_trans r1 (holds_context c1_rule33 [2] [5, 4, 5, 2])
  have r3 := holds_trans r2 (holds_context c1_rule1078 [] [5, 2])
  have r4 := holds_trans r3 (holds_context c1_rule52 [-9, 3] [2])
  have r5 := holds_trans r4 (holds_context c1_rule199 [-9, 3, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule3275 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [4, -5, 4] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule441 [] [3, 7, 7, 2])) (holds_context c1_rule92 [3, 4, 5] []))
  have l0 := holds_refl [2, 3, 7, -9, 3, 7, 7, 2]
  have l1 := holds_trans l0 (holds_context c1_rule3087 [2, 3, 7] [7, 2])
  have l2 := holds_trans l1 (holds_context c1_rule939 [2, 3] [7, 2])
  have l3 := holds_trans l2 (holds_context c1_rule200 [2] [-7, -9, -7, 7, 2])
  have l4 := holds_trans l3 (holds_context c1_rule54 [] [-7, 7, 2])
  have l5 := holds_trans l4 (holds_context c1_rule13 [-5, 2] [2])
  have l6 := holds_trans l5 (holds_context c1_rule199 [-5] [])
  have r0 := holds_refl [3, 4, 5, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule32 [3, 4] [4, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule30 [3] [5, 4, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [4, 5, 4, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule560 [4] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule3280 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 5, -9, -7] [] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule441 [] [9, 3, 2, -9, -7])) (holds_context c1_rule176 [3, 4, 5] []))
  have l0 := holds_refl [2, 3, 7, -9, 9, 3, 2, -9, -7]
  have l1 := holds_trans l0 (holds_context c1_rule17 [2, 3, 7] [3, 2, -9, -7])
  have l2 := holds_trans l1 (holds_context c1_rule34 [2, 3] [2, -9, -7])
  have l3 := holds_trans l2 (holds_context c1_rule200 [2] [7, 2, -9, -7])
  have l4 := holds_trans l3 (holds_context c1_rule1074 [] [-9, -7])
  have r0 := holds_refl [3, 4, 5, 3, 4, 5, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule32 [3, 4] [4, 5, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule30 [3] [5, 4, 5, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [4, 5, 4, 5, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule560 [4] [5])
  have r5 := holds_trans r4 (holds_context c1_rule3275 [] [5])
  have r6 := holds_trans r5 (holds_context c1_rule9 [] [])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r6)) (by central_nf)

theorem c1_rule3591 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, -5, 4] [3, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule458 [] [2, -9, -7, -5])) (holds_context c1_rule165 [5, 2, 9] []))
  have l0 := holds_refl [3, 2, 8, 7, 2, -9, -7, -5]
  have l1 := holds_trans l0 (holds_context c1_rule1438 [3] [-9, -7, -5])
  have l2 := holds_trans l1 (holds_context c1_rule3280 [3, 4] [-5])
  have r0 := holds_refl [5, 2, 9, 2, 4, 6, 9, 4]
  have r1 := holds_trans r0 (holds_context c1_rule45 [5, 2] [4, 6, 9, 4])
  have r2 := holds_trans r1 (holds_context c1_rule199 [5] [-9, 4, 6, 9, 4])
  have r3 := holds_trans r2 (holds_context c1_rule728 [5] [])
  have r4 := holds_trans r3 (holds_context c1_rule32 [] [4, 5, 5])
  have r5 := holds_trans r4 (holds_context c1_rule560 [3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r5))) (by central_nf)

theorem equation_r1_1698 : (normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule279 [] [2, -7])) (holds_context c1_rule55 [3, 5, 4, 5] []))
  have l0 := holds_refl [3, -5, 4, 2, -7]
  have l1 := holds_trans l0 (holds_context c1_rule42 [3, -5] [-7])
  have l2 := holds_trans l1 (holds_context c1_rule105 [] [-7])
  have l3 := holds_trans l2 (holds_context c1_rule28 [2, 9, 3] [])
  have l4 := holds_trans l3 (holds_context c1_rule213 [] [7])
  have r0 := holds_refl [3, 5, 4, 5, 2, 9]
  have r1 := holds_trans r0 (holds_context c1_rule107 [3, 5] [])
  have r2 := holds_trans r1 (holds_context c1_rule32 [3] [2, 3, 7])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [5, 2, 3, 7])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 2, 3, 7] [5, 2, 3, 7] := holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r1_296 : (normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .i_s7) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule123 [3, 10] [])) (holds_context c1_rule112 [] [10, 3]))
  have l0 := holds_refl [3, 10, 3, 4, 5, 5, 10]
  have l1 := holds_trans l0 (holds_context c1_rule129 [] [10])
  have r0 := holds_refl [10, 3, 4, 5, 5, 10, 3]
  have r1 := holds_trans r0 (holds_context c1_rule117 [10] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .i_s7) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [10, 3, 9, 9, 3, 10] [10, 3, 9, 9, 3, 10] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)
  exact holds_cancel hh

theorem equation_r1_5242 : (normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule436 [] [6])) (holds_context c1_rule266 [9, 8, -9] []))
  have l0 := holds_refl [-7, 6, 7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule79 [] [])
  have r0 := holds_refl [9, 8, -9, 6, 8]
  have r1 := holds_trans r0 (holds_context c1_rule434 [] [8])
  have r2 := holds_trans r1 (holds_context c1_rule287 [3] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ)) [3, 4, 5, 5] [3, 4, 5, 5] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r1_5927 : (normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (9 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule464 [] [-5, 4, -7, 6])) (holds_context c1_rule394 [3, -7, -5, 2, 8] []))
  have l0 := holds_refl [2, -5, -7, -5, 4, -7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule2711 [2, -5, -7] [])
  have l2 := holds_trans l1 (holds_context c1_rule2824 [2, -5] [5])
  have l3 := holds_trans l2 (holds_context c1_rule2998 [2, -5, 7] [])
  have l4 := holds_trans l3 (holds_context c1_rule2417 [2, -5] [7])
  have l5 := holds_trans l4 (holds_context c1_rule31 [2] [4, 5, 7, 7])
  have l6 := holds_trans l5 (holds_context c1_rule3591 [2] [5, 7, 7])
  have l7 := holds_trans l6 (holds_context c1_rule9 [2, 3, 4] [7, 7])
  have l8 := holds_trans l7 (holds_context c1_rule1170 [] [])
  have r0 := holds_refl [3, -7, -5, 2, 8, 5, 6, -7]
  have r1 := holds_trans r0 (holds_context c1_rule524 [] [5, 6, -7])
  have r2 := holds_trans r1 (holds_context c1_rule789 [2] [6, -7])
  have r3 := holds_trans r2 (holds_context c1_rule202 [2, 3, 4, -7] [-7])
  have r4 := holds_trans r3 (holds_context c1_rule28 [2, 3, 4] [])
  have r5 := holds_trans r4 (holds_context c1_rule1170 [] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (9 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [3, 8, 3, 2] [3, 8, 3, 2] := holds_factor (holds_trans (holds_symm l8) (holds_trans h0 r5)) (by central_nf)
  exact holds_cancel hh

theorem c2_rule2 : Holds ((1 : C)) [2, -2] [] := by
  have h0 := (show Holds 1 [2, -2] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [2, -2]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule4 : Holds ((1 : C)) [3, -3] [] := by
  have h0 := (show Holds 1 [3, -3] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [3, -3]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule6 : Holds ((1 : C)) [4, -4] [] := by
  have h0 := (show Holds 1 [4, -4] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [4, -4]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule8 : Holds ((1 : C)) [5, -5] [] := by
  have h0 := (show Holds 1 [5, -5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [5, -5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule9 : Holds ((1 : C)) [-5, 5] [] := by
  have h0 := (show Holds 1 [-5, 5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-5, 5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule10 : Holds ((1 : C)) [6, -6] [] := by
  have h0 := (show Holds 1 [6, -6] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [6, -6]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule12 : Holds ((1 : C)) [7, -7] [] := by
  have h0 := (show Holds 1 [7, -7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [7, -7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule13 : Holds ((1 : C)) [-7, 7] [] := by
  have h0 := (show Holds 1 [-7, 7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-7, 7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule14 : Holds ((1 : C)) [8, -8] [] := by
  have h0 := (show Holds 1 [8, -8] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [8, -8]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule16 : Holds ((1 : C)) [9, -9] [] := by
  have h0 := (show Holds 1 [9, -9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [9, -9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule17 : Holds ((1 : C)) [-9, 9] [] := by
  have h0 := (show Holds 1 [-9, 9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-9, 9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule21 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ)) [-2] [2] := by
  have h0 := (split [2] [2] (rotate [] [2, 2] source1))
  have l0 := holds_refl [2]
  have r0 := holds_refl [-2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule22 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule23 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule24 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ)) [-6] [6] := by
  have h0 := (split [6] [6] (rotate [] [6, 6] source4))
  have l0 := holds_refl [6]
  have r0 := holds_refl [-6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule25 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule26 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ)) [-10] [10] := by
  have h0 := (split [10] [10] (rotate [] [10, 10] source6))
  have l0 := holds_refl [10]
  have r0 := holds_refl [-10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule27 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ)) [-5, -5] [5, 5] := by
  have h0 := (split [5, 5] [5, 5] (rotate [] [5, 5, 5, 5] source7))
  have l0 := holds_refl [5, 5]
  have r0 := holds_refl [-5, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule28 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ)) [-7, -7] [7, 7] := by
  have h0 := (split [7, 7] [7, 7] (rotate [] [7, 7, 7, 7] source8))
  have l0 := holds_refl [7, 7]
  have r0 := holds_refl [-7, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule30 : Holds (normalizedRelatorError .ii_s1_s2) [3, 4] [4, 3] := by
  have h0 := (split [-3, -4] [3, 4] (rotate [] [-3, -4, 3, 4] source10))
  have l0 := holds_refl [-3, -4]
  have l1 := holds_trans l0 (holds_context c2_rule22 [] [-4])
  have l2 := holds_trans l1 (holds_context c2_rule23 [3] [])
  have r0 := holds_refl [-4, -3]
  have r1 := holds_trans r0 (holds_context c2_rule23 [] [-3])
  have r2 := holds_trans r1 (holds_context c2_rule22 [4] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c2_rule31 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [-5, 3] [3, -5] := by
  have h0 := (split [-3, -5] [3, 5] (rotate [] [-3, -5, 3, 5] source11))
  have l0 := holds_refl [-3, -5]
  have l1 := holds_trans l0 (holds_context c2_rule22 [] [-5])
  have r0 := holds_refl [-5, -3]
  have r1 := holds_trans r0 (holds_context c2_rule22 [-5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule32 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [5, 3] [3, 5] := by
  have h0 := (split [3, 5] [-3, -5] (rotate [-3, -5] [3, 5] source11))
  have l0 := holds_refl [3, 5]
  have r0 := holds_refl [5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule33 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 3] [3, -7] := by
  have h0 := (split [-3, -7] [3, 7] (rotate [] [-3, -7, 3, 7] source12))
  have l0 := holds_refl [-3, -7]
  have l1 := holds_trans l0 (holds_context c2_rule22 [] [-7])
  have r0 := holds_refl [-7, -3]
  have r1 := holds_trans r0 (holds_context c2_rule22 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule34 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, 3] [3, 7] := by
  have h0 := (split [3, 7] [-3, -7] (rotate [-3, -7] [3, 7] source12))
  have l0 := holds_refl [3, 7]
  have r0 := holds_refl [7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule35 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [6, 4] [4, 6] := by
  have h0 := (split [-4, -6] [4, 6] (rotate [] [-4, -6, 4, 6] source16))
  have l0 := holds_refl [-4, -6]
  have l1 := holds_trans l0 (holds_context c2_rule23 [] [-6])
  have l2 := holds_trans l1 (holds_context c2_rule24 [4] [])
  have r0 := holds_refl [-6, -4]
  have r1 := holds_trans r0 (holds_context c2_rule24 [] [-4])
  have r2 := holds_trans r1 (holds_context c2_rule23 [6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c2_rule36 : Holds ((normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 4] [4, 8] := by
  have h0 := (split [-4, -8] [4, 8] (rotate [] [-4, -8, 4, 8] source17))
  have l0 := holds_refl [-4, -8]
  have l1 := holds_trans l0 (holds_context c2_rule23 [] [-8])
  have l2 := holds_trans l1 (holds_context c2_rule25 [4] [])
  have r0 := holds_refl [-8, -4]
  have r1 := holds_trans r0 (holds_context c2_rule25 [] [-4])
  have r2 := holds_trans r1 (holds_context c2_rule23 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c2_rule41 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ)) [8, 2] [2, 4] := by
  have h0 := (split [2, 4] [2, -8] (rotate [] [2, 4, 2, -8] source31))
  have l0 := holds_refl [2, 4]
  have r0 := holds_refl [8, -2]
  have r1 := holds_trans r0 (holds_context c2_rule21 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule42 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2) [4, 2] [2, 8] := by
  have h0 := (split [4, 2] [-8, 2] (rotate [2] [4, 2, -8] source31))
  have l0 := holds_refl [4, 2]
  have r0 := holds_refl [-2, 8]
  have r1 := holds_trans r0 (holds_context c2_rule21 [] [8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
