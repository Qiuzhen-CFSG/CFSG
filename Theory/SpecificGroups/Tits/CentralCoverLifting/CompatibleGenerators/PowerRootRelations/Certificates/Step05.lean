module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step04

/-! Kernel-checked central word identities, chunk 5.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c1_rule1170 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, 4, 7, 7] [3, 8, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule209 [] [5, 5, 2])) (holds_context c1_rule108 [8] []))
  have l0 := holds_refl [4, 8, 3, 5, 5, 2]
  have l1 := holds_trans l0 (holds_context c1_rule297 [] [5, 2])
  have l2 := holds_trans l1 (holds_context c1_rule9 [3, 8, 3] [2])
  have r0 := holds_refl [8, 2, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c1_rule41 [] [3, 7, 7])
  have r2 := holds_trans r1 (holds_context c1_rule30 [2] [7, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule1362 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .viii_s3) [2, 3, 8, -5, 2] [4, 8, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule230 [4] [])) (holds_context c1_rule42 [] [4, 5, 2]))
  have l0 := holds_refl [4, 8, 9, 7]
  have r0 := holds_refl [2, 8, 4, 5, 2]
  have r1 := holds_trans r0 (holds_context c1_rule36 [2] [5, 2])
  have r2 := holds_trans r1 (holds_context c1_rule1117 [2] [2])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule1438 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 8, 7, 2] [4, 9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule238 [2] [])) (holds_context c1_rule199 [] [4, 9, 5]))
  have l0 := holds_refl [2, 8, 7, 2]
  have r0 := holds_refl [4, 9, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule1737 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 4, 5, 5] [3, 6, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule281 [] [3])) (holds_context c1_rule67 [3, 7] []))
  have l0 := holds_refl [3, 7, 4, 5, 5, 3]
  have l1 := holds_trans l0 (holds_context c1_rule355 [] [3])
  have l2 := holds_trans l1 (holds_context c1_rule806 [6, 7] [])
  have l3 := holds_trans l2 (holds_context c1_rule34 [6] [6])
  have l4 := holds_trans l3 (holds_context c1_rule806 [] [7, 6])
  have r0 := holds_refl [3, 7, 3, 5, 5, 4]
  have r1 := holds_trans r0 (holds_context c1_rule34 [3] [5, 5, 4])
  have r2 := holds_trans r1 (holds_context c1_rule200 [] [7, 5, 5, 4])
  have r3 := holds_trans r2 (holds_context c1_rule296 [7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r3))) (by central_nf)

theorem c1_rule1923 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [8, 3, 6] [6, 8, 3] := by
  have h0 := c1_rule308
  have l0 := holds_refl [4, 6, 5, 5, 8]
  have l1 := holds_trans l0 (holds_context c1_rule764 [] [8])
  have l2 := holds_trans l1 (holds_context c1_rule522 [3] [])
  have l3 := holds_trans l2 (holds_context c1_rule200 [] [8, 3, 6])
  have r0 := holds_refl [6, 8, 3]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule1941 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 3, 8, 3, 2] [3, 7, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule311 [2, 3] [])) (holds_context c1_rule100 [] [2, 4]))
  have l0 := holds_refl [2, 3, 8, 3, 2]
  have r0 := holds_refl [3, 7, 7, 2, 2, 4]
  have r1 := holds_trans r0 (holds_context c1_rule199 [3, 7, 7] [4])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule1952 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [6, 5, 5] [5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule313 [] [10])) (holds_context c1_rule57 [8, 3] []))
  have l0 := holds_refl [5, 5, 6, 10, 10]
  have l1 := holds_trans l0 (holds_context c1_rule204 [5, 5, 6] [])
  have r0 := holds_refl [8, 3, 4, 6, 8]
  have r1 := holds_trans r0 (holds_context c1_rule209 [] [6, 8])
  have r2 := holds_trans r1 (holds_context c1_rule1923 [4] [8])
  have r3 := holds_trans r2 (holds_context c1_rule287 [4, 6] [])
  have r4 := holds_trans r3 (holds_context c1_rule35 [4] [5, 5])
  have r5 := holds_trans r4 (holds_context c1_rule201 [] [6, 5, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule1974 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [3, 4, -7, 6, -7] [-9, 6, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule315 [] [5, 5])) (holds_context c1_rule152 [-9, 4] []))
  have l0 := holds_refl [6, 7, 7, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule1033 [6] [])
  have l2 := holds_trans l1 (holds_context c1_rule1952 [] [7, 7])
  have l3 := holds_trans l2 (holds_context c1_rule396 [] [])
  have r0 := holds_refl [-9, 4, 4, 6, 9, 4]
  have r1 := holds_trans r0 (holds_context c1_rule201 [-9] [6, 9, 4])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule1978 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 3] [6, 7, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule315 [] [4])) (holds_context c1_rule201 [-9, 4, 9, 3] []))
  have l0 := holds_refl [6, 7, 7, 4]
  have r0 := holds_refl [-9, 4, 9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule1996 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, -7, 6, 7, 2] [3, 6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule317 [] [2])) (holds_context c1_rule199 [6, 3, 7, 7] []))
  have l0 := holds_refl [2, 9, 8, -9, 8, 2]
  have l1 := holds_trans l0 (holds_context c1_rule436 [2] [2])
  have r0 := holds_refl [6, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c1_rule806 [] [7, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule2026 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ)) [-7, 4, 6, -7] [7, 4, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule320 [7, 4, -9] [])) (holds_context c1_rule76 [] [9, 3, 4, -7]))
  have l0 := holds_refl [7, 4, -9, 9, 6, 7]
  have l1 := holds_trans l0 (holds_context c1_rule17 [7, 4] [6, 7])
  have r0 := holds_refl [3, -7, 6, -9, 9, 3, 4, -7]
  have r1 := holds_trans r0 (holds_context c1_rule17 [3, -7, 6] [3, 4, -7])
  have r2 := holds_trans r1 (holds_context c1_rule806 [3, -7] [4, -7])
  have r3 := holds_trans r2 (holds_context c1_rule33 [3] [6, 4, -7])
  have r4 := holds_trans r3 (holds_context c1_rule200 [] [-7, 6, 4, -7])
  have r5 := holds_trans r4 (holds_context c1_rule35 [-7] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule2072 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [6, 7, 6, 7, 4] [4, 7, 6, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule330 [] [5, 5])) (holds_context c1_rule81 [6, 3, 7] []))
  have l0 := holds_refl [3, 4, 7, 7, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule1737 [3, 4, 7] [])
  have l2 := holds_trans l1 (holds_context c1_rule34 [3, 4] [6, 7, 6])
  have l3 := holds_trans l2 (holds_context c1_rule30 [3] [7, 6, 7, 6])
  have l4 := holds_trans l3 (holds_context c1_rule200 [] [4, 7, 6, 7, 6])
  have r0 := holds_refl [6, 3, 7, 6, 3, 7, 4]
  have r1 := holds_trans r0 (holds_context c1_rule806 [] [7, 6, 3, 7, 4])
  have r2 := holds_trans r1 (holds_context c1_rule806 [3, 6, 7] [7, 4])
  have r3 := holds_trans r2 (holds_context c1_rule34 [3, 6] [6, 7, 4])
  have r4 := holds_trans r3 (holds_context c1_rule806 [3] [7, 6, 7, 4])
  have r5 := holds_trans r4 (holds_context c1_rule200 [] [6, 7, 6, 7, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule2098 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ)) [3, 7, 7, 4] [3, 4, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule332 [] [2])) (holds_context c1_rule199 [3, 4, 7, 7] []))
  have l0 := holds_refl [2, 9, 8, -9, 6, 2]
  have l1 := holds_trans l0 (holds_context c1_rule434 [2] [2])
  have l2 := holds_trans l1 (holds_context c1_rule1941 [] [])
  have r0 := holds_refl [3, 4, 7, 7]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule2141 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [3, 7, 7, 6] [3, 6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule337 [] [2])) (holds_context c1_rule43 [3, 7, 7, 2] []))
  have l0 := holds_refl [2, 8, 9, 8, -9, 2]
  have l1 := holds_trans l0 (holds_context c1_rule504 [] [2])
  have l2 := holds_trans l1 (holds_context c1_rule1996 [] [])
  have r0 := holds_refl [3, 7, 7, 2, 2, 6]
  have r1 := holds_trans r0 (holds_context c1_rule199 [3, 7, 7] [6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule2143 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, 9, 8, -9] [-7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule337 [2] [])) (holds_context c1_rule92 [] [6]))
  have l0 := holds_refl [2, 2, 8, 9, 8, -9]
  have l1 := holds_trans l0 (holds_context c1_rule199 [] [8, 9, 8, -9])
  have r0 := holds_refl [3, 4, 5, 5, 6]
  have r1 := holds_trans r0 (holds_context c1_rule86 [3] [])
  have r2 := holds_trans r1 (holds_context c1_rule200 [] [-7, 6, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c1_rule2144 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [3, 7, 6, 7] [9, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule337 [3, 7, 7, 2] [])) (holds_context c1_rule103 [] [7, 7, 2, 6]))
  have l0 := holds_refl [3, 7, 7, 2, 2, 8, 9, 8, -9]
  have l1 := holds_trans l0 (holds_context c1_rule199 [3, 7, 7] [8, 9, 8, -9])
  have l2 := holds_trans l1 (holds_context c1_rule2143 [3, 7, 7] [])
  have l3 := holds_trans l2 (holds_context c1_rule12 [3, 7] [6, 7])
  have r0 := holds_refl [2, 5, 5, 4, 7, 7, 2, 6]
  have r1 := holds_trans r0 (holds_context c1_rule296 [2] [7, 7, 2, 6])
  have r2 := holds_trans r1 (holds_context c1_rule1096 [2] [2, 6])
  have r3 := holds_trans r2 (holds_context c1_rule43 [2, -9, 6, 9] [6])
  have r4 := holds_trans r3 (holds_context c1_rule45 [2, -9, 6] [6, 6])
  have r5 := holds_trans r4 (holds_context c1_rule43 [2, -9] [-9, 6, 6])
  have r6 := holds_trans r5 (holds_context c1_rule44 [2] [6, -9, 6, 6])
  have r7 := holds_trans r6 (holds_context c1_rule199 [] [9, 6, -9, 6, 6])
  have r8 := holds_trans r7 (holds_context c1_rule202 [9, 6, -9] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r8)) (by central_nf)

theorem c1_rule2165 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, -7] [3, 4, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule340 [] [-7])) (holds_context c1_rule12 [4, 6, 3, 7] []))
  have l0 := holds_refl [3, 7, 7, 4, 6, -7]
  have l1 := holds_trans l0 (holds_context c1_rule2098 [] [6, -7])
  have l2 := holds_trans l1 (holds_context c1_rule1108 [] [-7])
  have r0 := holds_refl [4, 6, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule806 [4] [7])
  have r2 := holds_trans r1 (holds_context c1_rule30 [] [6, 7])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c1_rule2166 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s4) [6, 7, 7, 4] [4, 6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule340 [] [3])) (holds_context c1_rule34 [4, 6, 3, 7] []))
  have l0 := holds_refl [3, 7, 7, 4, 6, 3]
  have l1 := holds_trans l0 (holds_context c1_rule2098 [] [6, 3])
  have l2 := holds_trans l1 (holds_context c1_rule1108 [] [3])
  have l3 := holds_trans l2 (holds_context c1_rule1978 [] [])
  have r0 := holds_refl [4, 6, 3, 7, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule806 [4] [7, 3, 7])
  have r2 := holds_trans r1 (holds_context c1_rule30 [] [6, 7, 3, 7])
  have r3 := holds_trans r2 (holds_context c1_rule34 [3, 4, 6] [7])
  have r4 := holds_trans r3 (holds_context c1_rule806 [3, 4] [7, 7])
  have r5 := holds_trans r4 (holds_context c1_rule30 [3] [6, 7, 7])
  have r6 := holds_trans r5 (holds_context c1_rule200 [] [4, 6, 7, 7])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r6)) (by central_nf)

theorem c1_rule2171 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 6, 7, 6] [4, -9, 3, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule340 [] [6, 5, 5])) (holds_context c1_rule81 [4, 6, 3, 7] []))
  have l0 := holds_refl [3, 7, 7, 4, 6, 6, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule2098 [] [6, 6, 5, 5])
  have l2 := holds_trans l1 (holds_context c1_rule1108 [] [6, 5, 5])
  have l3 := holds_trans l2 (holds_context c1_rule74 [] [5, 5])
  have l4 := holds_trans l3 (holds_context c1_rule1033 [3, 4] [])
  have l5 := holds_trans l4 (holds_context c1_rule1096 [3] [])
  have l6 := holds_trans l5 (holds_context c1_rule1083 [] [])
  have r0 := holds_refl [4, 6, 3, 7, 6, 3, 7, 4]
  have r1 := holds_trans r0 (holds_context c1_rule806 [4] [7, 6, 3, 7, 4])
  have r2 := holds_trans r1 (holds_context c1_rule30 [] [6, 7, 6, 3, 7, 4])
  have r3 := holds_trans r2 (holds_context c1_rule806 [3, 4, 6, 7] [7, 4])
  have r4 := holds_trans r3 (holds_context c1_rule34 [3, 4, 6] [6, 7, 4])
  have r5 := holds_trans r4 (holds_context c1_rule806 [3, 4] [7, 6, 7, 4])
  have r6 := holds_trans r5 (holds_context c1_rule30 [3] [6, 7, 6, 7, 4])
  have r7 := holds_trans r6 (holds_context c1_rule200 [] [4, 6, 7, 6, 7, 4])
  have r8 := holds_trans r7 (holds_context c1_rule2072 [4] [])
  have r9 := holds_trans r8 (holds_context c1_rule201 [] [7, 6, 7, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r9))) (by central_nf)

theorem c1_rule2181 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ)) [7, 7, 4] [4, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule340 [6, 3] [])) (holds_context c1_rule208 [] [6, 3, 7, 7]))
  have l0 := holds_refl [6, 3, 3, 7, 7, 4, 6]
  have l1 := holds_trans l0 (holds_context c1_rule806 [] [3, 7, 7, 4, 6])
  have l2 := holds_trans l1 (holds_context c1_rule806 [3] [7, 7, 4, 6])
  have l3 := holds_trans l2 (holds_context c1_rule200 [] [6, 7, 7, 4, 6])
  have l4 := holds_trans l3 (holds_context c1_rule2166 [] [6])
  have l5 := holds_trans l4 (holds_context c1_rule1153 [4] [])
  have l6 := holds_trans l5 (holds_context c1_rule201 [] [7, 7, 4])
  have r0 := holds_refl [4, 6, 3, 6, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c1_rule806 [4] [6, 3, 7, 7])
  have r2 := holds_trans r1 (holds_context c1_rule30 [] [6, 6, 3, 7, 7])
  have r3 := holds_trans r2 (holds_context c1_rule202 [3, 4] [3, 7, 7])
  have r4 := holds_trans r3 (holds_context c1_rule30 [3] [7, 7])
  have r5 := holds_trans r4 (holds_context c1_rule200 [] [4, 7, 7])
  exact holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r5)) (by central_nf)

theorem c1_rule2232 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ)) [-7, 4, 6, 7, 7] [7, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule345 [] [9, 6])) (holds_context c1_rule74 [3, -7, 6] []))
  have l0 := holds_refl [7, 4, -9, 9, 6]
  have l1 := holds_trans l0 (holds_context c1_rule17 [7, 4] [6])
  have r0 := holds_refl [3, -7, 6, 3, 4, 7, 7]
  have r1 := holds_trans r0 (holds_context c1_rule806 [3, -7] [4, 7, 7])
  have r2 := holds_trans r1 (holds_context c1_rule33 [3] [6, 4, 7, 7])
  have r3 := holds_trans r2 (holds_context c1_rule200 [] [-7, 6, 4, 7, 7])
  have r4 := holds_trans r3 (holds_context c1_rule35 [-7] [7, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule2309 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 6] [3, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule355 [5, 6] [])) (holds_context c1_rule155 [] [5, 5]))
  have l0 := holds_refl [5, 6, 6, 7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule202 [5] [7, 6])
  have r0 := holds_refl [3, 7, 5, 4, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule1109 [] [4, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule751 [3] [5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule205 [3, 7] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

theorem c1_rule2311 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 4, -5] [6, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule355 [] [6, -7, -5, 7])) (holds_context c1_rule159 [3, 7, 4, 5] []))
  have l0 := holds_refl [6, 7, 6, 6, -7, -5, 7]
  have l1 := holds_trans l0 (holds_context c1_rule202 [6, 7] [-7, -5, 7])
  have l2 := holds_trans l1 (holds_context c1_rule12 [6] [-5, 7])
  have r0 := holds_refl [3, 7, 4, 5, 3, -5, 4, 4, -5]
  have r1 := holds_trans r0 (holds_context c1_rule32 [3, 7, 4] [-5, 4, 4, -5])
  have r2 := holds_trans r1 (holds_context c1_rule30 [3, 7] [5, -5, 4, 4, -5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [3] [4, 5, -5, 4, 4, -5])
  have r4 := holds_trans r3 (holds_context c1_rule200 [] [7, 4, 5, -5, 4, 4, -5])
  have r5 := holds_trans r4 (holds_context c1_rule8 [7, 4] [4, 4, -5])
  have r6 := holds_trans r5 (holds_context c1_rule201 [7] [4, -5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r6))) (by central_nf)

theorem c1_rule2410 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [7, 5, 5, 6] [3, 6, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule367 [] [5])) (holds_context c1_rule9 [6, 3, 7, 4] []))
  have l0 := holds_refl [7, 6, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule1952 [7] [])
  have r0 := holds_refl [6, 3, 7, 4]
  have r1 := holds_trans r0 (holds_context c1_rule806 [] [7, 4])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule2411 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s3_s5) [3, 7, 6, 5] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule367 [] [3])) (holds_context c1_rule31 [6, 3, 7, 4] []))
  have l0 := holds_refl [7, 6, 5, 3]
  have l1 := holds_trans l0 (holds_context c1_rule32 [7, 6] [])
  have l2 := holds_trans l1 (holds_context c1_rule806 [7] [5])
  have l3 := holds_trans l2 (holds_context c1_rule34 [] [6, 5])
  have r0 := holds_refl [6, 3, 7, 4, 3, -5]
  have r1 := holds_trans r0 (holds_context c1_rule806 [] [7, 4, 3, -5])
  have r2 := holds_trans r1 (holds_context c1_rule30 [3, 6, 7] [-5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [3, 6] [4, -5])
  have r4 := holds_trans r3 (holds_context c1_rule806 [3] [7, 4, -5])
  have r5 := holds_trans r4 (holds_context c1_rule200 [] [6, 7, 4, -5])
  have r6 := holds_trans r5 (holds_context c1_rule2311 [6] [])
  have r7 := holds_trans r6 (holds_context c1_rule202 [] [-5, 7])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r7)) (by central_nf)

theorem c1_rule2417 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 4, 6, -5] [3, 4, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule367 [4, 5, 5] [])) (holds_context c1_rule86 [] [3, 7, 4, -5]))
  have l0 := holds_refl [4, 5, 5, 7, 6, 5]
  have l1 := holds_trans l0 (holds_context c1_rule2309 [4, 5] [5])
  have l2 := holds_trans l1 (holds_context c1_rule32 [4] [7, -5, 5])
  have l3 := holds_trans l2 (holds_context c1_rule30 [] [5, 7, -5, 5])
  have l4 := holds_trans l3 (holds_context c1_rule9 [3, 4, 5, 7] [])
  have r0 := holds_refl [3, -7, 6, 7, 3, 7, 4, -5]
  have r1 := holds_trans r0 (holds_context c1_rule34 [3, -7, 6] [7, 4, -5])
  have r2 := holds_trans r1 (holds_context c1_rule806 [3, -7] [7, 7, 4, -5])
  have r3 := holds_trans r2 (holds_context c1_rule33 [3] [6, 7, 7, 4, -5])
  have r4 := holds_trans r3 (holds_context c1_rule200 [] [-7, 6, 7, 7, 4, -5])
  have r5 := holds_trans r4 (holds_context c1_rule2181 [-7, 6] [-5])
  have r6 := holds_trans r5 (holds_context c1_rule35 [-7] [7, 7, -5])
  have r7 := holds_trans r6 (holds_context c1_rule2232 [] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r7))) (by central_nf)

theorem c1_rule2426 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 6, 7, 4] [3, -5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule368 [] [3])) (holds_context c1_rule32 [7, 6, 3, 5] []))
  have l0 := holds_refl [6, 7, 4, 3]
  have l1 := holds_trans l0 (holds_context c1_rule30 [6, 7] [])
  have l2 := holds_trans l1 (holds_context c1_rule34 [6] [4])
  have l3 := holds_trans l2 (holds_context c1_rule806 [] [7, 4])
  have r0 := holds_refl [7, 6, 3, 5, 3, 5]
  have r1 := holds_trans r0 (holds_context c1_rule806 [7] [5, 3, 5])
  have r2 := holds_trans r1 (holds_context c1_rule34 [] [6, 5, 3, 5])
  have r3 := holds_trans r2 (holds_context c1_rule2411 [] [3, 5])
  have r4 := holds_trans r3 (holds_context c1_rule34 [-5] [5])
  have r5 := holds_trans r4 (holds_context c1_rule31 [] [7, 5])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r5)) (by central_nf)

theorem c1_rule2456 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ)) [3, 6, 7, 2, 8] [3, -5, 7, 5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule370 [] [7])) (holds_context c1_rule13 [6, 3, 7, 2, 8] []))
  have l0 := holds_refl [7, 6, 5, 2, 9, 7]
  have l1 := holds_trans l0 (holds_context c1_rule47 [7, 6, 5] [])
  have l2 := holds_trans l1 (holds_context c1_rule1952 [7] [2])
  have l3 := holds_trans l2 (holds_context c1_rule2410 [] [2])
  have l4 := holds_trans l3 (holds_context c1_rule2426 [] [2])
  have r0 := holds_refl [6, 3, 7, 2, 8]
  have r1 := holds_trans r0 (holds_context c1_rule806 [] [7, 2, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule2459 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s3_s5) [7, 6, 5] [3, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule370 [] [2, 9])) (holds_context c1_rule53 [6, 3, 7, 2, 8] []))
  have l0 := holds_refl [7, 6, 5, 2, 9, 2, 9]
  have l1 := holds_trans l0 (holds_context c1_rule45 [7, 6, 5, 2] [9])
  have l2 := holds_trans l1 (holds_context c1_rule199 [7, 6, 5] [-9, 9])
  have l3 := holds_trans l2 (holds_context c1_rule17 [7, 6, 5] [])
  have r0 := holds_refl [6, 3, 7, 2, 8, 2, -5]
  have r1 := holds_trans r0 (holds_context c1_rule806 [] [7, 2, 8, 2, -5])
  have r2 := holds_trans r1 (holds_context c1_rule2456 [] [2, -5])
  have r3 := holds_trans r2 (holds_context c1_rule199 [3, -5, 7, 5] [-5])
  have r4 := holds_trans r3 (holds_context c1_rule8 [3, -5, 7] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r4)) (by central_nf)

theorem c1_rule2488 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 6, -7, 4, 6] [-7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule371 [6, 3, 7, 7] [])) (holds_context c1_rule330 [] [3, 7, 5, 5]))
  have l0 := holds_refl [6, 3, 7, 7, 7, 4, 6]
  have l1 := holds_trans l0 (holds_context c1_rule806 [] [7, 7, 7, 4, 6])
  have l2 := holds_trans l1 (holds_context c1_rule206 [3, 6] [4, 6])
  have r0 := holds_refl [3, 4, 7, 7, 4, 3, 7, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule2181 [3, 4] [3, 7, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule201 [3] [7, 7, 3, 7, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [3, 7] [7, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule34 [3] [7, 7, 5, 5])
  have r5 := holds_trans r4 (holds_context c1_rule200 [] [7, 7, 7, 5, 5])
  have r6 := holds_trans r5 (holds_context c1_rule206 [] [5, 5])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r6)) (by central_nf)

theorem c1_rule2502 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-9, 3, 9, -7] [4, 6, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule373 [-9, 4, 9] [])) (holds_context c1_rule71 [] [6, 5, 5, -7]))
  have l0 := holds_refl [-9, 4, 9, -7, 6, 3]
  have l1 := holds_trans l0 (holds_context c1_rule2165 [] [6, 3])
  have l2 := holds_trans l1 (holds_context c1_rule806 [3, 4, 6, 7] [])
  have l3 := holds_trans l2 (holds_context c1_rule34 [3, 4, 6] [6])
  have l4 := holds_trans l3 (holds_context c1_rule806 [3, 4] [7, 6])
  have l5 := holds_trans l4 (holds_context c1_rule30 [3] [6, 7, 6])
  have l6 := holds_trans l5 (holds_context c1_rule200 [] [4, 6, 7, 6])
  have r0 := holds_refl [6, 3, 7, 7, 6, 5, 5, -7]
  have r1 := holds_trans r0 (holds_context c1_rule806 [] [7, 7, 6, 5, 5, -7])
  have r2 := holds_trans r1 (holds_context c1_rule1153 [3] [5, 5, -7])
  have r3 := holds_trans r2 (holds_context c1_rule2181 [3, 4] [5, 5, -7])
  have r4 := holds_trans r3 (holds_context c1_rule201 [3] [7, 7, 5, 5, -7])
  have r5 := holds_trans r4 (holds_context c1_rule1033 [3] [-7])
  have r6 := holds_trans r5 (holds_context c1_rule1047 [] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r6))) (by central_nf)

theorem c1_rule2511 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 4, 6, 7, 6] [5, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule373 [-9, 4, 9, 3] [])) (holds_context c1_rule315 [] [6, 5, 5, -7]))
  have l0 := holds_refl [-9, 4, 9, 3, -7, 6, 3]
  have l1 := holds_trans l0 (holds_context c1_rule1978 [] [-7, 6, 3])
  have l2 := holds_trans l1 (holds_context c1_rule2181 [6] [-7, 6, 3])
  have l3 := holds_trans l2 (holds_context c1_rule35 [] [7, 7, -7, 6, 3])
  have l4 := holds_trans l3 (holds_context c1_rule12 [4, 6, 7] [6, 3])
  have l5 := holds_trans l4 (holds_context c1_rule806 [4, 6, 7] [])
  have l6 := holds_trans l5 (holds_context c1_rule34 [4, 6] [6])
  have l7 := holds_trans l6 (holds_context c1_rule806 [4] [7, 6])
  have l8 := holds_trans l7 (holds_context c1_rule30 [] [6, 7, 6])
  have r0 := holds_refl [6, 7, 7, 6, 5, 5, -7]
  have r1 := holds_trans r0 (holds_context c1_rule1153 [] [5, 5, -7])
  have r2 := holds_trans r1 (holds_context c1_rule2181 [4] [5, 5, -7])
  have r3 := holds_trans r2 (holds_context c1_rule201 [] [7, 7, 5, 5, -7])
  have r4 := holds_trans r3 (holds_context c1_rule1033 [] [-7])
  have r5 := holds_trans r4 (holds_context c1_rule12 [5, 5, 7] [])
  exact holds_factor (holds_trans (holds_symm l8) (holds_trans h0 r5)) (by central_nf)

theorem c1_rule2515 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 4, 6, 5] [3, 6, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule374 [] [-5])) (holds_context c1_rule8 [-7, 4, 6, 5] []))
  have l0 := holds_refl [7, 7, 6, 3, 7, -5]
  have l1 := holds_trans l0 (holds_context c1_rule806 [7, 7] [7, -5])
  have l2 := holds_trans l1 (holds_context c1_rule34 [7] [6, 7, -5])
  have l3 := holds_trans l2 (holds_context c1_rule34 [] [7, 6, 7, -5])
  have l4 := holds_trans l3 (holds_context c1_rule2141 [] [7, -5])
  have l5 := holds_trans l4 (holds_context c1_rule206 [3, 6] [-5])
  have r0 := holds_refl [-7, 4, 6, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule2516 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-9, 6, 9] [9, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule374 [-7] [])) (holds_context c1_rule28 [] [4, 6, 5, 5]))
  have l0 := holds_refl [-7, 7, 7, 6, 3, 7]
  have l1 := holds_trans l0 (holds_context c1_rule13 [] [7, 6, 3, 7])
  have l2 := holds_trans l1 (holds_context c1_rule806 [7] [7])
  have l3 := holds_trans l2 (holds_context c1_rule34 [] [6, 7])
  have l4 := holds_trans l3 (holds_context c1_rule2144 [] [])
  have r0 := holds_refl [7, 7, 4, 6, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule2181 [] [6, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule2459 [4, 7] [5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [4] [-5, 7, 5])
  have r4 := holds_trans r3 (holds_context c1_rule30 [] [7, -5, 7, 5])
  have r5 := holds_trans r4 (holds_context c1_rule773 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule2552 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [9, 6, -9, 3] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule377 [2, 3, 4, 5] [])) (holds_context c1_rule100 [] [2, 4, 6, 5, 5]))
  have l0 := holds_refl [2, 3, 4, 5, 2, 4, 9, 4, -7]
  have l1 := holds_trans l0 (holds_context c1_rule441 [2] [4, 9, 4, -7])
  have l2 := holds_trans l1 (holds_context c1_rule199 [] [3, 7, -9, 4, 9, 4, -7])
  have l3 := holds_trans l2 (holds_context c1_rule71 [3, 7] [-7])
  have l4 := holds_trans l3 (holds_context c1_rule806 [3, 7] [7, 7, -7])
  have l5 := holds_trans l4 (holds_context c1_rule34 [3] [6, 7, 7, -7])
  have l6 := holds_trans l5 (holds_context c1_rule200 [] [7, 6, 7, 7, -7])
  have l7 := holds_trans l6 (holds_context c1_rule12 [7, 6, 7] [])
  have r0 := holds_refl [3, 7, 7, 2, 2, 4, 6, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule199 [3, 7, 7] [4, 6, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule2181 [3] [6, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule1108 [] [5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule717 [-9] [])
  have r5 := holds_trans r4 (holds_context c1_rule2516 [] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l7) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule2581 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [9, 6, -9, 4, -7] [3, 4, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule379 [-9, 4, 9] [])) (holds_context c1_rule315 [] [5, 5, -7]))
  have l0 := holds_refl [-9, 4, 9, 6, -7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule74 [] [-7, 6])
  have l2 := holds_trans l1 (holds_context c1_rule12 [3, 4, 7] [6])
  have r0 := holds_refl [6, 7, 7, 5, 5, -7]
  have r1 := holds_trans r0 (holds_context c1_rule1033 [6] [-7])
  have r2 := holds_trans r1 (holds_context c1_rule1952 [] [7, 7, -7])
  have r3 := holds_trans r2 (holds_context c1_rule396 [] [-7])
  have r4 := holds_trans r3 (holds_context c1_rule1974 [] [-7])
  have r5 := holds_trans r4 (holds_context c1_rule2516 [] [4, -7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule2631 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [7, 6, 7, 4] [4, -7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule384 [] [3])) (holds_context c1_rule32 [6, 7, 7, 5] []))
  have l0 := holds_refl [3, 4, 7, 6, 7, 3]
  have l1 := holds_trans l0 (holds_context c1_rule719 [] [3])
  have l2 := holds_trans l1 (holds_context c1_rule2516 [] [4, 3])
  have l3 := holds_trans l2 (holds_context c1_rule30 [9, 6, -9] [])
  have l4 := holds_trans l3 (holds_context c1_rule2552 [] [4])
  have r0 := holds_refl [6, 7, 7, 5, 3, 5]
  have r1 := holds_trans r0 (holds_context c1_rule32 [6, 7, 7] [5])
  have r2 := holds_trans r1 (holds_context c1_rule34 [6, 7] [5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [6] [7, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule806 [] [7, 7, 5, 5])
  have r5 := holds_trans r4 (holds_context c1_rule1033 [3, 6] [])
  have r6 := holds_trans r5 (holds_context c1_rule1952 [3] [7, 7])
  have r7 := holds_trans r6 (holds_context c1_rule396 [3] [])
  have r8 := holds_trans r7 (holds_context c1_rule200 [] [4, -7, 6, -7])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r8)) (by central_nf)

theorem c1_rule2664 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [3, 4, 6, 7, 7] [-9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule387 [3, 4, -5, -7] [])) (holds_context c1_rule161 [] [6, -7, 4, 6]))
  have l0 := holds_refl [3, 4, -5, -7, 3, -5, 4, -7, 4]
  have l1 := holds_trans l0 (holds_context c1_rule33 [3, 4, -5] [-5, 4, -7, 4])
  have l2 := holds_trans l1 (holds_context c1_rule31 [3, 4] [-7, -5, 4, -7, 4])
  have l3 := holds_trans l2 (holds_context c1_rule30 [3] [-5, -7, -5, 4, -7, 4])
  have l4 := holds_trans l3 (holds_context c1_rule200 [] [4, -5, -7, -5, 4, -7, 4])
  have l5 := holds_trans l4 (holds_context c1_rule813 [] [4])
  have l6 := holds_trans l5 (holds_context c1_rule2141 [] [4])
  have l7 := holds_trans l6 (holds_context c1_rule2181 [3, 6] [])
  have l8 := holds_trans l7 (holds_context c1_rule35 [3] [7, 7])
  have r0 := holds_refl [3, -7, 6, 6, -7, 4, 6]
  have r1 := holds_trans r0 (holds_context c1_rule202 [3, -7] [-7, 4, 6])
  have r2 := holds_trans r1 (holds_context c1_rule28 [3] [4, 6])
  have r3 := holds_trans r2 (holds_context c1_rule2181 [3] [6])
  have r4 := holds_trans r3 (holds_context c1_rule1108 [] [])
  exact holds_factor (holds_trans (holds_symm l8) (holds_trans h0 r4)) (by central_nf)

theorem c1_rule2711 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [-5, 4, -7, 6] [5, 5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule392 [] [7, 6, -9, 6, 9])) (holds_context c1_rule137 [5, -7, 6] []))
  have l0 := holds_refl [3, -5, 4, 6, 7, 6, -9, 6, 9]
  have l1 := holds_trans l0 (holds_context c1_rule687 [3, -5, 4] [9])
  have l2 := holds_trans l1 (holds_context c1_rule30 [3, -5] [-7, 6, -9, 9])
  have l3 := holds_trans l2 (holds_context c1_rule31 [3] [4, -7, 6, -9, 9])
  have l4 := holds_trans l3 (holds_context c1_rule200 [] [-5, 4, -7, 6, -9, 9])
  have l5 := holds_trans l4 (holds_context c1_rule17 [-5, 4, -7, 6] [])
  have r0 := holds_refl [5, -7, 6, 3, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule806 [5, -7] [3, 4, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule33 [5] [6, 3, 4, 5, 5])
  have r3 := holds_trans r2 (holds_context c1_rule32 [] [-7, 6, 3, 4, 5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule806 [3, 5, -7] [4, 5, 5])
  have r5 := holds_trans r4 (holds_context c1_rule33 [3, 5] [6, 4, 5, 5])
  have r6 := holds_trans r5 (holds_context c1_rule32 [3] [-7, 6, 4, 5, 5])
  have r7 := holds_trans r6 (holds_context c1_rule200 [] [5, -7, 6, 4, 5, 5])
  have r8 := holds_trans r7 (holds_context c1_rule35 [5, -7] [5, 5])
  have r9 := holds_trans r8 (holds_context c1_rule2515 [5] [5])
  have r10 := holds_trans r9 (holds_context c1_rule32 [] [6, -7, -5, 5])
  have r11 := holds_trans r10 (holds_context c1_rule778 [3] [5])
  have r12 := holds_trans r11 (holds_context c1_rule200 [] [5, 5, -7, 5])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r12)) (by central_nf)

theorem c1_rule2761 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [5, 5, 6, 7] [3, 4, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule396 [] [-7])) (holds_context c1_rule12 [5, 5, 6, 7] []))
  have l0 := holds_refl [3, 4, -7, 6, -7, -7]
  have l1 := holds_trans l0 (holds_context c1_rule1974 [] [-7])
  have l2 := holds_trans l1 (holds_context c1_rule2516 [] [4, -7])
  have l3 := holds_trans l2 (holds_context c1_rule2581 [] [])
  have r0 := holds_refl [5, 5, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
