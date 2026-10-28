module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step10

/-! Kernel-checked central word identities, chunk 11.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c2_rule1391 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 4, 6, 5] [5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1382 [] [5])) (holds_context c2_rule9 [5, -7] []))
  have l0 := holds_refl [-7, 4, 6, 5]
  have r0 := holds_refl [5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1400 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 7, -5, -7] [4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1389 [5] [])) (holds_context c2_rule8 [] [4, 6]))
  have l0 := holds_refl [5, 7, -5, -7]
  have r0 := holds_refl [4, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1401 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 7, -5] [4, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1400 [] [7])) (holds_context c2_rule13 [5, 7, -5] []))
  have l0 := holds_refl [4, 6, 7]
  have r0 := holds_refl [5, 7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1408 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [4, 6, 7, 5] [5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1401 [] [5])) (holds_context c2_rule9 [5, 7] []))
  have l0 := holds_refl [4, 6, 7, 5]
  have r0 := holds_refl [5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1409 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [6, 7, 5] [4, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1408 [4] [])) (holds_context c2_rule230 [] [6, 7, 5]))
  have l0 := holds_refl [4, 5, 7]
  have r0 := holds_refl [6, 7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1441 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [8, 7, 6, 7, 7] [8, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule566 [3, 8] [])) (holds_context c2_rule375 [] [-7, 5]))
  have l0 := holds_refl [3, 8, 3, 6, -7]
  have l1 := holds_trans l0 (holds_context c2_rule1196 [] [-7])
  have l2 := holds_trans l1 (holds_context c2_rule1213 [] [-7])
  have l3 := holds_trans l2 (holds_context c2_rule28 [8, 7, 6] [])
  have r0 := holds_refl [4, 8, -5, -7, 5]
  have r1 := holds_trans r0 (holds_context c2_rule603 [4, 8] [])
  have r2 := holds_trans r1 (holds_context c2_rule36 [4] [-7, 6])
  have r3 := holds_trans r2 (holds_context c2_rule230 [] [8, -7, 6])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r3)) (by central_nf)

theorem c2_rule1442 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 6, 7, 7] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1441 [8] [])) (holds_context c2_rule232 [] [7, 6, 7, 7]))
  have l0 := holds_refl [8, 8, -7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule232 [] [-7, 6])
  have r0 := holds_refl [7, 6, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1443 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, -7] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1442 [] [-7])) (holds_context c2_rule12 [7, 6, 7] []))
  have l0 := holds_refl [-7, 6, -7]
  have r0 := holds_refl [7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1444 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 7, 6] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1442 [-7] [])) (holds_context c2_rule13 [] [6, 7, 7]))
  have l0 := holds_refl [-7, -7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule28 [] [6])
  have r0 := holds_refl [6, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1445 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, 7] [7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1442 [] [7])) (holds_context c2_rule235 [7, 6] []))
  have l0 := holds_refl [-7, 6, 7]
  have r0 := holds_refl [7, 6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1450 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [4, 7, 7, 4] [7, 7] := by
  have h0 := c2_rule1272
  have l0 := holds_refl [6, 7, 7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule1444 [6] [])
  have l2 := holds_trans l1 (holds_context c2_rule231 [] [7, 7])
  have r0 := holds_refl [4, 7, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1451 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 7, 4] [4, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1450 [4] [])) (holds_context c2_rule230 [] [7, 7, 4]))
  have l0 := holds_refl [4, 7, 7]
  have r0 := holds_refl [7, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1456 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [6, 7, 6, -7] [4, 3, 5, 5] := by
  have h0 := c2_rule83
  have l0 := holds_refl [6, -7, 6, 7]
  have l1 := holds_trans l0 (holds_context c2_rule1445 [6] [])
  have r0 := holds_refl [8, 3, 8, 3]
  have r1 := holds_trans r0 (holds_context c2_rule322 [] [3])
  have r2 := holds_trans r1 (holds_context c2_rule32 [4, 5] [])
  have r3 := holds_trans r2 (holds_context c2_rule32 [4] [5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

theorem c2_rule1461 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 4, 7, 7] [7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1451 [-7] [])) (holds_context c2_rule13 [] [7, 4]))
  have l0 := holds_refl [-7, 4, 7, 7]
  have r0 := holds_refl [7, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1462 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 4, 7] [7, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1461 [] [-7])) (holds_context c2_rule12 [-7, 4, 7] []))
  have l0 := holds_refl [7, 4, -7]
  have r0 := holds_refl [-7, 4, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1467 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 7, 4, -7] [-7, -5, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1462 [-5] [])) (holds_context c2_rule1386 [] [7]))
  have l0 := holds_refl [-5, 7, 4, -7]
  have r0 := holds_refl [-7, -5, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1541 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [4, -9, 4, 9, 7] [8, 7, 8] := by
  have h0 := c2_rule461
  have l0 := holds_refl [-7, 4, 5, 5, 6]
  have l1 := holds_trans l0 (holds_context c2_rule1216 [] [6])
  have l2 := holds_trans l1 (holds_context c2_rule1075 [4] [])
  have l3 := holds_trans l2 (holds_context c2_rule230 [] [3, 6, -7])
  have l4 := holds_trans l3 (holds_context c2_rule1137 [] [])
  have r0 := holds_refl [4, -9, 4, 9, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1542 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-9, 4, 9, 7] [4, 8, 7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1541 [4] [])) (holds_context c2_rule230 [] [-9, 4, 9, 7]))
  have l0 := holds_refl [4, 8, 7, 8]
  have r0 := holds_refl [-9, 4, 9, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1586 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, -5, 6, 7, 6] [4, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule603 [-5, 7] [])) (holds_context c2_rule538 [] [-7, 5]))
  have l0 := holds_refl [-5, 7, 4, -7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule1467 [] [6])
  have r0 := holds_refl [3, 7, 6, -7, 5]
  have r1 := holds_trans r0 (holds_context c2_rule1145 [] [-7, 5])
  have r2 := holds_trans r1 (holds_context c2_rule1132 [8] [5])
  have r3 := holds_trans r2 (holds_context c2_rule322 [] [6, 5])
  have r4 := holds_trans r3 (holds_context c2_rule1013 [4] [5])
  have r5 := holds_trans r4 (holds_context c2_rule234 [4, 6] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r5)) (by central_nf)

theorem c2_rule1587 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ)) [-5, 6, 7, 6] [4, 3, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1586 [7] [])) (holds_context c2_rule12 [] [-5, 6, 7, 6]))
  have l0 := holds_refl [7, 4, 6, -5]
  have l1 := holds_trans l0 (holds_context c2_rule1044 [] [])
  have l2 := holds_trans l1 (holds_context c2_rule1409 [3] [])
  have l3 := holds_trans l2 (holds_context c2_rule30 [] [5, 7])
  have r0 := holds_refl [-5, 6, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1723 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [9, 4, 3, -5, -9] [2, 3, 9, -5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule638 [] [-9])) (holds_context c2_rule292 [2, 3] []))
  have l0 := holds_refl [9, 4, 3, -5, -9]
  have r0 := holds_refl [2, 3, 9, -5, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1752 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [5, -7, 6] [4, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule768 [-5] [])) (holds_context c2_rule48 [] [8, 5, 2]))
  have l0 := holds_refl [-5, -9, 4, 9, 7]
  have l1 := holds_trans l0 (holds_context c2_rule1542 [-5] [])
  have l2 := holds_trans l1 (holds_context c2_rule319 [] [7, 8])
  have l3 := holds_trans l2 (holds_context c2_rule1143 [5, 8] [])
  have l4 := holds_trans l3 (holds_context c2_rule232 [5] [-7, 6])
  have r0 := holds_refl [2, -7, 8, 5, 2]
  have r1 := holds_trans r0 (holds_context c2_rule1192 [2] [2])
  have r2 := holds_trans r1 (holds_context c2_rule250 [2, 8] [])
  have r3 := holds_trans r2 (holds_context c2_rule41 [2] [-7, 5])
  have r4 := holds_trans r3 (holds_context c2_rule228 [] [4, -7, 5])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r4)) (by central_nf)

theorem c2_rule1762 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [5, 4, -5, -7] [4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1752 [] [-5])) (holds_context c2_rule582 [5] []))
  have l0 := holds_refl [4, -7, 5, -5]
  have l1 := holds_trans l0 (holds_context c2_rule8 [4, -7] [])
  have r0 := holds_refl [5, 4, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1763 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [5, 4, -5] [4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1762 [] [7])) (holds_context c2_rule13 [5, 4, -5] []))
  have l0 := holds_refl [4, -7, 7]
  have l1 := holds_trans l0 (holds_context c2_rule13 [4] [])
  have r0 := holds_refl [5, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1764 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-5, 4] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1763 [-5] [])) (holds_context c2_rule9 [] [4, -5]))
  have l0 := holds_refl [-5, 4]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1765 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [5, 4] [4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1763 [] [5])) (holds_context c2_rule9 [5, 4] []))
  have l0 := holds_refl [4, 5]
  have r0 := holds_refl [5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1768 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-5, 2, 8] [4, -5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1764 [] [2])) (holds_context c2_rule42 [-5] []))
  have l0 := holds_refl [4, -5, 2]
  have r0 := holds_refl [-5, 2, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1781 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [9, 4, 3, -5] [2, 3, -7, 2] := by
  have h0 := c2_rule526
  have l0 := holds_refl [9, 3, -5, 4]
  have l1 := holds_trans l0 (holds_context c2_rule1764 [9, 3] [])
  have l2 := holds_trans l1 (holds_context c2_rule30 [9] [-5])
  have r0 := holds_refl [2, 3, -7, 2]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1802 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 2, 9, 3] [4, -5, 2, 7] := by
  have h0 := c2_rule907
  have l0 := holds_refl [-5, 2, 8, 7]
  have l1 := holds_trans l0 (holds_context c2_rule1768 [] [7])
  have r0 := holds_refl [3, 2, 9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1957 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-5, -9, 4] [-9, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1093 [2] [])) (holds_context c2_rule183 [] [-5]))
  have l0 := holds_refl [2, -7, 2, 4]
  have l1 := holds_trans l0 (holds_context c2_rule255 [] [4])
  have r0 := holds_refl [-9, -7, 5, 4, -5]
  have r1 := holds_trans r0 (holds_context c2_rule1765 [-9, -7] [-5])
  have r2 := holds_trans r1 (holds_context c2_rule8 [-9, -7, 4] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c2_rule1959 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-9, -7, 4, 6] [3, 5, -9] := by
  have h0 := c2_rule628
  have l0 := holds_refl [-5, -9, 4, 6]
  have l1 := holds_trans l0 (holds_context c2_rule1957 [] [6])
  have r0 := holds_refl [3, 5, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1960 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [5, -9, -7, 4] [-9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1957 [5] [])) (holds_context c2_rule8 [] [-9, 4]))
  have l0 := holds_refl [5, -9, -7, 4]
  have r0 := holds_refl [-9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1961 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [5, -9, -7] [-9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1960 [] [4])) (holds_context c2_rule230 [5, -9, -7] []))
  have l0 := holds_refl [-9, 4, 4]
  have l1 := holds_trans l0 (holds_context c2_rule230 [-9] [])
  have r0 := holds_refl [5, -9, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1962 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-5, -9] [-9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1961 [-5] [])) (holds_context c2_rule9 [] [-9, -7]))
  have l0 := holds_refl [-5, -9]
  have r0 := holds_refl [-9, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1963 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [5, -9] [-9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1961 [] [7])) (holds_context c2_rule13 [5, -9] []))
  have l0 := holds_refl [-9, 7]
  have r0 := holds_refl [5, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1964 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [2, -9, -7] [-7, 2] := by
  have h0 := c2_rule251
  have l0 := holds_refl [2, -5, -9]
  have l1 := holds_trans l0 (holds_context c2_rule1962 [2] [])
  have r0 := holds_refl [-7, 2]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1965 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [-9, -7, 9] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1962 [] [9])) (holds_context c2_rule17 [-5] []))
  have l0 := holds_refl [-9, -7, 9]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1966 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [9, -5] [-7, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1965 [9] [])) (holds_context c2_rule16 [] [-7, 9]))
  have l0 := holds_refl [9, -5]
  have r0 := holds_refl [-7, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1969 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-9, 7, 9] [5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1963 [] [9])) (holds_context c2_rule17 [5] []))
  have l0 := holds_refl [-9, 7, 9]
  have r0 := holds_refl [5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1970 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [9, 5] [7, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1969 [9] [])) (holds_context c2_rule16 [] [7, 9]))
  have l0 := holds_refl [9, 5]
  have r0 := holds_refl [7, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
