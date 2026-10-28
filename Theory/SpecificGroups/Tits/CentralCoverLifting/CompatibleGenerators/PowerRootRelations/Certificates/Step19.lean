module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step18

/-! Kernel-checked central word identities, chunk 19.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule1339 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 7] [6, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1338 [] [5])) (holds_context c6_rule9 [4, 5, 7] []))
  have l0 := holds_refl [6, 7, 5]
  have r0 := holds_refl [4, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1346 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [6, 7, 5, -7] [4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1339 [] [-7])) (holds_context c6_rule12 [4, 5] []))
  have l0 := holds_refl [6, 7, 5, -7]
  have r0 := holds_refl [4, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1347 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [7, 5, -7] [6, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1346 [6] [])) (holds_context c6_rule172 [] [7, 5, -7]))
  have l0 := holds_refl [6, 4, 5]
  have r0 := holds_refl [7, 5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1356 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ)) [-9, 6, 9, 6] [6, -9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1224 [-7] [])) (holds_context c6_rule13 [] [6, -9, 6, 9]))
  have l0 := holds_refl [-7, 5, 5, 4, -7]
  have l1 := holds_trans l0 (holds_context c6_rule654 [] [])
  have l2 := holds_trans l1 (holds_context c6_rule1266 [3] [6])
  have l3 := holds_trans l2 (holds_context c6_rule336 [] [7, 6])
  have l4 := holds_trans l3 (holds_context c6_rule1234 [] [6])
  have r0 := holds_refl [6, -9, 6, 9]
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1404 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, 5] [5, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1236 [3, 7] [])) (holds_context c6_rule1114 [] [9]))
  have l0 := holds_refl [3, 7, 7, -5, 7]
  have l1 := holds_trans l0 (holds_context c6_rule349 [3] [])
  have l2 := holds_trans l1 (holds_context c6_rule170 [] [-7, 6, 5])
  have r0 := holds_refl [5, -7, 4, -9, 9]
  have r1 := holds_trans r0 (holds_context c6_rule17 [5, -7, 4] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule1407 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [6, 4, 5, 4] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1404 [7] [])) (holds_context c6_rule12 [] [6, 5]))
  have l0 := holds_refl [7, 5, -7, 4]
  have l1 := holds_trans l0 (holds_context c6_rule1347 [] [4])
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1409 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [4, 5, 4] [5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1407 [6] [])) (holds_context c6_rule172 [] [4, 5, 4]))
  have l0 := holds_refl [6, 6, 5]
  have l1 := holds_trans l0 (holds_context c6_rule172 [] [5])
  have r0 := holds_refl [4, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1410 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [4, 5] [5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1409 [4] [])) (holds_context c6_rule171 [] [5, 4]))
  have l0 := holds_refl [4, 5]
  have r0 := holds_refl [5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1411 : Holds ((normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [4, -5, 4] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1409 [5, 5] [])) (holds_context c6_rule230 [] [4]))
  have l0 := holds_refl [5, 5, 5]
  have l1 := holds_trans l0 (holds_context c6_rule175 [] [])
  have r0 := holds_refl [4, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1412 : Holds ((normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [4, -5] [-5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1411 [4] [])) (holds_context c6_rule171 [] [-5, 4]))
  have l0 := holds_refl [4, -5]
  have r0 := holds_refl [-5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1416 : Holds ((normalizedRelatorError .i_s1) ^ (4 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ)) [-7, 6, -5] [-5, 4, -7] := by
  have h0 := c6_rule214
  have l0 := holds_refl [4, -5, -7]
  have l1 := holds_trans l0 (holds_context c6_rule1412 [] [-7])
  have r0 := holds_refl [-7, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1598 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (9 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ)) [5, 6, -5, 4, -7] [6, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1281 [-7] [])) (holds_context c6_rule13 [] [6, -7, 4]))
  have l0 := holds_refl [-7, 5, 5, 3, 6]
  have l1 := holds_trans l0 (holds_context c6_rule219 [] [6])
  have l2 := holds_trans l1 (holds_context c6_rule365 [] [5, 6])
  have l3 := holds_trans l2 (holds_context c6_rule259 [-5, 6] [])
  have l4 := holds_trans l3 (holds_context c6_rule389 [] [4, -7])
  have r0 := holds_refl [6, -7, 4]
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1599 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (9 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ)) [6, -5, 4, -7] [-5, 6, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1598 [-5] [])) (holds_context c6_rule9 [] [6, -5, 4, -7]))
  have l0 := holds_refl [-5, 6, -7, 4]
  have r0 := holds_refl [6, -5, 4, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1732 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ)) [9, 6, -9, 6, 9] [6, 9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1356 [9] [])) (holds_context c6_rule16 [] [6, 9, 6]))
  have l0 := holds_refl [9, 6, -9, 6, 9]
  have r0 := holds_refl [6, 9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1733 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ)) [9, 6, -9, 6] [6, 9, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1732 [] [-9])) (holds_context c6_rule16 [9, 6, -9, 6] []))
  have l0 := holds_refl [6, 9, 6, -9]
  have r0 := holds_refl [9, 6, -9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2183 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [-5, 9, 9, 3, 10, 3] [5, 4, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule83 [-5] [])) (holds_context c6_rule9 [] [5, 3, 3, 4, 10]))
  have l0 := holds_refl [-5, 9, 9, 3, 10, 3]
  have r0 := holds_refl [5, 3, 3, 4, 10]
  have r1 := holds_trans r0 (holds_context c6_rule170 [5] [4, 10])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule2184 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [9, 9, 3, 10, 3] [5, 5, 4, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2183 [5] [])) (holds_context c6_rule8 [] [9, 9, 3, 10, 3]))
  have l0 := holds_refl [5, 5, 4, 10]
  have r0 := holds_refl [9, 9, 3, 10, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2185 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [-5, 9, 9, 3, 10] [5, 4, 10, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2183 [] [3])) (holds_context c6_rule170 [-5, 9, 9, 3, 10] []))
  have l0 := holds_refl [5, 4, 10, 3]
  have r0 := holds_refl [-5, 9, 9, 3, 10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2186 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [-9, 5, 5, 4, 10] [9, 3, 10, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2184 [-9] [])) (holds_context c6_rule17 [] [9, 3, 10, 3]))
  have l0 := holds_refl [-9, 5, 5, 4, 10]
  have r0 := holds_refl [9, 3, 10, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2189 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s8 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [5, 4, 10, 3, 10] [-5, 9, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2185 [] [10])) (holds_context c6_rule174 [-5, 9, 9, 3] []))
  have l0 := holds_refl [5, 4, 10, 3, 10]
  have r0 := holds_refl [-5, 9, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2190 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [9, 3, 10, 3, 10] [-9, 5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2186 [] [10])) (holds_context c6_rule174 [-9, 5, 5, 4] []))
  have l0 := holds_refl [9, 3, 10, 3, 10]
  have r0 := holds_refl [-9, 5, 5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2194 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [5, 5, 9, 9, 3] [4, 10, 3, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2189 [-5] [])) (holds_context c6_rule9 [] [4, 10, 3, 10]))
  have l0 := holds_refl [-5, -5, 9, 9, 3]
  have l1 := holds_trans l0 (holds_context c6_rule26 [] [9, 9, 3])
  have r0 := holds_refl [4, 10, 3, 10]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2195 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [9, 9, 5, 5, 4] [3, 10, 3, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2190 [-9] [])) (holds_context c6_rule17 [] [3, 10, 3, 10]))
  have l0 := holds_refl [-9, -9, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c6_rule28 [] [5, 5, 4])
  have r0 := holds_refl [3, 10, 3, 10]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2198 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [3, 10, 3, 10, 4] [9, 9, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2195 [] [4])) (holds_context c6_rule171 [9, 9, 5, 5] []))
  have l0 := holds_refl [3, 10, 3, 10, 4]
  have r0 := holds_refl [9, 9, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2202 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [3, 9, 9, 5, 5] [10, 3, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2198 [3] [])) (holds_context c6_rule170 [] [10, 3, 10, 4]))
  have l0 := holds_refl [3, 9, 9, 5, 5]
  have r0 := holds_refl [10, 3, 10, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2234 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ)) [6, 9, 3, 6] [3, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule133 [9] [])) (holds_context c6_rule16 [] [3, 9, 3, 3, 4]))
  have l0 := holds_refl [9, 6, -9, 6, 9, 3]
  have l1 := holds_trans l0 (holds_context c6_rule1733 [] [9, 3])
  have l2 := holds_trans l1 (holds_context c6_rule17 [6, 9, 6] [3])
  have l3 := holds_trans l2 (holds_context c6_rule355 [6, 9] [])
  have r0 := holds_refl [3, 9, 3, 3, 4]
  have r1 := holds_trans r0 (holds_context c6_rule170 [3, 9] [4])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule2235 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [3, 6, 9, 4] [9, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2234 [6] [])) (holds_context c6_rule172 [] [9, 3, 6]))
  have l0 := holds_refl [6, 3, 9, 4]
  have l1 := holds_trans l0 (holds_context c6_rule355 [] [9, 4])
  have r0 := holds_refl [9, 3, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2236 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [3, 9, 6, 4] [6, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2234 [] [6])) (holds_context c6_rule172 [6, 9, 3] []))
  have l0 := holds_refl [3, 9, 4, 6]
  have l1 := holds_trans l0 (holds_context c6_rule34 [3, 9] [])
  have r0 := holds_refl [6, 9, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2237 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ)) [3, 9, 3, 6] [6, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2235 [3] [])) (holds_context c6_rule170 [] [6, 9, 4]))
  have l0 := holds_refl [3, 9, 3, 6]
  have r0 := holds_refl [6, 9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2238 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ)) [9, 3, 6, 4] [3, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2235 [] [4])) (holds_context c6_rule171 [3, 6, 9] []))
  have l0 := holds_refl [9, 3, 6, 4]
  have r0 := holds_refl [3, 6, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2241 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [6, 9, 6, 4] [3, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2237 [] [6])) (holds_context c6_rule172 [3, 9, 3] []))
  have l0 := holds_refl [6, 9, 4, 6]
  have l1 := holds_trans l0 (holds_context c6_rule34 [6, 9] [])
  have r0 := holds_refl [3, 9, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2242 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [-9, 3, 6, 9] [3, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2238 [-9] [])) (holds_context c6_rule17 [] [3, 6, 4]))
  have l0 := holds_refl [-9, 3, 6, 9]
  have r0 := holds_refl [3, 6, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2246 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ)) [3, 9, 3, 4] [6, 9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2241 [] [4])) (holds_context c6_rule171 [6, 9, 6] []))
  have l0 := holds_refl [3, 9, 3, 4]
  have r0 := holds_refl [6, 9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2247 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ)) [3, 6, 4, -9] [-9, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2242 [] [-9])) (holds_context c6_rule16 [-9, 3, 6] []))
  have l0 := holds_refl [3, 6, 4, -9]
  have r0 := holds_refl [-9, 3, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2248 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [3, -9, 3, 6] [6, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2247 [3] [])) (holds_context c6_rule170 [] [6, 4, -9]))
  have l0 := holds_refl [3, -9, 3, 6]
  have r0 := holds_refl [6, 4, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2249 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ)) [6, 4, -9, 6] [3, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2248 [] [6])) (holds_context c6_rule172 [3, -9, 3] []))
  have l0 := holds_refl [6, 4, -9, 6]
  have r0 := holds_refl [3, -9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2250 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [3, 6, -9, 3] [4, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2249 [6] [])) (holds_context c6_rule172 [] [4, -9, 6]))
  have l0 := holds_refl [6, 3, -9, 3]
  have l1 := holds_trans l0 (holds_context c6_rule355 [] [-9, 3])
  have r0 := holds_refl [4, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2290 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ)) [6, 9, 3, 9, 3] [10, 3, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2236 [] [9, 3])) (holds_context c6_rule994 [3, 9] []))
  have l0 := holds_refl [6, 9, 3, 9, 3]
  have r0 := holds_refl [3, 9, 9, 5, 5]
  have r1 := holds_trans r0 (holds_context c6_rule2202 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule2422 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ)) [6, 4, -9, 3] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2248 [] [3])) (holds_context c6_rule355 [3, -9, 3] []))
  have l0 := holds_refl [6, 4, -9, 3]
  have r0 := holds_refl [3, -9, 3, 3, 6]
  have r1 := holds_trans r0 (holds_context c6_rule170 [3, -9] [6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule2524 : Holds ((normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [6, 9, 6, 9, 6] [10, 3, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2290 [] [4])) (holds_context c6_rule2246 [6, 9] []))
  have l0 := holds_refl [10, 3, 10, 4, 4]
  have l1 := holds_trans l0 (holds_context c6_rule171 [10, 3, 10] [])
  have r0 := holds_refl [6, 9, 6, 9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
