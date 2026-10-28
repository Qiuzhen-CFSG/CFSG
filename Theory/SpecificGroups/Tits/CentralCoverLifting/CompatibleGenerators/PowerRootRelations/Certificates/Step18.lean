module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step17

/-! Kernel-checked central word identities, chunk 18.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule1184 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4) [5, 5, 4, -7, -9] [7, 6, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1108 [-5] [])) (holds_context c6_rule9 [] [7, 6, -9, 6]))
  have l0 := holds_refl [-5, -5, 4, -7, -9]
  have l1 := holds_trans l0 (holds_context c6_rule26 [] [4, -7, -9])
  have r0 := holds_refl [7, 6, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1192 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [3, -7, -9, 6, 9] [4, 5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1130 [-7] [])) (holds_context c6_rule13 [] [4, 5, 7, -5]))
  have l0 := holds_refl [-7, -9, 6, 9, 3]
  have l1 := holds_trans l0 (holds_context c6_rule1162 [-7] [])
  have l2 := holds_trans l1 (holds_context c6_rule32 [] [-9, 6, 9])
  have r0 := holds_refl [4, 5, 7, -5]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1194 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4) [-9, 6, 9, 6, -7] [5, 5, 4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1132 [-9] [])) (holds_context c6_rule17 [] [5, 5, 4, 7]))
  have l0 := holds_refl [-9, 6, 9, 6, -7]
  have r0 := holds_refl [5, 5, 4, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1211 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, 9, 3, 7, 4] [9, 5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1155 [6] [])) (holds_context c6_rule172 [] [9, 5, -7, -5]))
  have l0 := holds_refl [6, 9, 3, 7, 4]
  have r0 := holds_refl [9, 5, -7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1224 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [7, 6, -9, 6, 9] [5, 5, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1184 [] [9])) (holds_context c6_rule17 [5, 5, 4, -7] []))
  have l0 := holds_refl [7, 6, -9, 6, 9]
  have r0 := holds_refl [5, 5, 4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1232 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .v_s7_s4) [5, 5, 4, 7, 6] [-7, -9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1192 [3] [])) (holds_context c6_rule170 [] [-7, -9, 6, 9]))
  have l0 := holds_refl [3, 4, 5, 7, -5]
  have l1 := holds_trans l0 (holds_context c6_rule560 [] [])
  have r0 := holds_refl [-7, -9, 6, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1233 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, -9, 6, 9] [3, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1194 [] [6])) (holds_context c6_rule1120 [-9] []))
  have l0 := holds_refl [5, 5, 4, 7, 6]
  have l1 := holds_trans l0 (holds_context c6_rule1232 [] [])
  have r0 := holds_refl [-9, 9, 3, 6, 7]
  have r1 := holds_trans r0 (holds_context c6_rule17 [] [3, 6, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule1234 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-5, 7, -5, 7] [-9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1233 [7] [])) (holds_context c6_rule12 [] [-9, 6, 9]))
  have l0 := holds_refl [7, 3, 6, 7]
  have l1 := holds_trans l0 (holds_context c6_rule33 [] [6, 7])
  have l2 := holds_trans l1 (holds_context c6_rule336 [] [7])
  have r0 := holds_refl [-9, 6, 9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1235 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 6, 7, -9] [-7, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1233 [] [-9])) (holds_context c6_rule16 [-7, -9, 6] []))
  have l0 := holds_refl [3, 6, 7, -9]
  have r0 := holds_refl [-7, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1236 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, -9, 6, 9] [7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1234 [5] [])) (holds_context c6_rule8 [] [7, -5, 7]))
  have l0 := holds_refl [5, -9, 6, 9]
  have r0 := holds_refl [7, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1237 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-9, 6, 9, -7] [-5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1234 [] [-7])) (holds_context c6_rule12 [-5, 7, -5] []))
  have l0 := holds_refl [-9, 6, 9, -7]
  have r0 := holds_refl [-5, 7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1238 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, -7, -9, 6] [6, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1235 [3] [])) (holds_context c6_rule170 [] [6, 7, -9]))
  have l0 := holds_refl [3, -7, -9, 6]
  have r0 := holds_refl [6, 7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1242 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 7, -9, 6] [3, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1238 [] [6])) (holds_context c6_rule172 [3, -7, -9] []))
  have l0 := holds_refl [6, 7, -9, 6]
  have r0 := holds_refl [3, -7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1245 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, -7, 5, -9] [7, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1242 [6] [])) (holds_context c6_rule172 [] [7, -9, 6]))
  have l0 := holds_refl [6, 3, -7, -9]
  have l1 := holds_trans l0 (holds_context c6_rule355 [] [-7, -9])
  have l2 := holds_trans l1 (holds_context c6_rule351 [] [-9])
  have r0 := holds_refl [7, -9, 6]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1249 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, -9, 6, 9] [5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1245 [] [9])) (holds_context c6_rule17 [5, -7, 5] []))
  have l0 := holds_refl [7, -9, 6, 9]
  have r0 := holds_refl [5, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1251 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, -7, 6, -7] [-9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1249 [-7] [])) (holds_context c6_rule13 [] [-9, 6, 9]))
  have l0 := holds_refl [-7, 5, -7, 5]
  have l1 := holds_trans l0 (holds_context c6_rule375 [] [])
  have r0 := holds_refl [-9, 6, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1254 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [-9, 6, 9, 7] [3, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1251 [] [7])) (holds_context c6_rule13 [3, -7, 6] []))
  have l0 := holds_refl [-9, 6, 9, 7]
  have r0 := holds_refl [3, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1255 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [3, -9, 6, 9] [-7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1251 [3] [])) (holds_context c6_rule170 [] [-7, 6, -7]))
  have l0 := holds_refl [3, -9, 6, 9]
  have r0 := holds_refl [-7, 6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1258 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [9, 3, -7, 6] [6, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1254 [9] [])) (holds_context c6_rule16 [] [6, 9, 7]))
  have l0 := holds_refl [9, 3, -7, 6]
  have r0 := holds_refl [6, 9, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1260 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, -7, -9] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1255 [] [-9])) (holds_context c6_rule16 [3, -9, 6] []))
  have l0 := holds_refl [-7, 6, -7, -9]
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1263 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [-7, 6, 7, 7] [7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1255 [] [-7])) (holds_context c6_rule1237 [3] []))
  have l0 := holds_refl [-7, 6, -7, -7]
  have l1 := holds_trans l0 (holds_context c6_rule27 [-7, 6] [])
  have r0 := holds_refl [3, -5, 7, -5]
  have r1 := holds_trans r0 (holds_context c6_rule30 [] [7, -5])
  have r2 := holds_trans r1 (holds_context c6_rule326 [-5] [])
  have r3 := holds_trans r2 (holds_context c6_rule9 [] [7, 6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

theorem c6_rule1265 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [-7, 6, 7] [7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1263 [] [-7])) (holds_context c6_rule12 [-7, 6, 7] []))
  have l0 := holds_refl [7, 6, -7]
  have r0 := holds_refl [-7, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1266 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [-7, 6, -7] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1263 [] [7])) (holds_context c6_rule176 [-7, 6] []))
  have l0 := holds_refl [7, 6, 7]
  have r0 := holds_refl [-7, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1267 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [7, 6, 7, 7] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1255 [] [7])) (holds_context c6_rule1254 [3] []))
  have l0 := holds_refl [-7, 6, -7, 7]
  have l1 := holds_trans l0 (holds_context c6_rule1266 [] [7])
  have r0 := holds_refl [3, 3, -7, 6]
  have r1 := holds_trans r0 (holds_context c6_rule170 [] [-7, 6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule1268 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 9, 7, 6] [9, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1258 [] [6])) (holds_context c6_rule172 [9, 3, -7] []))
  have l0 := holds_refl [6, 9, 7, 6]
  have r0 := holds_refl [9, 3, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1269 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 7, -9, 6] [6, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1260 [7] [])) (holds_context c6_rule12 [] [6, -7, -9]))
  have l0 := holds_refl [7, 3, -9, 6]
  have l1 := holds_trans l0 (holds_context c6_rule33 [] [-9, 6])
  have r0 := holds_refl [6, -7, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1281 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-13 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ)) [7, 6, -7, 4] [5, 5, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1265 [] [4])) (holds_context c6_rule269 [-7] []))
  have l0 := holds_refl [7, 6, -7, 4]
  have r0 := holds_refl [-7, -5, 7, 5]
  have r1 := holds_trans r0 (holds_context c6_rule329 [] [5])
  have r2 := holds_trans r1 (holds_context c6_rule387 [3] [])
  have r3 := holds_trans r2 (holds_context c6_rule31 [] [5, 6])
  have r4 := holds_trans r3 (holds_context c6_rule31 [5] [6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem c6_rule1282 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 7, -9] [3, -9, 6] := by
  have h0 := c6_rule1260
  have l0 := holds_refl [-7, 6, -7, -9]
  have l1 := holds_trans l0 (holds_context c6_rule1266 [] [-9])
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1285 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 9, 3, -7] [9, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1268 [6] [])) (holds_context c6_rule172 [] [9, 7, 6]))
  have l0 := holds_refl [6, 9, 3, -7]
  have r0 := holds_refl [9, 7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1287 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [9, 7, 6, 7] [6, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1285 [] [7])) (holds_context c6_rule13 [6, 9, 3] []))
  have l0 := holds_refl [9, 7, 6, 7]
  have r0 := holds_refl [6, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1288 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 9, 3, 7] [9, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1287 [] [7])) (holds_context c6_rule1267 [9] []))
  have l0 := holds_refl [6, 9, 3, 7]
  have r0 := holds_refl [9, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1306 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [9, 5, -7, -5, 4] [9, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1211 [] [4])) (holds_context c6_rule171 [6, 9, 3, 7] []))
  have l0 := holds_refl [9, 5, -7, -5, 4]
  have r0 := holds_refl [6, 9, 3, 7]
  have r1 := holds_trans r0 (holds_context c6_rule1288 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule1307 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [5, -7, -5, 4] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1306 [-9] [])) (holds_context c6_rule17 [] [5, -7, -5, 4]))
  have l0 := holds_refl [-9, 9, -7, 6]
  have l1 := holds_trans l0 (holds_context c6_rule17 [] [-7, 6])
  have r0 := holds_refl [5, -7, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1308 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [-7, -5, 4] [-5, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1307 [-5] [])) (holds_context c6_rule9 [] [-7, -5, 4]))
  have l0 := holds_refl [-5, -7, 6]
  have r0 := holds_refl [-7, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1310 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, -5, -7, 6] [-5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1308 [7] [])) (holds_context c6_rule12 [] [-5, 4]))
  have l0 := holds_refl [7, -5, -7, 6]
  have r0 := holds_refl [-5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1311 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, -5, -7] [-5, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1310 [] [6])) (holds_context c6_rule172 [7, -5, -7] []))
  have l0 := holds_refl [-5, 4, 6]
  have l1 := holds_trans l0 (holds_context c6_rule34 [-5] [])
  have r0 := holds_refl [7, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1316 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * normalizedRelatorError .vii_s4) [-7, -5, 1, 10] [-5, -7, 1, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1308 [] [1])) (holds_context c6_rule37 [-7, -5] []))
  have l0 := holds_refl [-5, -7, 6, 1]
  have l1 := holds_trans l0 (holds_context c6_rule39 [-5, -7] [])
  have r0 := holds_refl [-7, -5, 1, 10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1328 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [-5, 6, 4, 7] [7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1311 [] [7])) (holds_context c6_rule13 [7, -5] []))
  have l0 := holds_refl [-5, 6, 4, 7]
  have r0 := holds_refl [7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1329 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [6, 4, 7] [5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1328 [5] [])) (holds_context c6_rule8 [] [6, 4, 7]))
  have l0 := holds_refl [5, 7, -5]
  have r0 := holds_refl [6, 4, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1338 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 7, -5] [6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1329 [4] [])) (holds_context c6_rule34 [] [4, 7]))
  have l0 := holds_refl [4, 5, 7, -5]
  have r0 := holds_refl [6, 4, 4, 7]
  have r1 := holds_trans r0 (holds_context c6_rule171 [6] [7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
