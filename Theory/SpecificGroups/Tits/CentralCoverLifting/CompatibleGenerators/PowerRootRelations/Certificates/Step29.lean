module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step28

/-! Kernel-checked central word identities, chunk 29.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c9_rule1167 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 7, 6, 4] [6, 7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1166 [6] [])) (holds_context c9_rule226 [] [3, 7, 6, 4]))
  have l0 := holds_refl [6, 7, 5, 5]
  have r0 := holds_refl [3, 7, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1203 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 9, 3, 5, 5] [4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule448 [6, 9] [])) (holds_context c9_rule132 [] [4]))
  have l0 := holds_refl [6, 9, 3, 5, 5]
  have r0 := holds_refl [4, 9, 4, 4]
  have r1 := holds_trans r0 (holds_context c9_rule225 [4, 9] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule1204 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 9, 3, 5] [4, 9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1203 [] [-5])) (holds_context c9_rule8 [6, 9, 3, 5] []))
  have l0 := holds_refl [4, 9, -5]
  have r0 := holds_refl [6, 9, 3, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1205 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [9, 3, 5, 5] [6, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1203 [6] [])) (holds_context c9_rule226 [] [9, 3, 5, 5]))
  have l0 := holds_refl [6, 4, 9]
  have r0 := holds_refl [9, 3, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1206 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 9, 3, -5] [4, 9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1203 [] [5])) (holds_context c9_rule229 [6, 9, 3] []))
  have l0 := holds_refl [4, 9, 5]
  have r0 := holds_refl [6, 9, 3, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1207 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [4, 9, 5, 5] [6, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1204 [] [-5])) (holds_context c9_rule8 [6, 9, 3] []))
  have l0 := holds_refl [4, 9, -5, -5]
  have l1 := holds_trans l0 (holds_context c9_rule27 [4, 9] [])
  have r0 := holds_refl [6, 9, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1208 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [6, 4, 9, -5] [9, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1204 [6] [])) (holds_context c9_rule226 [] [9, 3, 5]))
  have l0 := holds_refl [6, 4, 9, -5]
  have r0 := holds_refl [9, 3, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1209 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [-9, 6, 4, 9] [3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1205 [-9] [])) (holds_context c9_rule17 [] [3, 5, 5]))
  have l0 := holds_refl [-9, 6, 4, 9]
  have r0 := holds_refl [3, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1211 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 4, 9, 3] [9, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1207 [4] [])) (holds_context c9_rule225 [] [9, 5, 5]))
  have l0 := holds_refl [4, 6, 9, 3]
  have l1 := holds_trans l0 (holds_context c9_rule35 [] [9, 3])
  have r0 := holds_refl [9, 5, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1213 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [3, 5, 5, -9] [-9, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1209 [] [-9])) (holds_context c9_rule16 [-9, 6, 4] []))
  have l0 := holds_refl [3, 5, 5, -9]
  have r0 := holds_refl [-9, 6, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1215 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [6, 9, 5, 5] [4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1211 [6] [])) (holds_context c9_rule226 [] [4, 9, 3]))
  have l0 := holds_refl [6, 9, 5, 5]
  have r0 := holds_refl [4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1216 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [3, -9, 6, 4] [5, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1213 [3] [])) (holds_context c9_rule224 [] [5, 5, -9]))
  have l0 := holds_refl [3, -9, 6, 4]
  have r0 := holds_refl [5, 5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1218 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [4, 9, 3, -5] [6, 9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1215 [] [-5])) (holds_context c9_rule8 [6, 9, 5] []))
  have l0 := holds_refl [4, 9, 3, -5]
  have r0 := holds_refl [6, 9, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1220 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [5, 5, -9, 4] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1216 [] [4])) (holds_context c9_rule225 [3, -9, 6] []))
  have l0 := holds_refl [5, 5, -9, 4]
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1222 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [3, 5, -9, 6] [-5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1220 [5] [])) (holds_context c9_rule229 [] [-9, 4]))
  have l0 := holds_refl [5, 3, -9, 6]
  have l1 := holds_trans l0 (holds_context c9_rule32 [] [-9, 6])
  have r0 := holds_refl [-5, -9, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1226 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [3, -5, -9, 4] [5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1222 [3] [])) (holds_context c9_rule224 [] [5, -9, 6]))
  have l0 := holds_refl [3, -5, -9, 4]
  have r0 := holds_refl [5, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1227 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [-5, -9, 6, 4] [3, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1222 [] [6])) (holds_context c9_rule226 [3, 5, -9] []))
  have l0 := holds_refl [-5, -9, 4, 6]
  have l1 := holds_trans l0 (holds_context c9_rule35 [-5, -9] [])
  have r0 := holds_refl [3, 5, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1250 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ)) [6, -7, 5, 5, 7] [5, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule455 [5] [])) (holds_context c9_rule32 [] [-7, -5, 7]))
  have l0 := holds_refl [5, 6, 5]
  have r0 := holds_refl [3, 5, -7, -5, 7]
  have r1 := holds_trans r0 (holds_context c9_rule472 [] [-5, 7])
  have r2 := holds_trans r1 (holds_context c9_rule27 [6, -7] [7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule1251 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ)) [-7, 5, 5, 7] [6, 5, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1250 [6] [])) (holds_context c9_rule226 [] [-7, 5, 5, 7]))
  have l0 := holds_refl [6, 5, 6, 5]
  have r0 := holds_refl [-7, 5, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1307 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, -9, 4, 9, 4] [-7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule478 [] [7, 7])) (holds_context c9_rule71 [-5] []))
  have l0 := holds_refl [3, -5, 6, 7, 7]
  have l1 := holds_trans l0 (holds_context c9_rule493 [3] [])
  have l2 := holds_trans l1 (holds_context c9_rule224 [] [-7, 5, -7])
  have r0 := holds_refl [-5, -9, 4, 9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1308 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, -9, 4, 9] [-7, 5, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1307 [] [4])) (holds_context c9_rule225 [-5, -9, 4, 9] []))
  have l0 := holds_refl [-7, 5, -7, 4]
  have r0 := holds_refl [-5, -9, 4, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1326 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [4, 9, 5, 4] [9, 7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule485 [2] [])) (holds_context c9_rule51 [] [-5, 7]))
  have l0 := holds_refl [2, 6, 3, -7, 2]
  have l1 := holds_trans l0 (holds_context c9_rule43 [] [3, -7, 2])
  have l2 := holds_trans l1 (holds_context c9_rule599 [6] [])
  have l3 := holds_trans l2 (holds_context c9_rule1206 [] [4])
  have r0 := holds_refl [9, 7, -5, 7]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1347 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ)) [6, 4, 7, 7, 4] [7, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule503 [4] [])) (holds_context c9_rule35 [] [7, 7, 4]))
  have l0 := holds_refl [4, -9, 4, 9, 3]
  have l1 := holds_trans l0 (holds_context c9_rule75 [] [3])
  have l2 := holds_trans l1 (holds_context c9_rule459 [3, 7] [])
  have l3 := holds_trans l2 (holds_context c9_rule34 [3] [7, 6])
  have l4 := holds_trans l3 (holds_context c9_rule224 [] [7, 7, 6])
  have r0 := holds_refl [6, 4, 7, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1348 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ)) [7, 7, 6, 4] [6, 4, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1347 [] [4])) (holds_context c9_rule225 [6, 4, 7, 7] []))
  have l0 := holds_refl [7, 7, 6, 4]
  have r0 := holds_refl [6, 4, 7, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1387 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -9, 2, 3, -5] [-7, 2, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule570 [] [3])) (holds_context c9_rule30 [-7, 2, 3] []))
  have l0 := holds_refl [3, -9, 2, -5, 3]
  have l1 := holds_trans l0 (holds_context c9_rule31 [3, -9, 2] [])
  have r0 := holds_refl [-7, 2, 3, 3, 4]
  have r1 := holds_trans r0 (holds_context c9_rule224 [-7, 2] [4])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule1478 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ)) [-9, 3, -9, 2, 3] [2, -7, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule616 [-9] [])) (holds_context c9_rule17 [] [2, -7, 5, 4]))
  have l0 := holds_refl [-9, 3, -9, 2, 3]
  have r0 := holds_refl [2, -7, 5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1496 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [5, 6, 5, 6, -7] [-7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule626 [5] [])) (holds_context c9_rule402 [] [6, 5]))
  have l0 := holds_refl [5, 6, 5, 6, -7]
  have r0 := holds_refl [-7, 5, 6, 6, 5]
  have r1 := holds_trans r0 (holds_context c9_rule226 [-7, 5] [5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule1497 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [5, 6, 5, 6] [6, 5, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1496 [] [7])) (holds_context c9_rule13 [5, 6, 5, 6] []))
  have l0 := holds_refl [-7, 5, 5, 7]
  have l1 := holds_trans l0 (holds_context c9_rule1251 [] [])
  have r0 := holds_refl [5, 6, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1501 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 2, -7, 6, 7] [2, 8, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule628 [9] [])) (holds_context c9_rule16 [] [2, 8, -9, 8]))
  have l0 := holds_refl [9, 2, -7, 6, 7]
  have r0 := holds_refl [2, 8, -9, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1509 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 8, 3, -7, 8] [6, 2, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule632 [4] [])) (holds_context c9_rule42 [] [3, -7, 8]))
  have l0 := holds_refl [4, 9, 3, -5, 2]
  have l1 := holds_trans l0 (holds_context c9_rule1218 [] [2])
  have l2 := holds_trans l1 (holds_context c9_rule243 [6] [])
  have r0 := holds_refl [2, 8, 3, -7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1510 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_r3) [8, 3, -7, 8] [6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1509 [2] [])) (holds_context c9_rule223 [] [8, 3, -7, 8]))
  have l0 := holds_refl [2, 6, 2, 7]
  have l1 := holds_trans l0 (holds_context c9_rule43 [] [2, 7])
  have l2 := holds_trans l1 (holds_context c9_rule223 [6] [7])
  have r0 := holds_refl [8, 3, -7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1511 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_r3) [3, -7, 8] [6, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1510 [8] [])) (holds_context c9_rule227 [] [3, -7, 8]))
  have l0 := holds_refl [8, 6, 7]
  have l1 := holds_trans l0 (holds_context c9_rule304 [] [7])
  have r0 := holds_refl [3, -7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1512 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_r3) [8, 3, -7] [6, 7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1510 [] [8])) (holds_context c9_rule227 [8, 3, -7] []))
  have l0 := holds_refl [6, 7, 8]
  have r0 := holds_refl [8, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1524 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 8, 7, 8] [3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1511 [] [8])) (holds_context c9_rule227 [3, -7] []))
  have l0 := holds_refl [6, 8, 7, 8]
  have r0 := holds_refl [3, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1525 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, 7, 8] [6, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1524 [6] [])) (holds_context c9_rule226 [] [8, 7, 8]))
  have l0 := holds_refl [6, 3, -7]
  have r0 := holds_refl [8, 7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1528 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 7, 8, 7] [8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1512 [] [7])) (holds_context c9_rule13 [8, 3] []))
  have l0 := holds_refl [6, 7, 8, 7]
  have r0 := holds_refl [8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1529 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 8, 7] [6, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1528 [6] [])) (holds_context c9_rule226 [] [7, 8, 7]))
  have l0 := holds_refl [6, 8, 3]
  have r0 := holds_refl [7, 8, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1556 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_r3) [-7, 6, 8, 3] [8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1529 [-7] [])) (holds_context c9_rule13 [] [8, 7]))
  have l0 := holds_refl [-7, 6, 8, 3]
  have r0 := holds_refl [8, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1568 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [-7, 6, 4, -5] [6, 3, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1556 [] [8, 5])) (holds_context c9_rule387 [-7, 6] []))
  have l0 := holds_refl [8, 7, 8, 5]
  have l1 := holds_trans l0 (holds_context c9_rule1525 [] [5])
  have r0 := holds_refl [-7, 6, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1569 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [-7, 6, 5, 5] [6, 3, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1556 [] [8, 4])) (holds_context c9_rule391 [-7, 6] []))
  have l0 := holds_refl [8, 7, 8, 4]
  have l1 := holds_trans l0 (holds_context c9_rule1525 [] [4])
  have r0 := holds_refl [-7, 6, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
