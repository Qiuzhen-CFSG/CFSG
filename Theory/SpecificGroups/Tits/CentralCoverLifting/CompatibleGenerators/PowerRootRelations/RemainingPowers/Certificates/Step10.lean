module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Certificates.Step09

/-! Additional kernel-checked central word identities, chunk 10.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p21_rule1258 : Holds ((normalizedRelatorError .i_r8) ^ (-14 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (22 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-17 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (9 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-9 : ℤ)) [4, 8, -9, 8] [-9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule987 [] [-7])) (holds_context p21_rule788 [4] []))
  have l0 := holds_refl [-9, 4, 7, -7]
  have l1 := holds_trans l0 (holds_context p21_rule12 [-9, 4] [])
  have r0 := holds_refl [4, 8, -9, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1259 : Holds ((normalizedRelatorError .i_r8) ^ (-14 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (22 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-17 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (9 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-9 : ℤ)) [8, -9, 8] [4, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1258 [4] [])) (holds_context p21_rule199 [] [8, -9, 8]))
  have l0 := holds_refl [4, -9, 4]
  have r0 := holds_refl [8, -9, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1269 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [8, 9, 8] [4, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule995 [] [-5])) (holds_context p21_rule8 [4, 9, 4] []))
  have l0 := holds_refl [7, 6, 9, -5]
  have l1 := holds_trans l0 (holds_context p21_rule811 [] [])
  have r0 := holds_refl [4, 9, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1274 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [9, 8, -7, 8] [6, 9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1004 [] [6])) (holds_context p21_rule200 [6, 9, -7] []))
  have l0 := holds_refl [9, 3, 7, 6]
  have l1 := holds_trans l0 (holds_context p21_rule398 [9] [])
  have r0 := holds_refl [6, 9, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1290 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-24 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [4, -9, 6, -5] [-9, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1030 [] [-5])) (holds_context p21_rule8 [-9, 3, 5] []))
  have l0 := holds_refl [4, -9, 6, -5]
  have r0 := holds_refl [-9, 3, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1291 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-24 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [9, 4, -9, 6] [3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1030 [9] [])) (holds_context p21_rule16 [] [3, 5, 5]))
  have l0 := holds_refl [9, 4, -9, 6]
  have r0 := holds_refl [3, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1292 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-24 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [4, -9, 6, 5] [-9, 3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1030 [] [5])) (holds_context p21_rule216 [-9, 3] []))
  have l0 := holds_refl [4, -9, 6, 5]
  have r0 := holds_refl [-9, 3, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1321 : Holds ((normalizedRelatorError .i_r8) ^ (-9 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [9, 8, -9, -7] [8, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1099 [9] [])) (holds_context p21_rule16 [] [8, -7, 6]))
  have l0 := holds_refl [9, 8, -9, -7]
  have r0 := holds_refl [8, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1322 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [7, -9, 8, 7] [-9, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1100 [7] [])) (holds_context p21_rule12 [] [-9, -5, -7]))
  have l0 := holds_refl [7, -9, 8, 7]
  have r0 := holds_refl [-9, -5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1324 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [8, 7, 7, 5] [9, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1101 [] [5])) (holds_context p21_rule9 [9, -7, -9] []))
  have l0 := holds_refl [8, 7, 7, 5]
  have r0 := holds_refl [9, -7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1335 : Holds ((normalizedRelatorError .i_r8) ^ (-20 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-15 : ℤ) * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (31 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-31 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (12 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (14 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-9, 6, -7, 8] [8, -5, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1172 [] [7])) (holds_context p21_rule992 [8] []))
  have l0 := holds_refl [-9, 3, 8, 7]
  have l1 := holds_trans l0 (holds_context p21_rule725 [-9] [])
  have r0 := holds_refl [8, -5, 6, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1338 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 8, 3, 9] [6, 9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1174 [] [9])) (holds_context p21_rule17 [6, 9, 8] []))
  have l0 := holds_refl [3, 8, 3, 9]
  have r0 := holds_refl [6, 9, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1339 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, -5, 6, -9] [-5, 8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1179 [-9] [])) (holds_context p21_rule17 [] [-5, 8, -9]))
  have l0 := holds_refl [-9, 6, -7, 8]
  have l1 := holds_trans l0 (holds_context p21_rule1335 [] [])
  have r0 := holds_refl [-5, 8, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1342 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4) [8, 2, 3, 5] [6, 2, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1184 [2] [])) (holds_context p21_rule43 [] [-5, 6]))
  have l0 := holds_refl [2, 4, 3, 5]
  have l1 := holds_trans l0 (holds_context p21_rule41 [] [3, 5])
  have r0 := holds_refl [6, 2, -5, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1343 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (10 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ)) [6, 8, -5, 6] [4, 8, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1184 [8] [])) (holds_context p21_rule223 [] [-5, 6]))
  have l0 := holds_refl [8, 4, 3, 5]
  have l1 := holds_trans l0 (holds_context p21_rule36 [] [3, 5])
  have r0 := holds_refl [6, 8, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1347 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [-5, 7, 1, 8] [6, -5, 7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1189 [] [1])) (holds_context p21_rule40 [-5, 7] []))
  have l0 := holds_refl [6, -5, 7, 1]
  have r0 := holds_refl [-5, 7, 1, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1400 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [6, 9, -7, 8] [9, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1274 [] [8])) (holds_context p21_rule201 [9, 8, -7] []))
  have l0 := holds_refl [6, 9, -7, 8]
  have r0 := holds_refl [9, 8, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1410 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [9, 6, 3, -9] [5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1291 [] [3])) (holds_context p21_rule1020 [9] []))
  have l0 := holds_refl [3, 5, 5, 3]
  have l1 := holds_trans l0 (holds_context p21_rule32 [3, 5] [])
  have l2 := holds_trans l1 (holds_context p21_rule32 [3] [5])
  have l3 := holds_trans l2 (holds_context p21_rule198 [] [5, 5])
  have r0 := holds_refl [9, 6, 3, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1411 : Holds ((normalizedRelatorError .i_r8) ^ (-12 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (18 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-5 : ℤ)) [-9, 5, 5] [6, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1410 [-9] [])) (holds_context p21_rule17 [] [6, 3, -9]))
  have l0 := holds_refl [-9, 5, 5]
  have r0 := holds_refl [6, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1423 : Holds ((normalizedRelatorError .i_r8) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (6 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-13 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-9, 7, 7, -5] [7, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1322 [] [-7])) (holds_context p21_rule12 [7, -9, 8] []))
  have l0 := holds_refl [-9, -5, -7, -7]
  have l1 := holds_trans l0 (holds_context p21_rule28 [-9, -5] [])
  have l2 := holds_trans l1 (holds_context p21_rule1008 [-9] [])
  have r0 := holds_refl [7, -9, 8]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1424 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [8, 9, -7, -9] [7, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1324 [8] [])) (holds_context p21_rule201 [] [7, 7, 5]))
  have l0 := holds_refl [8, 9, -7, -9]
  have r0 := holds_refl [7, 7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1429 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 3, 9, 8] [8, 3, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1338 [3] [])) (holds_context p21_rule198 [] [8, 3, 9]))
  have l0 := holds_refl [3, 6, 9, 8]
  have l1 := holds_trans l0 (holds_context p21_rule274 [] [9, 8])
  have r0 := holds_refl [8, 3, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1431 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, -5, 6] [-5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1339 [] [9])) (holds_context p21_rule17 [8, -5, 6] []))
  have l0 := holds_refl [-5, 8, -9, 9]
  have l1 := holds_trans l0 (holds_context p21_rule17 [-5, 8] [])
  have r0 := holds_refl [8, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1432 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * normalizedRelatorError .viii_r3) [-5, 6, 8] [8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1431 [] [6])) (holds_context p21_rule200 [8, -5] []))
  have l0 := holds_refl [-5, 8, 6]
  have l1 := holds_trans l0 (holds_context p21_rule223 [-5] [])
  have r0 := holds_refl [8, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1433 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * normalizedRelatorError .viii_r3) [8, -5, 8] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1431 [8] [])) (holds_context p21_rule201 [] [-5, 6]))
  have l0 := holds_refl [8, -5, 8]
  have r0 := holds_refl [-5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1434 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (8 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 8, -5] [6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1432 [5] [])) (holds_context p21_rule8 [] [6, 8]))
  have l0 := holds_refl [5, 8, -5]
  have r0 := holds_refl [6, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1435 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * normalizedRelatorError .viii_r3) [6, 8, 5] [5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1434 [] [5])) (holds_context p21_rule9 [5, 8] []))
  have l0 := holds_refl [6, 8, 5]
  have r0 := holds_refl [5, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1436 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (13 : ℤ) * (normalizedRelatorError .i_s6) ^ (8 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 5, 8] [8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1435 [6] [])) (holds_context p21_rule200 [] [8, 5]))
  have l0 := holds_refl [6, 5, 8]
  have r0 := holds_refl [8, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1437 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-13 : ℤ) * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * normalizedRelatorError .viii_r3) [8, 5, 8] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1436 [] [8])) (holds_context p21_rule201 [6, 5] []))
  have l0 := holds_refl [8, 5, 8]
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1468 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [6, 9, 8, -7] [9, -7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1400 [6] [])) (holds_context p21_rule200 [] [9, -7, 8]))
  have l0 := holds_refl [6, 9, 8, -7]
  have r0 := holds_refl [9, -7, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1480 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [6, 3, -9, -5] [-9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1411 [] [-5])) (holds_context p21_rule8 [-9, 5] []))
  have l0 := holds_refl [6, 3, -9, -5]
  have r0 := holds_refl [-9, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1481 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [3, -9, -5] [6, -9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1480 [6] [])) (holds_context p21_rule200 [] [3, -9, -5]))
  have l0 := holds_refl [6, -9, 5]
  have r0 := holds_refl [3, -9, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1487 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-10 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (17 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [-9, 4, 3, 7] [4, 6, -9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1411 [5] [])) (holds_context p21_rule445 [] [5, 5]))
  have l0 := holds_refl [5, 6, 3, -9]
  have l1 := holds_trans l0 (holds_context p21_rule645 [] [-9])
  have l2 := holds_trans l1 (holds_context p21_rule1071 [] [-9])
  have l3 := holds_trans l2 (holds_context p21_rule444 [4, 6] [])
  have r0 := holds_refl [-9, 7, 5, 5]
  have r1 := holds_trans r0 (holds_context p21_rule736 [-9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule1498 : Holds ((normalizedRelatorError .i_r8) ^ (5 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, -9, 8, 5] [-9, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1423 [] [5])) (holds_context p21_rule9 [-9, 7, 7] []))
  have l0 := holds_refl [7, -9, 8, 5]
  have r0 := holds_refl [-9, 7, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1502 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [7, 7, 5, 9] [8, 9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1424 [] [9])) (holds_context p21_rule17 [8, 9, -7] []))
  have l0 := holds_refl [7, 7, 5, 9]
  have r0 := holds_refl [8, 9, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1510 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-31 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (24 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [4, 8, 3, 5] [6, -5, 8] := by
  have h0 := p21_rule1343
  have l0 := holds_refl [6, 8, -5, 6]
  have l1 := holds_trans l0 (holds_context p21_rule1431 [6] [])
  have r0 := holds_refl [4, 8, 3, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1515 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-6 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (31 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-21 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, 8, 5] [9, 8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1431 [] [5])) (holds_context p21_rule492 [8] []))
  have l0 := holds_refl [-5, 8, 5]
  have r0 := holds_refl [8, 5, 6, -5]
  have r1 := holds_trans r0 (holds_context p21_rule977 [8] [])
  have r2 := holds_trans r1 (holds_context p21_rule406 [] [])
  have r3 := holds_trans r2 (holds_context p21_rule787 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem p21_rule1525 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (18 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-19 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-5 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (8 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [4, -5, 10, 4] [8, -5, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1432 [] [10])) (holds_context p21_rule56 [-5] []))
  have l0 := holds_refl [8, -5, 10]
  have r0 := holds_refl [-5, 4, 10, 4]
  have r1 := holds_trans r0 (holds_context p21_rule438 [] [10, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule1536 : Holds ((normalizedRelatorError .i_r8) ^ (-12 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (25 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [8, 5, -7, 8] [3, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1433 [7] [])) (holds_context p21_rule887 [] [8]))
  have l0 := holds_refl [7, -5, 6]
  have l1 := holds_trans l0 (holds_context p21_rule629 [] [])
  have r0 := holds_refl [8, 5, -7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1545 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * normalizedRelatorError .viii_r3) [4, 6, 3, 8] [5, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1435 [] [5])) (holds_context p21_rule338 [6] []))
  have l0 := holds_refl [5, 8, 5]
  have r0 := holds_refl [6, 4, 3, 8]
  have r1 := holds_trans r0 (holds_context p21_rule35 [] [3, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
