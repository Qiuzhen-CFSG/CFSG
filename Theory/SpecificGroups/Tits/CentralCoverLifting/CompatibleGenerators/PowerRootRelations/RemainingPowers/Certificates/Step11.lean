module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Certificates.Step10

/-! Additional kernel-checked central word identities, chunk 11.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p21_rule1548 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-13 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * normalizedRelatorError .viii_r3) [4, 10, 4, 5] [10, 5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1435 [10] [])) (holds_context p21_rule478 [] [8, 5]))
  have l0 := holds_refl [10, 5, 8]
  have r0 := holds_refl [6, 10, 8, 5]
  have r1 := holds_trans r0 (holds_context p21_rule705 [6] [5])
  have r2 := holds_trans r1 (holds_context p21_rule56 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem p21_rule1550 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-19 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [4, 3, -5, 8] [8, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1436 [] [6])) (holds_context p21_rule223 [6, 5] []))
  have l0 := holds_refl [8, 5, 6]
  have r0 := holds_refl [6, 5, 6, 8]
  have r1 := holds_trans r0 (holds_context p21_rule850 [] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule1551 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (8 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-21 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (26 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -5, 7, 8] [7, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1436 [7] [])) (holds_context p21_rule310 [] [8]))
  have l0 := holds_refl [7, 8, 5]
  have r0 := holds_refl [3, -5, 7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1553 : Holds ((normalizedRelatorError .i_r8) ^ (14 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (17 : ℤ) * (normalizedRelatorError .i_s6) ^ (10 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-37 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (35 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (18 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-14 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [4, 6, -5, 8] [8, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1436 [] [3])) (holds_context p21_rule625 [6] []))
  have l0 := holds_refl [8, 5, 3]
  have l1 := holds_trans l0 (holds_context p21_rule32 [8] [])
  have r0 := holds_refl [6, 4, -5, 8]
  have r1 := holds_trans r0 (holds_context p21_rule35 [] [-5, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule1554 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (13 : ℤ) * (normalizedRelatorError .i_s6) ^ (9 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (22 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (16 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [6, 7, -5, 8] [8, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1436 [] [-7])) (holds_context p21_rule881 [6] []))
  have l0 := holds_refl [8, 5, -7]
  have r0 := holds_refl [6, 7, -5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1560 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-13 : ℤ) * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * normalizedRelatorError .viii_r3) [8, 10, 5, 8] [6, 10, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1437 [10] [])) (holds_context p21_rule705 [] [5, 8]))
  have l0 := holds_refl [10, 6, 5]
  have l1 := holds_trans l0 (holds_context p21_rule478 [] [5])
  have r0 := holds_refl [8, 10, 5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1573 : Holds ((normalizedRelatorError .i_r8) ^ (12 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [3, -9, 3, -5] [6, -9, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1481 [] [3])) (holds_context p21_rule31 [3, -9] []))
  have l0 := holds_refl [6, -9, 5, 3]
  have l1 := holds_trans l0 (holds_context p21_rule32 [6, -9] [])
  have r0 := holds_refl [3, -9, 3, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1577 : Holds ((normalizedRelatorError .i_r8) ^ (20 : ℤ) * (normalizedRelatorError .i_s1) ^ (8 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (16 : ℤ) * (normalizedRelatorError .i_s6) ^ (10 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-22 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-46 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (22 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (11 : ℤ)) [3, -9, 4, -5] [6, -9, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1481 [] [4])) (holds_context p21_rule438 [3, -9] []))
  have l0 := holds_refl [6, -9, 5, 4]
  have l1 := holds_trans l0 (holds_context p21_rule439 [6, -9] [])
  have r0 := holds_refl [3, -9, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1593 : Holds ((normalizedRelatorError .i_r8) ^ (-25 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-11 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-14 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (9 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [4, 3, -7, -9] [-9, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1498 [-7] [])) (holds_context p21_rule13 [] [-9, 8, 5]))
  have l0 := holds_refl [-7, -9, 7, 7]
  have l1 := holds_trans l0 (holds_context p21_rule1074 [] [])
  have r0 := holds_refl [-9, 8, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1597 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-7, 8, 9, -7] [7, 5, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1502 [-7] [])) (holds_context p21_rule13 [] [7, 5, 9]))
  have l0 := holds_refl [-7, 8, 9, -7]
  have r0 := holds_refl [7, 5, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1611 : Holds ((normalizedRelatorError .i_r8) ^ (20 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-10 : ℤ) * (normalizedRelatorError .i_s4) ^ (14 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-62 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (45 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-22 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-15 : ℤ) * (normalizedRelatorError .viii_s2) ^ (4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-5, 9, 8, -9] [6, -5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1515 [-5] [])) (holds_context p21_rule27 [] [8, 5]))
  have l0 := holds_refl [-5, 9, 8, -9]
  have r0 := holds_refl [5, 5, 8, 5]
  have r1 := holds_trans r0 (holds_context p21_rule230 [] [5])
  have r2 := holds_trans r1 (holds_context p21_rule1510 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem p21_rule1612 : Holds ((normalizedRelatorError .i_r8) ^ (16 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (10 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (40 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (11 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-15 : ℤ) * (normalizedRelatorError .viii_s2) ^ (4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [9, 8, -9, 5] [8, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1515 [] [5])) (holds_context p21_rule338 [-5] []))
  have l0 := holds_refl [9, 8, -9, 5]
  have r0 := holds_refl [-5, 4, 3, 8]
  have r1 := holds_trans r0 (holds_context p21_rule438 [] [3, 8])
  have r2 := holds_trans r1 (holds_context p21_rule31 [4] [8])
  have r3 := holds_trans r2 (holds_context p21_rule1550 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem p21_rule1623 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (19 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (9 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (5 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [4, 8, -5, 10] [-5, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1525 [4] [])) (holds_context p21_rule199 [] [-5, 10, 4]))
  have l0 := holds_refl [4, 8, -5, 10]
  have r0 := holds_refl [-5, 10, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1633 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (14 : ℤ) * (normalizedRelatorError .i_s6) ^ (9 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-29 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (16 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [9, 5, 8, 5] [8, 3, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1545 [9] [])) (holds_context p21_rule573 [] [8]))
  have l0 := holds_refl [9, 5, 8, 5]
  have r0 := holds_refl [6, 3, 9, 8]
  have r1 := holds_trans r0 (holds_context p21_rule1429 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule1635 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (15 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-14 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [8, 3, -5, -7] [-5, 7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1551 [3] [])) (holds_context p21_rule198 [] [-5, 7, 8]))
  have l0 := holds_refl [3, 7, 8, 5]
  have l1 := holds_trans l0 (holds_context p21_rule396 [] [5])
  have l2 := holds_trans l1 (holds_context p21_rule1016 [8] [])
  have r0 := holds_refl [-5, 7, 8]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1637 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [3, 5, 7] [6, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1554 [] [8])) (holds_context p21_rule201 [6, 7, -5] []))
  have l0 := holds_refl [8, 5, -7, 8]
  have l1 := holds_trans l0 (holds_context p21_rule1536 [] [])
  have r0 := holds_refl [6, 7, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1641 : Holds ((normalizedRelatorError .i_r8) ^ (25 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (11 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-9 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [4, -9, 8, 5] [3, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1593 [4] [])) (holds_context p21_rule199 [] [3, -7, -9]))
  have l0 := holds_refl [4, -9, 8, 5]
  have r0 := holds_refl [3, -7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1642 : Holds ((normalizedRelatorError .i_r8) ^ (25 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-9 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-9, 8, 5, 6] [4, 6, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1593 [] [6])) (holds_context p21_rule538 [4] []))
  have l0 := holds_refl [-9, 8, 5, 6]
  have r0 := holds_refl [4, 6, 7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1644 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [7, 5, 9, 7] [-7, 8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1597 [] [7])) (holds_context p21_rule13 [-7, 8, 9] []))
  have l0 := holds_refl [7, 5, 9, 7]
  have r0 := holds_refl [-7, 8, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1664 : Holds ((normalizedRelatorError .i_r8) ^ (-20 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (10 : ℤ) * (normalizedRelatorError .i_s4) ^ (-14 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (6 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (62 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-45 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (22 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (15 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [6, -5, 8, 9] [-5, 9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1611 [] [9])) (holds_context p21_rule17 [-5, 9, 8] []))
  have l0 := holds_refl [6, -5, 8, 9]
  have r0 := holds_refl [-5, 9, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1666 : Holds ((normalizedRelatorError .i_r8) ^ (-41 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (-17 : ℤ) * (normalizedRelatorError .i_s6) ^ (-10 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-50 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-18 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (20 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (15 : ℤ) * (normalizedRelatorError .viii_s3) ^ (24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [4, 6, 7, -9] [8, -9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1612 [-9] [])) (holds_context p21_rule17 [] [8, -9, 5]))
  have l0 := holds_refl [-9, 8, 5, 6]
  have l1 := holds_trans l0 (holds_context p21_rule1642 [] [])
  have r0 := holds_refl [8, -9, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1672 : Holds ((normalizedRelatorError .i_r8) ^ (-16 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-17 : ℤ) * (normalizedRelatorError .i_s6) ^ (-11 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (12 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (40 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-29 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (14 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (14 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [6, 7, 8, 9] [9, 5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1633 [] [-5])) (holds_context p21_rule8 [9, 5, 8] []))
  have l0 := holds_refl [8, 3, 9, -5]
  have l1 := holds_trans l0 (holds_context p21_rule1077 [] [])
  have r0 := holds_refl [9, 5, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1680 : Holds ((normalizedRelatorError .i_r8) ^ (-19 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s5) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-22 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (7 : ℤ)) [3, 8, -7, -9] [-9, 3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1641 [] [8])) (holds_context p21_rule1437 [4, -9] []))
  have l0 := holds_refl [3, -7, -9, 8]
  have l1 := holds_trans l0 (holds_context p21_rule745 [3] [])
  have r0 := holds_refl [4, -9, 6, 5]
  have r1 := holds_trans r0 (holds_context p21_rule1292 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule1685 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 7, 8, 9] [5, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1644 [-7] [])) (holds_context p21_rule13 [] [5, 9, 7]))
  have l0 := holds_refl [-7, -7, 8, 9]
  have l1 := holds_trans l0 (holds_context p21_rule28 [] [8, 9])
  have r0 := holds_refl [5, 9, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1687 : Holds ((normalizedRelatorError .i_r8) ^ (20 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-10 : ℤ) * (normalizedRelatorError .i_s4) ^ (15 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-62 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (45 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-22 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-15 : ℤ) * (normalizedRelatorError .viii_s2) ^ (4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [6, -5, 9, 8] [-5, 8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1664 [6] [])) (holds_context p21_rule200 [] [-5, 8, 9]))
  have l0 := holds_refl [6, -5, 9, 8]
  have r0 := holds_refl [-5, 8, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1688 : Holds ((normalizedRelatorError .i_r8) ^ (-34 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s2) ^ (9 : ℤ) * (normalizedRelatorError .i_s4) ^ (-31 : ℤ) * (normalizedRelatorError .i_s6) ^ (-16 : ℤ) * (normalizedRelatorError .i_s3) ^ (5 : ℤ) * (normalizedRelatorError .i_s5) ^ (-12 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (99 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-80 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (18 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-18 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-26 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-26 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-13 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (29 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (14 : ℤ) * (normalizedRelatorError .viii_s3) ^ (28 : ℤ) * normalizedRelatorError .viii_r3) [8, 3, 5, 9] [4, -5, 9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1664 [4] [])) (holds_context p21_rule1553 [] [9]))
  have l0 := holds_refl [4, -5, 9, 8]
  have r0 := holds_refl [8, 3, 5, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1691 : Holds ((normalizedRelatorError .i_r8) ^ (41 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-5 : ℤ) * (normalizedRelatorError .i_s4) ^ (17 : ℤ) * (normalizedRelatorError .i_s6) ^ (10 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (50 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (18 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-20 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-15 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [8, -9, 5, 9] [4, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1666 [] [9])) (holds_context p21_rule17 [4, 6, 7] []))
  have l0 := holds_refl [8, -9, 5, 9]
  have r0 := holds_refl [4, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1693 : Holds ((normalizedRelatorError .i_r8) ^ (16 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (11 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (40 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (11 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-15 : ℤ) * (normalizedRelatorError .viii_s2) ^ (4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [8, -9, 5, 6] [-9, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1666 [] [6])) (holds_context p21_rule539 [4] []))
  have l0 := holds_refl [8, -9, 5, 6]
  have r0 := holds_refl [4, 3, -7, -9]
  have r1 := holds_trans r0 (holds_context p21_rule1593 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule1703 : Holds ((normalizedRelatorError .i_r8) ^ (16 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (18 : ℤ) * (normalizedRelatorError .i_s6) ^ (11 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-12 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-40 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (29 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-14 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-14 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [6, 9, 5, 8] [7, 8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1672 [6] [])) (holds_context p21_rule200 [] [7, 8, 9]))
  have l0 := holds_refl [6, 9, 5, 8]
  have r0 := holds_refl [7, 8, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1714 : Holds ((normalizedRelatorError .i_r8) ^ (7 : ℤ) * (normalizedRelatorError .i_s1) ^ (-8 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (38 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (32 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-12 : ℤ)) [6, -9, 3, 5] [8, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1680 [3] [])) (holds_context p21_rule198 [] [8, -7, -9]))
  have l0 := holds_refl [3, -9, 3, -5]
  have l1 := holds_trans l0 (holds_context p21_rule1573 [] [])
  have r0 := holds_refl [8, -7, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1721 : Holds ((normalizedRelatorError .i_r8) ^ (-28 : ℤ) * (normalizedRelatorError .i_s2) ^ (8 : ℤ) * (normalizedRelatorError .i_s4) ^ (-14 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (59 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-36 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (17 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (16 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (10 : ℤ) * (normalizedRelatorError .viii_s3) ^ (20 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [4, -5, 9, 4] [6, -5, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1687 [] [8])) (holds_context p21_rule201 [6, -5, 9] []))
  have l0 := holds_refl [-5, 8, 9, 8]
  have l1 := holds_trans l0 (holds_context p21_rule1269 [-5] [])
  have l2 := holds_trans l1 (holds_context p21_rule438 [] [9, 4])
  have r0 := holds_refl [6, -5, 9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1722 : Holds ((normalizedRelatorError .i_r8) ^ (-41 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (-18 : ℤ) * (normalizedRelatorError .i_s6) ^ (-10 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-50 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (20 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (15 : ℤ) * (normalizedRelatorError .viii_s3) ^ (24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [4, 6, 8, 7] [-9, 5, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1691 [8] [])) (holds_context p21_rule201 [] [-9, 5, 9]))
  have l0 := holds_refl [8, 4, 6, 7]
  have l1 := holds_trans l0 (holds_context p21_rule36 [] [6, 7])
  have l2 := holds_trans l1 (holds_context p21_rule223 [4] [7])
  have r0 := holds_refl [-9, 5, 9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1725 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s4) ^ (-6 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-17 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (25 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-12 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (15 : ℤ)) [4, -9, 4, 5] [-9, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1693 [8] [])) (holds_context p21_rule201 [] [-9, 5, 6]))
  have l0 := holds_refl [8, -9, 8, 5]
  have l1 := holds_trans l0 (holds_context p21_rule1259 [] [5])
  have r0 := holds_refl [-9, 5, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1733 : Holds ((normalizedRelatorError .i_r8) ^ (25 : ℤ) * (normalizedRelatorError .i_s1) ^ (7 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (25 : ℤ) * (normalizedRelatorError .i_s6) ^ (16 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-13 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-62 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (34 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (26 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (13 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-25 : ℤ) * (normalizedRelatorError .viii_s2) ^ (5 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-20 : ℤ) * normalizedRelatorError .viii_r3) [3, 9, 6, 8] [5, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1703 [7] [])) (holds_context p21_rule991 [] [8]))
  have l0 := holds_refl [7, 7, 8, 9]
  have l1 := holds_trans l0 (holds_context p21_rule1685 [] [])
  have r0 := holds_refl [3, 9, 6, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1743 : Holds ((normalizedRelatorError .i_r8) ^ (-7 : ℤ) * (normalizedRelatorError .i_s1) ^ (8 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-38 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-32 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (12 : ℤ)) [6, 8, -7, -9] [-9, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1714 [6] [])) (holds_context p21_rule200 [] [-9, 3, 5]))
  have l0 := holds_refl [6, 8, -7, -9]
  have r0 := holds_refl [-9, 3, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1755 : Holds ((normalizedRelatorError .i_r8) ^ (28 : ℤ) * (normalizedRelatorError .i_s2) ^ (-7 : ℤ) * (normalizedRelatorError .i_s4) ^ (14 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-59 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (36 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-17 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-16 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-20 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [4, 6, -5, 9] [-5, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1721 [4] [])) (holds_context p21_rule199 [] [-5, 9, 4]))
  have l0 := holds_refl [4, 6, -5, 9]
  have r0 := holds_refl [-5, 9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1758 : Holds ((normalizedRelatorError .i_r8) ^ (41 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (18 : ℤ) * (normalizedRelatorError .i_s6) ^ (10 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (50 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-20 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-15 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [4, -9, 5, 9] [6, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1722 [4] [])) (holds_context p21_rule199 [] [6, 8, 7]))
  have l0 := holds_refl [4, -9, 5, 9]
  have r0 := holds_refl [6, 8, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1762 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (6 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (6 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (17 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-25 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (12 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-15 : ℤ)) [4, -9, 5, 6] [-9, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1725 [4] [])) (holds_context p21_rule199 [] [-9, 4, 5]))
  have l0 := holds_refl [4, -9, 5, 6]
  have r0 := holds_refl [-9, 4, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1767 : Holds ((normalizedRelatorError .i_r8) ^ (-25 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-25 : ℤ) * (normalizedRelatorError .i_s6) ^ (-16 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (62 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-34 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-26 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-13 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (25 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (11 : ℤ) * (normalizedRelatorError .viii_s3) ^ (20 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 5, 9, 7] [9, 6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1733 [3] [])) (holds_context p21_rule198 [] [9, 6, 8]))
  have l0 := holds_refl [3, 5, 9, 7]
  have r0 := holds_refl [9, 6, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1797 : Holds ((normalizedRelatorError .i_r8) ^ (-28 : ℤ) * (normalizedRelatorError .i_s2) ^ (7 : ℤ) * (normalizedRelatorError .i_s4) ^ (-14 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (59 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-36 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (17 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (16 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (10 : ℤ) * (normalizedRelatorError .viii_s3) ^ (20 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-5, 9, 4, -9] [4, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1755 [] [-9])) (holds_context p21_rule16 [4, 6, -5] []))
  have l0 := holds_refl [-5, 9, 4, -9]
  have r0 := holds_refl [4, 6, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
