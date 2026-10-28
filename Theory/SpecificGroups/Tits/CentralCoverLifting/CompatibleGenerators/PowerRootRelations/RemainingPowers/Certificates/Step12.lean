module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Certificates.Step11

/-! Additional kernel-checked central word identities, chunk 12.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p21_rule1798 : Holds ((normalizedRelatorError .i_r8) ^ (-41 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-18 : ℤ) * (normalizedRelatorError .i_s6) ^ (-10 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-50 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (20 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (15 : ℤ) * (normalizedRelatorError .viii_s3) ^ (24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [6, 8, 7, -9] [4, -9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1758 [] [-9])) (holds_context p21_rule16 [4, -9, 5] []))
  have l0 := holds_refl [6, 8, 7, -9]
  have r0 := holds_refl [4, -9, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1802 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-17 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (25 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-12 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (15 : ℤ)) [-9, 4, 5, 6] [4, -9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1762 [] [6])) (holds_context p21_rule200 [4, -9, 5] []))
  have l0 := holds_refl [-9, 4, 5, 6]
  have r0 := holds_refl [4, -9, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1807 : Holds ((normalizedRelatorError .i_r8) ^ (23 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (22 : ℤ) * (normalizedRelatorError .i_s6) ^ (16 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-52 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (21 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (26 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (11 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-22 : ℤ) * (normalizedRelatorError .viii_s2) ^ (5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-9 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-5 : ℤ)) [8, 9, 3, 7] [3, 5, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1767 [] [-7])) (holds_context p21_rule12 [3, 5, 9] []))
  have l0 := holds_refl [9, 6, 8, -7]
  have l1 := holds_trans l0 (holds_context p21_rule1222 [] [])
  have r0 := holds_refl [3, 5, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1837 : Holds ((normalizedRelatorError .i_r8) ^ (41 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (19 : ℤ) * (normalizedRelatorError .i_s6) ^ (10 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-42 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (50 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-20 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-15 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [4, 6, -9, 5] [8, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1798 [6] [])) (holds_context p21_rule200 [] [8, 7, -9]))
  have l0 := holds_refl [6, 4, -9, 5]
  have l1 := holds_trans l0 (holds_context p21_rule35 [] [-9, 5])
  have r0 := holds_refl [8, 7, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1844 : Holds ((normalizedRelatorError .i_r8) ^ (11 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-12 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-8 : ℤ) * (normalizedRelatorError .i_s5) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-47 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (59 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-20 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (19 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [4, -5, 9, 8] [9, 3, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1807 [8] [])) (holds_context p21_rule201 [] [9, 3, 7]))
  have l0 := holds_refl [8, 3, 5, 9]
  have l1 := holds_trans l0 (holds_context p21_rule1688 [] [])
  have r0 := holds_refl [9, 3, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1884 : Holds ((normalizedRelatorError .i_r8) ^ (-11 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (13 : ℤ) * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (8 : ℤ) * (normalizedRelatorError .i_s5) ^ (-13 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (47 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-59 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (20 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-19 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-10 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [4, 9, 3, 7] [-5, 9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1844 [4] [])) (holds_context p21_rule199 [] [-5, 9, 8]))
  have l0 := holds_refl [4, 9, 3, 7]
  have r0 := holds_refl [-5, 9, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1885 : Holds ((normalizedRelatorError .i_r8) ^ (-13 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (11 : ℤ) * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s3) ^ (7 : ℤ) * (normalizedRelatorError .i_s5) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (46 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-53 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (20 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-18 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-9 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 8, -7, 6] [4, -5, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1844 [] [8])) (holds_context p21_rule201 [4, -5, 9] []))
  have l0 := holds_refl [9, 3, 7, 8]
  have l1 := holds_trans l0 (holds_context p21_rule396 [9] [])
  have r0 := holds_refl [4, -5, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1930 : Holds ((normalizedRelatorError .i_r8) ^ (11 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-13 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-8 : ℤ) * (normalizedRelatorError .i_s5) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-47 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (59 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-20 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (19 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-5, 9, 8, -7] [4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1884 [] [-7])) (holds_context p21_rule12 [4, 9, 3] []))
  have l0 := holds_refl [-5, 9, 8, -7]
  have r0 := holds_refl [4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1932 : Holds ((normalizedRelatorError .i_r8) ^ (13 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-11 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s3) ^ (-7 : ℤ) * (normalizedRelatorError .i_s5) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-46 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (53 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-20 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (18 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (9 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * normalizedRelatorError .viii_r3) [-9, 4, -5, 9] [8, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1885 [-9] [])) (holds_context p21_rule17 [] [8, -7, 6]))
  have l0 := holds_refl [-9, 4, -5, 9]
  have r0 := holds_refl [8, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1934 : Holds ((normalizedRelatorError .i_r8) ^ (19 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (6 : ℤ) * (normalizedRelatorError .i_s4) ^ (5 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (5 : ℤ) * (normalizedRelatorError .i_s5) ^ (-10 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-10 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [9, 8, 3, 7] [-5, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1885 [6] [])) (holds_context p21_rule1468 [] [6]))
  have l0 := holds_refl [6, 4, -5, 9]
  have l1 := holds_trans l0 (holds_context p21_rule35 [] [-5, 9])
  have l2 := holds_trans l1 (holds_context p21_rule1755 [] [])
  have r0 := holds_refl [9, -7, 8, 6]
  have r1 := holds_trans r0 (holds_context p21_rule223 [9, -7] [])
  have r2 := holds_trans r1 (holds_context p21_rule733 [9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem p21_rule1995 : Holds ((normalizedRelatorError .i_r8) ^ (13 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-12 : ℤ) * (normalizedRelatorError .i_s4) ^ (10 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-7 : ℤ) * (normalizedRelatorError .i_s5) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-44 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (51 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (18 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-8 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * normalizedRelatorError .viii_r3) [-5, 6, 9, -7] [4, 9, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1930 [] [8])) (holds_context p21_rule1274 [-5] []))
  have l0 := holds_refl [4, 9, 3, 8]
  have r0 := holds_refl [-5, 6, 9, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1999 : Holds ((normalizedRelatorError .i_r8) ^ (-13 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (11 : ℤ) * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s3) ^ (7 : ℤ) * (normalizedRelatorError .i_s5) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (46 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-53 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (20 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-18 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-9 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, -7, 6, -9] [-9, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1932 [] [-9])) (holds_context p21_rule16 [-9, 4, -5] []))
  have l0 := holds_refl [8, -7, 6, -9]
  have r0 := holds_refl [-9, 4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2002 : Holds ((normalizedRelatorError .i_r8) ^ (-19 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-6 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-5 : ℤ) * (normalizedRelatorError .i_s5) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [-9, -5, 9, 4] [8, 3, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1934 [-9] [])) (holds_context p21_rule17 [] [8, 3, 7]))
  have l0 := holds_refl [-9, -5, 9, 4]
  have r0 := holds_refl [8, 3, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2059 : Holds ((normalizedRelatorError .i_r8) ^ (-9 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-10 : ℤ) * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-10 : ℤ) * (normalizedRelatorError .i_s3) ^ (-5 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (28 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (37 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-19 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (12 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-7 : ℤ)) [6, -9, 4, 5] [7, 8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1999 [3] [])) (holds_context p21_rule395 [] [-9]))
  have l0 := holds_refl [3, -9, 4, -5]
  have l1 := holds_trans l0 (holds_context p21_rule1577 [] [])
  have r0 := holds_refl [7, 8, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2061 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_r8) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (11 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (8 : ℤ) * (normalizedRelatorError .i_s5) ^ (-13 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (48 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-39 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (33 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-14 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-15 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [8, 3, 7, -9] [1, -5, 7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2002 [] [-9])) (holds_context p21_rule1797 [-9] []))
  have l0 := holds_refl [8, 3, 7, -9]
  have r0 := holds_refl [-9, 4, 6, -5]
  have r1 := holds_trans r0 (holds_context p21_rule602 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule2087 : Holds ((normalizedRelatorError .i_r8) ^ (48 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s2) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (21 : ℤ) * (normalizedRelatorError .i_s6) ^ (22 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-17 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-21 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (43 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (28 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (16 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (46 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-19 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (12 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-18 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-22 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-28 : ℤ) * (normalizedRelatorError .viii_r3) ^ (18 : ℤ)) [7, 8, -9, 6] [8, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2059 [] [6])) (holds_context p21_rule1802 [6] []))
  have l0 := holds_refl [7, 8, -9, 6]
  have r0 := holds_refl [6, 4, -9, 5]
  have r1 := holds_trans r0 (holds_context p21_rule35 [] [-9, 5])
  have r2 := holds_trans r1 (holds_context p21_rule1837 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem p21_rule2105 : Holds ((normalizedRelatorError .i_r8) ^ (-48 : ℤ) * (normalizedRelatorError .i_s1) ^ (7 : ℤ) * (normalizedRelatorError .i_s2) ^ (-5 : ℤ) * (normalizedRelatorError .i_s4) ^ (-20 : ℤ) * (normalizedRelatorError .i_s6) ^ (-22 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (17 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (21 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-43 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-28 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-46 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (19 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-12 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (18 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s1) ^ (8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (22 : ℤ) * (normalizedRelatorError .viii_s3) ^ (28 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-18 : ℤ)) [8, 7, -9, 6] [7, 8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2087 [] [6])) (holds_context p21_rule200 [7, 8, -9] []))
  have l0 := holds_refl [8, 7, -9, 6]
  have r0 := holds_refl [7, 8, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2112 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-10 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (15 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [9, 9, 4, 9, 6] [4, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule74 [-9] [])) (holds_context p21_rule29 [] [4, 9, 6]))
  have l0 := holds_refl [-9, 4, 3, 7, 7]
  have l1 := holds_trans l0 (holds_context p21_rule1487 [] [7])
  have l2 := holds_trans l1 (holds_context p21_rule13 [4, 6, -9] [])
  have r0 := holds_refl [9, 9, 4, 9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule2114 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s3) ^ (26 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [9, 9, 4, 9] [3, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2112 [] [6])) (holds_context p21_rule200 [9, 9, 4, 9] []))
  have l0 := holds_refl [4, 6, -9, 6]
  have l1 := holds_trans l0 (holds_context p21_rule579 [] [])
  have r0 := holds_refl [9, 9, 4, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule2115 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-26 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [3, -9, 3, -9] [9, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2114 [] [-9])) (holds_context p21_rule16 [9, 9, 4] []))
  have l0 := holds_refl [3, -9, 3, -9]
  have r0 := holds_refl [9, 9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2116 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-26 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [-9, 3, -9, 3] [9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2114 [-9] [])) (holds_context p21_rule17 [] [9, 4, 9]))
  have l0 := holds_refl [-9, 3, -9, 3]
  have r0 := holds_refl [9, 4, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2118 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s3) ^ (26 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [3, 9, 9, 4] [-9, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2115 [3] [])) (holds_context p21_rule198 [] [-9, 3, -9]))
  have l0 := holds_refl [3, 9, 9, 4]
  have r0 := holds_refl [-9, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2120 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (11 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-19 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-19 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (5 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [6, 10, 3, 10] [4, 9, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2115 [4] [])) (holds_context p21_rule1021 [] [-9]))
  have l0 := holds_refl [4, 9, 9, 4]
  have r0 := holds_refl [6, -9, 6, -9]
  have r1 := holds_trans r0 (holds_context p21_rule587 [6] [])
  have r2 := holds_trans r1 (holds_context p21_rule593 [6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem p21_rule2122 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s3) ^ (26 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [9, 4, 9, 3] [-9, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2116 [] [3])) (holds_context p21_rule198 [-9, 3, -9] []))
  have l0 := holds_refl [9, 4, 9, 3]
  have r0 := holds_refl [-9, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2124 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-26 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [-9, 3, -9, 4] [3, 9, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2118 [] [4])) (holds_context p21_rule199 [3, 9, 9] []))
  have l0 := holds_refl [-9, 3, -9, 4]
  have r0 := holds_refl [3, 9, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2451 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s5) [1, 7, 1, 7, 7] [3, -7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule460 [3, 1] [])) (holds_context p21_rule87 [] [-7]))
  have l0 := holds_refl [3, 1, 1, -7, 1]
  have l1 := holds_trans l0 (holds_context p21_rule458 [3] [-7, 1])
  have r0 := holds_refl [1, 7, 1, -7, -7]
  have r1 := holds_trans r0 (holds_context p21_rule28 [1, 7, 1] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule2453 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s5) [7, 1, 7, 7] [1, 3, -7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule2451 [1] [])) (holds_context p21_rule458 [] [7, 1, 7, 7]))
  have l0 := holds_refl [1, 3, -7, 1]
  have r0 := holds_refl [7, 1, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule2745 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 10, -9, 7, 6] [10, -9, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule589 [10] [])) (holds_context p21_rule478 [] [-9, 7, 6]))
  have l0 := holds_refl [10, -9, 3, -7]
  have r0 := holds_refl [6, 10, -9, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule2811 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [1, 4, -5, 1, 9] [3, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule615 [10] [])) (holds_context p21_rule202 [] [3, 1, 3]))
  have l0 := holds_refl [10, 1, -5, 1, 9]
  have l1 := holds_trans l0 (holds_context p21_rule37 [] [-5, 1, 9])
  have r0 := holds_refl [3, 1, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule2844 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (24 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s3) ^ (2 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-9, 1, -7, 1, 3] [1, -9, 3, -7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule622 [] [3, 1])) (holds_context p21_rule89 [-9] []))
  have l0 := holds_refl [1, -9, -7, 3, 1]
  have l1 := holds_trans l0 (holds_context p21_rule33 [1, -9] [1])
  have r0 := holds_refl [-9, 1, -7, 1, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule3185 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [7, 1, 8, -7, -9] [6, 5, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule745 [7, 1] [])) (holds_context p21_rule610 [] [8]))
  have l0 := holds_refl [7, 1, 8, -7, -9]
  have r0 := holds_refl [4, 3, -5, 1, 8]
  have r1 := holds_trans r0 (holds_context p21_rule1092 [4] [])
  have r2 := holds_trans r1 (holds_context p21_rule199 [] [6, 5, 1])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem p21_rule3186 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * normalizedRelatorError .vii_s4 * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -5, -7, 1] [1, 8, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule3185 [-7] [])) (holds_context p21_rule13 [] [1, 8, -7, -9]))
  have l0 := holds_refl [-7, 6, 5, 1]
  have l1 := holds_trans l0 (holds_context p21_rule1016 [] [1])
  have r0 := holds_refl [1, 8, -7, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule3200 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-14 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * (normalizedRelatorError .i_s3) ^ (-7 : ℤ) * (normalizedRelatorError .i_s5) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (23 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-12 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (61 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (14 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-8 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (10 : ℤ)) [8, 2, -7, -5, 2] [-9, 3, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule746 [] [-9, -7])) (holds_context p21_rule446 [2, -5, 6] []))
  have l0 := holds_refl [-7, -9, 6, -9, -7]
  have l1 := holds_trans l0 (holds_context p21_rule587 [-7] [-7])
  have l2 := holds_trans l1 (holds_context p21_rule448 [] [6, 9, -7])
  have l3 := holds_trans l2 (holds_context p21_rule1995 [9] [])
  have l4 := holds_trans l3 (holds_context p21_rule2122 [] [8])
  have r0 := holds_refl [2, -5, 6, -7, 2]
  have r1 := holds_trans r0 (holds_context p21_rule362 [2] [2])
  have r2 := holds_trans r1 (holds_context p21_rule942 [2] [2])
  have r3 := holds_trans r2 (holds_context p21_rule41 [] [-7, -5, 2])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r3))) (by central_nf)

theorem p21_rule3332 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-18 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-13 : ℤ) * (normalizedRelatorError .i_s5) ^ (17 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-57 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (40 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-44 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (20 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (17 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .vii_s4 * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [1, 6, -5, 7, 1] [3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule785 [] [8])) (holds_context p21_rule42 [2, 3, 5] []))
  have l0 := holds_refl [8, 3, 7, -9, 8]
  have l1 := holds_trans l0 (holds_context p21_rule2061 [] [8])
  have l2 := holds_trans l1 (holds_context p21_rule1347 [1] [])
  have r0 := holds_refl [2, 3, 5, 4, 2]
  have r1 := holds_trans r0 (holds_context p21_rule439 [2, 3] [2])
  have r2 := holds_trans r1 (holds_context p21_rule30 [2] [5, 2])
  have r3 := holds_trans r2 (holds_context p21_rule41 [] [3, 5, 2])
  have r4 := holds_trans r3 (holds_context p21_rule1342 [] [2])
  have r5 := holds_trans r4 (holds_context p21_rule746 [6] [])
  have r6 := holds_trans r5 (holds_context p21_rule994 [] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r6)) (by central_nf)

theorem p21_rule3333 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-18 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-13 : ℤ) * (normalizedRelatorError .i_s5) ^ (17 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-57 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (40 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-44 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (20 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (17 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .vii_s4 * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [6, -5, 7, 1] [1, 3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule3332 [1] [])) (holds_context p21_rule458 [] [6, -5, 7, 1]))
  have l0 := holds_refl [1, 3, 7, -9]
  have r0 := holds_refl [6, -5, 7, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule3334 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_r8) ^ (-17 : ℤ) * (normalizedRelatorError .i_s1) ^ (17 : ℤ) * (normalizedRelatorError .i_s2) ^ (-13 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-10 : ℤ) * (normalizedRelatorError .i_s5) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-50 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-78 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (30 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-28 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (14 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (22 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (4 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (18 : ℤ)) [1, -5, 7, 1, 6] [-9, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule785 [] [6])) (holds_context p21_rule43 [2, 3, 5] []))
  have l0 := holds_refl [8, 3, 7, -9, 6]
  have l1 := holds_trans l0 (holds_context p21_rule2061 [] [6])
  have r0 := holds_refl [2, 3, 5, 6, 2]
  have r1 := holds_trans r0 (holds_context p21_rule1071 [2] [2])
  have r2 := holds_trans r1 (holds_context p21_rule41 [] [6, -5, 2])
  have r3 := holds_trans r2 (holds_context p21_rule43 [8] [-5, 2])
  have r4 := holds_trans r3 (holds_context p21_rule223 [] [2, -5, 2])
  have r5 := holds_trans r4 (holds_context p21_rule49 [6, 8] [])
  have r6 := holds_trans r5 (holds_context p21_rule1743 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r6)) (by central_nf)

theorem p21_rule3335 : Holds ((normalizedRelatorError .i_r8) ^ (-17 : ℤ) * (normalizedRelatorError .i_s1) ^ (17 : ℤ) * (normalizedRelatorError .i_s2) ^ (-13 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-10 : ℤ) * (normalizedRelatorError .i_s5) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-50 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-78 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (30 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-28 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (14 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (22 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (4 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (18 : ℤ)) [-5, 7, 1, 6] [1, -9, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule3334 [1] [])) (holds_context p21_rule458 [] [-5, 7, 1, 6]))
  have l0 := holds_refl [1, -9, 3, 5]
  have r0 := holds_refl [-5, 7, 1, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule3662 : Holds ((normalizedRelatorError .i_r8) ^ (-25 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-11 : ℤ) * (normalizedRelatorError .i_s4) ^ (-17 : ℤ) * (normalizedRelatorError .i_s6) ^ (-14 : ℤ) * (normalizedRelatorError .i_s3) ^ (-5 : ℤ) * (normalizedRelatorError .i_s5) ^ (6 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (31 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (18 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (40 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-22 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-28 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (8 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-14 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (4 : ℤ) * (normalizedRelatorError .viii_s7) ^ (9 : ℤ) * (normalizedRelatorError .viii_s3) ^ (10 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [4, 3, 8, 9, 9] [-9, 3, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule919 [] [-9])) (holds_context p21_rule833 [8] []))
  have l0 := holds_refl [4, 3, 8, -9, -9]
  have l1 := holds_trans l0 (holds_context p21_rule29 [4, 3, 8] [])
  have r0 := holds_refl [8, 2, -7, -5, 2]
  have r1 := holds_trans r0 (holds_context p21_rule3200 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule3729 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [4, -5, 1, 9, -7] [-7, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule948 [7] [])) (holds_context p21_rule34 [] [1, 7, 7]))
  have l0 := holds_refl [7, 1, -7, 1, -7]
  have l1 := holds_trans l0 (holds_context p21_rule88 [] [-7])
  have l2 := holds_trans l1 (holds_context p21_rule1039 [] [-7])
  have r0 := holds_refl [3, 7, 1, 7, 7]
  have r1 := holds_trans r0 (holds_context p21_rule2453 [3] [])
  have r2 := holds_trans r1 (holds_context p21_rule464 [] [1])
  have r3 := holds_trans r2 (holds_context p21_rule89 [1] [])
  have r4 := holds_trans r3 (holds_context p21_rule458 [] [-7, 1, 3])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r4)) (by central_nf)

theorem p21_rule3730 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [-5, 1, 9, -7] [4, -7, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule3729 [4] [])) (holds_context p21_rule199 [] [-5, 1, 9, -7]))
  have l0 := holds_refl [4, -7, 1, 3]
  have r0 := holds_refl [-5, 1, 9, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
