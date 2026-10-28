module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Certificates.Step03

/-! Additional kernel-checked central word identities, chunk 4.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p20_rule1980 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (7 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-17 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [7, -9, -5, 3] [3, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1891 [] [3])) (holds_context p20_rule227 [3, -9, 8] []))
  have l0 := holds_refl [7, -9, -5, 3]
  have r0 := holds_refl [3, -9, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule1983 : Holds ((normalizedRelatorError .i_r8) ^ (60 : ℤ) * (normalizedRelatorError .i_s1) ^ (10 : ℤ) * (normalizedRelatorError .i_s2) ^ (-7 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-35 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (13 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (15 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (13 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-28 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-42 : ℤ) * (normalizedRelatorError .viii_r3) ^ (21 : ℤ)) [4, 7, -9, -5] [8, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1891 [4] [])) (holds_context p20_rule1806 [] [3]))
  have l0 := holds_refl [4, 7, -9, -5]
  have r0 := holds_refl [-7, -9, -5, 3]
  have r1 := holds_trans r0 (holds_context p20_rule1437 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p20_rule1990 : Holds ((normalizedRelatorError .i_r8) ^ (-60 : ℤ) * (normalizedRelatorError .i_s1) ^ (-10 : ℤ) * (normalizedRelatorError .i_s2) ^ (8 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (35 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-15 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-13 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s1) ^ (7 : ℤ) * (normalizedRelatorError .viii_s7) ^ (28 : ℤ) * (normalizedRelatorError .viii_s3) ^ (42 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-21 : ℤ)) [10, 4, 10, -9] [7, -9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1897 [] [3])) (holds_context p20_rule1437 [4] []))
  have l0 := holds_refl [3, -9, 8, 3]
  have l1 := holds_trans l0 (holds_context p20_rule1891 [] [])
  have r0 := holds_refl [4, 8, 6, -9]
  have r1 := holds_trans r0 (holds_context p20_rule60 [] [-9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule2055 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 7, -9, 8] [8, 3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1972 [] [6])) (holds_context p20_rule1053 [8] []))
  have l0 := holds_refl [-9, 5, 3, 6]
  have l1 := holds_trans l0 (holds_context p20_rule734 [-9] [])
  have l2 := holds_trans l1 (holds_context p20_rule1979 [] [])
  have r0 := holds_refl [8, 3, 7, -9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule2057 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (15 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, -7, -9, 5] [3, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1974 [8] [])) (holds_context p20_rule230 [] [3, -9, 3]))
  have l0 := holds_refl [8, -7, -9, 5]
  have r0 := holds_refl [3, -9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule2058 : Holds ((normalizedRelatorError .i_r8) ^ (-70 : ℤ) * (normalizedRelatorError .i_s1) ^ (-17 : ℤ) * (normalizedRelatorError .i_s2) ^ (8 : ℤ) * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s3) ^ (5 : ℤ) * (normalizedRelatorError .i_s5) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (60 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (30 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (37 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-13 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-25 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-16 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (8 : ℤ) * (normalizedRelatorError .viii_s1) ^ (8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (32 : ℤ) * (normalizedRelatorError .viii_s3) ^ (48 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-22 : ℤ)) [-7, -9, 5, 6] [7, -9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1974 [] [6])) (holds_context p20_rule607 [8] []))
  have l0 := holds_refl [-7, -9, 5, 6]
  have r0 := holds_refl [8, 4, 6, -9]
  have r1 := holds_trans r0 (holds_context p20_rule36 [] [6, -9])
  have r2 := holds_trans r1 (holds_context p20_rule60 [] [-9])
  have r3 := holds_trans r2 (holds_context p20_rule1990 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem p20_rule2062 : Holds ((normalizedRelatorError .i_r8) ^ (-88 : ℤ) * (normalizedRelatorError .i_s1) ^ (-14 : ℤ) * (normalizedRelatorError .i_s2) ^ (10 : ℤ) * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (6 : ℤ) * (normalizedRelatorError .i_s5) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (55 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (29 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (37 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-18 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-24 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-20 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s1) ^ (10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (40 : ℤ) * (normalizedRelatorError .viii_s3) ^ (60 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-28 : ℤ)) [-7, -9, 3] [4, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1983 [] [5])) (holds_context p20_rule9 [4, 7, -9] []))
  have l0 := holds_refl [8, 6, -9, 5]
  have l1 := holds_trans l0 (holds_context p20_rule1553 [8] [])
  have l2 := holds_trans l1 (holds_context p20_rule1802 [] [])
  have r0 := holds_refl [4, 7, -9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule2124 : Holds ((normalizedRelatorError .i_r8) ^ (60 : ℤ) * (normalizedRelatorError .i_s1) ^ (10 : ℤ) * (normalizedRelatorError .i_s2) ^ (-8 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-35 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (15 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (13 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-28 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-42 : ℤ) * (normalizedRelatorError .viii_r3) ^ (21 : ℤ)) [8, 7, -9, -5] [4, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule2058 [8] [])) (holds_context p20_rule2057 [] [6]))
  have l0 := holds_refl [8, 7, -9, -5]
  have r0 := holds_refl [3, -9, 3, 6]
  have r1 := holds_trans r0 (holds_context p20_rule607 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p20_rule2181 : Holds ((normalizedRelatorError .i_r8) ^ (58 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-9 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (15 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (10 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-26 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-36 : ℤ) * (normalizedRelatorError .viii_r3) ^ (16 : ℤ)) [8, 3, -9, 8] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule2124 [] [3])) (holds_context p20_rule1980 [8] []))
  have l0 := holds_refl [4, 6, -9, 3]
  have l1 := holds_trans l0 (holds_context p20_rule611 [] [])
  have r0 := holds_refl [8, 3, -9, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule2217 : Holds ((normalizedRelatorError .i_r8) ^ (-58 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (6 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (28 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s1) ^ (8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (26 : ℤ) * (normalizedRelatorError .viii_s3) ^ (36 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-16 : ℤ)) [3, -9, 8, 6] [8, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule2181 [] [8])) (holds_context p20_rule230 [8, 3, -9] []))
  have l0 := holds_refl [3, -9, 6, 8]
  have l1 := holds_trans l0 (holds_context p20_rule255 [3, -9] [])
  have r0 := holds_refl [8, 3, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule2249 : Holds ((normalizedRelatorError .i_r8) ^ (58 : ℤ) * (normalizedRelatorError .i_s1) ^ (6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (10 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-26 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-36 : ℤ) * (normalizedRelatorError .viii_r3) ^ (16 : ℤ)) [3, 8, 3, -9] [-9, 8, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule2217 [3] [])) (holds_context p20_rule227 [] [-9, 8, 6]))
  have l0 := holds_refl [3, 8, 3, -9]
  have r0 := holds_refl [-9, 8, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule2270 : Holds ((normalizedRelatorError .i_r8) ^ (-136 : ℤ) * (normalizedRelatorError .i_s1) ^ (-15 : ℤ) * (normalizedRelatorError .i_s2) ^ (19 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (8 : ℤ) * (normalizedRelatorError .i_s3) ^ (12 : ℤ) * (normalizedRelatorError .i_s5) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (69 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-20 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (52 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (17 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-33 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-28 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-27 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (15 : ℤ) * (normalizedRelatorError .viii_s1) ^ (17 : ℤ) * (normalizedRelatorError .viii_s7) ^ (62 : ℤ) * (normalizedRelatorError .viii_s3) ^ (90 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-43 : ℤ)) [-9, 8, 6, -5] [4, 3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule2249 [] [-5])) (holds_context p20_rule1802 [3] []))
  have l0 := holds_refl [-9, 8, 6, -5]
  have r0 := holds_refl [3, -7, -9, 3]
  have r1 := holds_trans r0 (holds_context p20_rule2062 [3] [])
  have r2 := holds_trans r1 (holds_context p20_rule30 [] [7, -9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem p20_rule2391 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 8, 3, 7, -9] [5, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule287 [4] [])) (holds_context p20_rule228 [] [5, 3, 2]))
  have l0 := holds_refl [4, 2, 3, 7, -9]
  have l1 := holds_trans l0 (holds_context p20_rule42 [] [3, 7, -9])
  have r0 := holds_refl [5, 3, 2]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule2393 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, 3, 7, -9] [2, 5, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule2391 [2] [])) (holds_context p20_rule226 [] [8, 3, 7, -9]))
  have l0 := holds_refl [2, 5, 3, 2]
  have r0 := holds_refl [8, 3, 7, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem equation_p20_204 : (normalizedRelatorError .i_r1) ^ (4 : ℤ) * (normalizedRelatorError .i_r8) ^ (-8 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-26 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-2 : ℤ) * normalizedRelatorError .vii_r3 * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ) = 1 := by
  have h0 := c6_rule4322
  have l0 := holds_refl [-5, -9, 7]
  have l1 := holds_trans l0 (holds_context p20_rule470 [-5] [])
  have l2 := holds_trans l1 (holds_context p20_rule9 [] [-9])
  have r0 := holds_refl [-9]
  have hh : Holds ((normalizedRelatorError .i_r1) ^ (4 : ℤ) * (normalizedRelatorError .i_r8) ^ (-8 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-26 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-2 : ℤ) * normalizedRelatorError .vii_r3 * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [-9] [-9] := holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)
  exact holds_cancel hh

theorem equation_p20_4197 : (normalizedRelatorError .i_r8) ^ (-124 : ℤ) * (normalizedRelatorError .i_s1) ^ (-20 : ℤ) * (normalizedRelatorError .i_s2) ^ (13 : ℤ) * (normalizedRelatorError .i_s4) ^ (-14 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (7 : ℤ) * (normalizedRelatorError .i_s5) ^ (-15 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (68 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (25 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-21 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (48 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-34 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-27 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-22 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (13 : ℤ) * (normalizedRelatorError .viii_s1) ^ (12 : ℤ) * (normalizedRelatorError .viii_s7) ^ (54 : ℤ) * (normalizedRelatorError .viii_s3) ^ (84 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-39 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule630 [] [8])) (holds_context p20_rule40 [1, -5, 7] []))
  have l0 := holds_refl [-9, 4, 6, -5, 8]
  have l1 := holds_trans l0 (holds_context p20_rule1979 [] [8])
  have l2 := holds_trans l1 (holds_context p20_rule2055 [] [8])
  have l3 := holds_trans l2 (holds_context p20_rule2393 [] [8])
  have l4 := holds_trans l3 (holds_context p20_rule739 [2, 5] [])
  have l5 := holds_trans l4 (holds_context p20_rule465 [2] [3, 2])
  have l6 := holds_trans l5 (holds_context p20_rule287 [2] [])
  have l7 := holds_trans l6 (holds_context p20_rule226 [] [3, 7, -9])
  have r0 := holds_refl [1, -5, 7, 6, 1]
  have r1 := holds_trans r0 (holds_context p20_rule1380 [] [1])
  have r2 := holds_trans r1 (holds_context p20_rule630 [8] [])
  have r3 := holds_trans r2 (holds_context p20_rule1528 [] [6, -5])
  have r4 := holds_trans r3 (holds_context p20_rule2270 [4] [])
  have r5 := holds_trans r4 (holds_context p20_rule228 [] [3, 7, -9])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-124 : ℤ) * (normalizedRelatorError .i_s1) ^ (-20 : ℤ) * (normalizedRelatorError .i_s2) ^ (13 : ℤ) * (normalizedRelatorError .i_s4) ^ (-14 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (7 : ℤ) * (normalizedRelatorError .i_s5) ^ (-15 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (68 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (25 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-21 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (48 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-34 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-27 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-22 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (13 : ℤ) * (normalizedRelatorError .viii_s1) ^ (12 : ℤ) * (normalizedRelatorError .viii_s7) ^ (54 : ℤ) * (normalizedRelatorError .viii_s3) ^ (84 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-39 : ℤ)) [3, 7, -9] [3, 7, -9] := holds_factor (holds_trans (holds_symm l7) (holds_trans h0 r5)) (by central_nf)
  exact holds_cancel hh

theorem p21_rule8 : Holds ((1 : C)) [5, -5] [] := by
  have h0 := (show Holds 1 [5, -5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [5, -5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule9 : Holds ((1 : C)) [-5, 5] [] := by
  have h0 := (show Holds 1 [-5, 5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-5, 5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule12 : Holds ((1 : C)) [7, -7] [] := by
  have h0 := (show Holds 1 [7, -7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [7, -7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule13 : Holds ((1 : C)) [-7, 7] [] := by
  have h0 := (show Holds 1 [-7, 7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-7, 7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule16 : Holds ((1 : C)) [9, -9] [] := by
  have h0 := (show Holds 1 [9, -9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [9, -9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule17 : Holds ((1 : C)) [-9, 9] [] := by
  have h0 := (show Holds 1 [-9, 9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-9, 9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule20 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ)) [-1] [1] := by
  have h0 := (split [1] [1] (rotate [] [1, 1] source0))
  have l0 := holds_refl [1]
  have r0 := holds_refl [-1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule21 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ)) [-2] [2] := by
  have h0 := (split [2] [2] (rotate [] [2, 2] source1))
  have l0 := holds_refl [2]
  have r0 := holds_refl [-2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule22 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule23 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule24 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ)) [-6] [6] := by
  have h0 := (split [6] [6] (rotate [] [6, 6] source4))
  have l0 := holds_refl [6]
  have r0 := holds_refl [-6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule25 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule26 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ)) [-10] [10] := by
  have h0 := (split [10] [10] (rotate [] [10, 10] source6))
  have l0 := holds_refl [10]
  have r0 := holds_refl [-10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule27 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ)) [-5, -5] [5, 5] := by
  have h0 := (split [5, 5] [5, 5] (rotate [] [5, 5, 5, 5] source7))
  have l0 := holds_refl [5, 5]
  have r0 := holds_refl [-5, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule28 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ)) [-7, -7] [7, 7] := by
  have h0 := (split [7, 7] [7, 7] (rotate [] [7, 7, 7, 7] source8))
  have l0 := holds_refl [7, 7]
  have r0 := holds_refl [-7, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule29 : Holds ((normalizedRelatorError .i_s7) ^ (-1 : ℤ)) [-9, -9] [9, 9] := by
  have h0 := (split [9, 9] [9, 9] (rotate [] [9, 9, 9, 9] source9))
  have l0 := holds_refl [9, 9]
  have r0 := holds_refl [-9, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule30 : Holds (normalizedRelatorError .ii_s1_s2) [3, 4] [4, 3] := by
  have h0 := (split [-3, -4] [3, 4] (rotate [] [-3, -4, 3, 4] source10))
  have l0 := holds_refl [-3, -4]
  have l1 := holds_trans l0 (holds_context p21_rule22 [] [-4])
  have l2 := holds_trans l1 (holds_context p21_rule23 [3] [])
  have r0 := holds_refl [-4, -3]
  have r1 := holds_trans r0 (holds_context p21_rule23 [] [-3])
  have r2 := holds_trans r1 (holds_context p21_rule22 [4] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem p21_rule31 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [-5, 3] [3, -5] := by
  have h0 := (split [-3, -5] [3, 5] (rotate [] [-3, -5, 3, 5] source11))
  have l0 := holds_refl [-3, -5]
  have l1 := holds_trans l0 (holds_context p21_rule22 [] [-5])
  have r0 := holds_refl [-5, -3]
  have r1 := holds_trans r0 (holds_context p21_rule22 [-5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule32 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [5, 3] [3, 5] := by
  have h0 := (split [3, 5] [-3, -5] (rotate [-3, -5] [3, 5] source11))
  have l0 := holds_refl [3, 5]
  have r0 := holds_refl [5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule33 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 3] [3, -7] := by
  have h0 := (split [-3, -7] [3, 7] (rotate [] [-3, -7, 3, 7] source12))
  have l0 := holds_refl [-3, -7]
  have l1 := holds_trans l0 (holds_context p21_rule22 [] [-7])
  have r0 := holds_refl [-7, -3]
  have r1 := holds_trans r0 (holds_context p21_rule22 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule34 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, 3] [3, 7] := by
  have h0 := (split [3, 7] [-3, -7] (rotate [-3, -7] [3, 7] source12))
  have l0 := holds_refl [3, 7]
  have r0 := holds_refl [7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule35 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [6, 4] [4, 6] := by
  have h0 := (split [-4, -6] [4, 6] (rotate [] [-4, -6, 4, 6] source16))
  have l0 := holds_refl [-4, -6]
  have l1 := holds_trans l0 (holds_context p21_rule23 [] [-6])
  have l2 := holds_trans l1 (holds_context p21_rule24 [4] [])
  have r0 := holds_refl [-6, -4]
  have r1 := holds_trans r0 (holds_context p21_rule24 [] [-4])
  have r2 := holds_trans r1 (holds_context p21_rule23 [6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem p21_rule36 : Holds ((normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 4] [4, 8] := by
  have h0 := (split [-4, -8] [4, 8] (rotate [] [-4, -8, 4, 8] source17))
  have l0 := holds_refl [-4, -8]
  have l1 := holds_trans l0 (holds_context p21_rule23 [] [-8])
  have l2 := holds_trans l1 (holds_context p21_rule25 [4] [])
  have r0 := holds_refl [-8, -4]
  have r1 := holds_trans r0 (holds_context p21_rule25 [] [-4])
  have r2 := holds_trans r1 (holds_context p21_rule23 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem p21_rule37 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ)) [10, 1] [1, 4] := by
  have h0 := (split [1, 4] [1, -10] (rotate [] [1, 4, 1, -10] source26))
  have l0 := holds_refl [1, 4]
  have r0 := holds_refl [10, -1]
  have r1 := holds_trans r0 (holds_context p21_rule20 [10] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
