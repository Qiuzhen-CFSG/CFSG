module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step14

/-! Central word identities for the remaining normalized commutators, chunk 15.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule2831 : Holds ((normalizedRelatorError .i_r8) ^ (-18 : ℤ) * (normalizedRelatorError .i_s1) ^ (13 : ℤ) * (normalizedRelatorError .i_s2) ^ (-12 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-11 : ℤ) * (normalizedRelatorError .i_s5) ^ (25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (32 : ℤ)) [-9, 6, 8, 9] [3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2830 [-9] [])) (holds_context rc22_rule17 [] [3, 8, 3]))
  have l0 := holds_refl [-9, 6, 8, 9]
  have r0 := holds_refl [3, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2832 : Holds ((normalizedRelatorError .i_r8) ^ (18 : ℤ) * (normalizedRelatorError .i_s1) ^ (-13 : ℤ) * (normalizedRelatorError .i_s2) ^ (12 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (11 : ℤ) * (normalizedRelatorError .i_s5) ^ (-25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-32 : ℤ)) [3, 8, 3, -9] [-9, 6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2831 [] [-9])) (holds_context rc22_rule16 [-9, 6, 8] []))
  have l0 := holds_refl [3, 8, 3, -9]
  have r0 := holds_refl [-9, 6, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2833 : Holds ((normalizedRelatorError .i_r8) ^ (-18 : ℤ) * (normalizedRelatorError .i_s1) ^ (14 : ℤ) * (normalizedRelatorError .i_s2) ^ (-12 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-11 : ℤ) * (normalizedRelatorError .i_s5) ^ (25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (32 : ℤ)) [3, -9, 6, 8] [8, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2832 [3] [])) (holds_context rc22_rule198 [] [8, 3, -9]))
  have l0 := holds_refl [3, -9, 6, 8]
  have r0 := holds_refl [8, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2834 : Holds ((normalizedRelatorError .i_r8) ^ (18 : ℤ) * (normalizedRelatorError .i_s1) ^ (-14 : ℤ) * (normalizedRelatorError .i_s2) ^ (12 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (11 : ℤ) * (normalizedRelatorError .i_s5) ^ (-25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-32 : ℤ)) [8, 3, -9, 8] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2833 [] [8])) (holds_context rc22_rule201 [3, -9, 6] []))
  have l0 := holds_refl [8, 3, -9, 8]
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2836 : Holds ((normalizedRelatorError .i_r8) ^ (-18 : ℤ) * (normalizedRelatorError .i_s1) ^ (14 : ℤ) * (normalizedRelatorError .i_s2) ^ (-12 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-11 : ℤ) * (normalizedRelatorError .i_s5) ^ (25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (32 : ℤ)) [8, 3, -9, 6] [3, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2834 [8] [])) (holds_context rc22_rule201 [] [3, -9, 8]))
  have l0 := holds_refl [8, 3, -9, 6]
  have r0 := holds_refl [3, -9, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2858 : Holds ((normalizedRelatorError .i_r8) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 5, 8, 7, -5] [8, 7, 5] := by
  have h0 := rc22_rule1031
  have l0 := holds_refl [3, 8, -5, 7, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule1357 [3] [6])
  have l2 := holds_trans l1 (holds_context rc22_rule33 [] [8, 5, 6])
  have l3 := holds_trans l2 (holds_context rc22_rule2380 [-7] [])
  have l4 := holds_trans l3 (holds_context rc22_rule13 [] [8, 7, 5])
  have r0 := holds_refl [5, 5, 8, 7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2859 : Holds ((normalizedRelatorError .i_r8) ^ (-5 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-5, 8, 7, 5] [5, 8, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2858 [-5] [])) (holds_context rc22_rule9 [] [5, 8, 7, -5]))
  have l0 := holds_refl [-5, 8, 7, 5]
  have r0 := holds_refl [5, 8, 7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2881 : Holds ((normalizedRelatorError .i_r8) ^ (7 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-9, 8, 9, -7, -5] [8, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1362 [] [6])) (holds_context rc22_rule200 [8, 5, 7] []))
  have l0 := holds_refl [-7, 6, 8, -5, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule2285 [-7] [])
  have l2 := holds_trans l1 (holds_context rc22_rule2408 [] [5])
  have l3 := holds_trans l2 (holds_context rc22_rule2550 [] [])
  have r0 := holds_refl [8, 5, 7]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2882 : Holds ((normalizedRelatorError .i_r8) ^ (7 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, 9, -7, -5] [9, 8, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2881 [9] [])) (holds_context rc22_rule16 [] [8, 9, -7, -5]))
  have l0 := holds_refl [9, 8, 5, 7]
  have r0 := holds_refl [8, 9, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2885 : Holds ((normalizedRelatorError .i_r1) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .vi_s1_r1) ^ (4 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ)) [3, 6, 1, 7, 3] [7, 7, 6, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1365 [] [1])) (holds_context rc22_rule39 [1, -7, 6] []))
  have l0 := holds_refl [6, 1, 7, 3, 1]
  have l1 := holds_trans l0 (holds_context rc22_rule1459 [6] [])
  have l2 := holds_trans l1 (holds_context rc22_rule1792 [] [1, -7])
  have r0 := holds_refl [1, -7, 6, 1, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule546 [] [6])
  have r2 := holds_trans r1 (holds_context rc22_rule280 [3, 1, -7] [])
  have r3 := holds_trans r2 (holds_context rc22_rule1365 [3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r3))) (by central_nf)

theorem rc22_rule2927 : Holds ((normalizedRelatorError .i_r8) ^ (5 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [3, 2, 5, 3] [7, 2, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1389 [-7] [])) (holds_context rc22_rule13 [] [3, 2, 5, 3]))
  have l0 := holds_refl [-7, -7, 2, 4, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [] [2, 4, -5])
  have l2 := holds_trans l1 (holds_context rc22_rule2147 [7, 7, 2] [])
  have l3 := holds_trans l2 (holds_context rc22_rule50 [7] [4])
  have r0 := holds_refl [3, 2, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2953 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [2, 9, 3, 2, -5] [-5, 3, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1408 [2] [])) (holds_context rc22_rule197 [] [-5, 3, 4, 9]))
  have l0 := holds_refl [2, 9, 3, 2, -5]
  have r0 := holds_refl [-5, 3, 4, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2954 : Holds ((normalizedRelatorError .i_r8) ^ (-22 : ℤ) * (normalizedRelatorError .i_s1) ^ (17 : ℤ) * (normalizedRelatorError .i_s2) ^ (-15 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-13 : ℤ) * (normalizedRelatorError .i_s5) ^ (30 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (52 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (17 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (12 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (13 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (38 : ℤ)) [-7, 2, 5, 3, 2] [3, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1410 [-7] [])) (holds_context rc22_rule28 [] [6, 8, -9]))
  have l0 := holds_refl [-7, 2, 5, 3, 2]
  have r0 := holds_refl [7, 7, 6, 8, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule2083 [] [])
  have r2 := holds_trans r1 (holds_context rc22_rule2836 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule2955 : Holds ((normalizedRelatorError .i_r8) ^ (22 : ℤ) * (normalizedRelatorError .i_s1) ^ (-17 : ℤ) * (normalizedRelatorError .i_s2) ^ (15 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (13 : ℤ) * (normalizedRelatorError .i_s5) ^ (-30 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-52 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-17 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-12 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-13 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-38 : ℤ)) [7, 3, -9, 8] [2, 5, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2954 [7] [])) (holds_context rc22_rule12 [] [2, 5, 3, 2]))
  have l0 := holds_refl [7, 3, -9, 8]
  have r0 := holds_refl [2, 5, 3, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2962 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [1, 2, 5, 3, 2] [6, 1, 7, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1410 [1] [])) (holds_context rc22_rule1365 [] [-9]))
  have l0 := holds_refl [1, 2, 5, 3, 2]
  have r0 := holds_refl [6, 1, 7, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2968 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [5, 4, -9, -5, -9] [3, 2, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1415 [] [-9])) (holds_context rc22_rule16 [3, 2, 3, 2] []))
  have l0 := holds_refl [4, 5, -9, -5, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule2145 [] [-9, -5, -9])
  have r0 := holds_refl [3, 2, 3, 2]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2969 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 4, -9, -5, 7] [7, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1415 [] [7])) (holds_context rc22_rule47 [3, 2, 3] []))
  have l0 := holds_refl [4, 5, -9, -5, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule2145 [] [-9, -5, 7])
  have r0 := holds_refl [3, 2, 3, 5, 2]
  have r1 := holds_trans r0 (holds_context rc22_rule32 [3, 2] [2])
  have r2 := holds_trans r1 (holds_context rc22_rule2927 [] [2])
  have r3 := holds_trans r2 (holds_context rc22_rule42 [7, 2, 9] [])
  have r4 := holds_trans r3 (holds_context rc22_rule45 [7, 2] [8])
  have r5 := holds_trans r4 (holds_context rc22_rule197 [7] [-9, 8])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r5)) (by central_nf)

theorem rc22_rule2970 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [4, -9, -5, 7] [-5, 7, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2969 [-5] [])) (holds_context rc22_rule9 [] [4, -9, -5, 7]))
  have l0 := holds_refl [-5, 7, -9, 8]
  have r0 := holds_refl [4, -9, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3015 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 2, -9, 3] [2, 7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1484 [5] [])) (holds_context rc22_rule55 [] [5, -9, 3]))
  have l0 := holds_refl [5, 3, 2, 8, 9]
  have l1 := holds_trans l0 (holds_context rc22_rule2161 [] [9])
  have l2 := holds_trans l1 (holds_context rc22_rule17 [2, 7, 3] [])
  have r0 := holds_refl [2, 9, 5, -9, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule52 [] [-9, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule3018 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 2, -9] [2, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3015 [] [3])) (holds_context rc22_rule198 [7, 2, -9] []))
  have l0 := holds_refl [2, 7, 3, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule198 [2, 7] [])
  have r0 := holds_refl [7, 2, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3019 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s3) ^ (-3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-7, 2, 7] [2, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3018 [-7] [])) (holds_context rc22_rule13 [] [2, -9]))
  have l0 := holds_refl [-7, 2, 7]
  have r0 := holds_refl [2, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3020 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s3) ^ (-3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [2, 7, 9] [7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3018 [] [9])) (holds_context rc22_rule17 [7, 2] []))
  have l0 := holds_refl [2, 7, 9]
  have r0 := holds_refl [7, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3022 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [9, 5, -9] [7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3018 [2] [])) (holds_context rc22_rule228 [] [-9]))
  have l0 := holds_refl [2, 2, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule197 [] [7])
  have r0 := holds_refl [9, 5, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3023 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [5, -9] [-9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3022 [-9] [])) (holds_context rc22_rule17 [] [5, -9]))
  have l0 := holds_refl [-9, 7]
  have r0 := holds_refl [5, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3025 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-7, 9, 5] [9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3019 [] [2])) (holds_context rc22_rule228 [-7] []))
  have l0 := holds_refl [2, -9, 2]
  have l1 := holds_trans l0 (holds_context rc22_rule44 [2] [])
  have l2 := holds_trans l1 (holds_context rc22_rule197 [] [9])
  have r0 := holds_refl [-7, 9, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3026 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-7, 9] [9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3025 [] [-5])) (holds_context rc22_rule8 [-7, 9] []))
  have l0 := holds_refl [9, -5]
  have r0 := holds_refl [-7, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3027 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, -9, 7] [-9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3019 [2] [])) (holds_context rc22_rule229 [] [7]))
  have l0 := holds_refl [2, 2, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule197 [] [-9])
  have r0 := holds_refl [-5, -9, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3028 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, -9] [-9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3027 [] [-7])) (holds_context rc22_rule12 [-5, -9] []))
  have l0 := holds_refl [-9, -7]
  have r0 := holds_refl [-5, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3029 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [7, 9] [9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3020 [2] [])) (holds_context rc22_rule197 [] [7, 9]))
  have l0 := holds_refl [2, 7, 2]
  have l1 := holds_trans l0 (holds_context rc22_rule228 [] [])
  have r0 := holds_refl [7, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3030 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [5, 9, 9] [-9, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3023 [] [-9])) (holds_context rc22_rule29 [5] []))
  have l0 := holds_refl [-9, 7, -9]
  have r0 := holds_refl [5, 9, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3034 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 9, -5] [-7, 3, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3026 [3] [])) (holds_context rc22_rule33 [] [9]))
  have l0 := holds_refl [3, 9, -5]
  have r0 := holds_refl [-7, 3, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3036 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, 9, 9] [-9, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3028 [] [-9])) (holds_context rc22_rule29 [-5] []))
  have l0 := holds_refl [-9, -7, -9]
  have r0 := holds_refl [-5, 9, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3037 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, -9, -7] [-5, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3028 [3] [])) (holds_context rc22_rule31 [] [-9]))
  have l0 := holds_refl [3, -9, -7]
  have r0 := holds_refl [-5, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3046 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-9, 5, 7, -5] [-5, 3, -9] := by
  have h0 := rc22_rule720
  have l0 := holds_refl [5, -9, 6, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule3023 [] [6, 4])
  have l2 := holds_trans l1 (holds_context rc22_rule2344 [-9] [])
  have r0 := holds_refl [-5, 3, -9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3047 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (13 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [-9, 7, 7, 6] [3, -9, 4] := by
  have h0 := rc22_rule724
  have l0 := holds_refl [5, 5, -9, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule3023 [5] [6])
  have l2 := holds_trans l1 (holds_context rc22_rule3023 [] [7, 6])
  have r0 := holds_refl [3, -9, 4]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3050 : Holds ((normalizedRelatorError .i_r8) ^ (11 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (6 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (5 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (12 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-21 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [-7, -9, 7, 6] [-5, 7, -9] := by
  have h0 := rc22_rule2489
  have l0 := holds_refl [-7, 5, -9, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule3023 [-7] [6])
  have r0 := holds_refl [-5, 7, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3051 : Holds ((normalizedRelatorError .i_r8) ^ (11 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (6 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (5 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (12 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-21 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [5, -7, -9, 7] [7, -9, 6] := by
  have h0 := rc22_rule2495
  have l0 := holds_refl [5, -7, 5, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule3023 [5, -7] [])
  have r0 := holds_refl [7, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3055 : Holds ((normalizedRelatorError .i_r8) ^ (-16 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-6 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-17 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (26 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [3, 8, -9, -7] [-9, 4, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3023 [4, 8] [])) (holds_context rc22_rule383 [] [-9]))
  have l0 := holds_refl [4, 8, -9, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule2707 [] [7])
  have r0 := holds_refl [3, 8, -5, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule3028 [3, 8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule3076 : Holds ((normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 6, 9, -5] [5, -7, 5, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3026 [3, 6] [])) (holds_context rc22_rule636 [] [9]))
  have l0 := holds_refl [3, 6, 9, -5]
  have r0 := holds_refl [5, -7, 5, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3079 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * normalizedRelatorError .viii_r3) [8, 5, 9, -5] [7, 8, -5, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3026 [8, 5] [])) (holds_context rc22_rule1374 [] [9]))
  have l0 := holds_refl [8, 5, 9, -5]
  have r0 := holds_refl [7, 8, -5, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
