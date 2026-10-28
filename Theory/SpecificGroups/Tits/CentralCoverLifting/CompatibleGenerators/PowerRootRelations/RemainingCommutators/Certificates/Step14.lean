module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step13

/-! Central word identities for the remaining normalized commutators, chunk 14.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule2656 : Holds ((normalizedRelatorError .i_r8) ^ (-13 : ℤ) * (normalizedRelatorError .i_s1) ^ (8 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (9 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (15 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [9, -7, 4, 7] [6, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2654 [] [7])) (holds_context rc22_rule13 [6, 4, 9] []))
  have l0 := holds_refl [9, -7, 4, 7]
  have r0 := holds_refl [6, 4, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2657 : Holds ((normalizedRelatorError .i_r8) ^ (-15 : ℤ) * (normalizedRelatorError .i_s1) ^ (9 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (19 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [-7, 4, 7] [5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2656 [-9] [])) (holds_context rc22_rule17 [] [-7, 4, 7]))
  have l0 := holds_refl [-9, 6, 4, 9]
  have l1 := holds_trans l0 (holds_context rc22_rule716 [] [])
  have r0 := holds_refl [-7, 4, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2658 : Holds ((normalizedRelatorError .i_r8) ^ (-14 : ℤ) * (normalizedRelatorError .i_s1) ^ (10 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (12 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (7 : ℤ)) [7, 7, 4, 7] [4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2657 [-7] [])) (holds_context rc22_rule28 [] [4, 7]))
  have l0 := holds_refl [-7, 5, 5, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule630 [] [])
  have l2 := holds_trans l1 (holds_context rc22_rule2291 [-5] [])
  have l3 := holds_trans l2 (holds_context rc22_rule9 [] [4, -7])
  have r0 := holds_refl [7, 7, 4, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2659 : Holds ((normalizedRelatorError .i_r8) ^ (14 : ℤ) * (normalizedRelatorError .i_s1) ^ (-10 : ℤ) * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-7 : ℤ)) [4, 7, 7] [7, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2658 [] [-7])) (holds_context rc22_rule12 [7, 7, 4] []))
  have l0 := holds_refl [4, -7, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [4] [])
  have r0 := holds_refl [7, 7, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2678 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 6, 7] [5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1323 [] [8])) (holds_context rc22_rule201 [3, 6, 7] []))
  have l0 := holds_refl [7, 7, 8, 7, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule2608 [] [8])
  have l2 := holds_trans l1 (holds_context rc22_rule201 [5, 7, 5] [])
  have r0 := holds_refl [3, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2679 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 7, 5, -9] [-7, -9, 6] := by
  have h0 := rc22_rule2508
  have l0 := holds_refl [3, 6, 7, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule2678 [] [-9])
  have r0 := holds_refl [-7, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2681 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [-5, -7, -9, 6] [7, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2679 [-5] [])) (holds_context rc22_rule9 [] [7, 5, -9]))
  have l0 := holds_refl [-5, -7, -9, 6]
  have r0 := holds_refl [7, 5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2682 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 5, -9, 6] [-5, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2681 [] [6])) (holds_context rc22_rule200 [-5, -7, -9] []))
  have l0 := holds_refl [7, 5, -9, 6]
  have r0 := holds_refl [-5, -7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2683 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [-7, -5, -7, -9] [5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2682 [-7] [])) (holds_context rc22_rule13 [] [5, -9, 6]))
  have l0 := holds_refl [-7, -5, -7, -9]
  have r0 := holds_refl [5, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2685 : Holds ((normalizedRelatorError .i_r8) ^ (7 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (7 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-7 : ℤ)) [-7, -5, -7] [7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2683 [] [9])) (holds_context rc22_rule17 [-7, -5, -7] []))
  have l0 := holds_refl [5, -9, 6, 9]
  have l1 := holds_trans l0 (holds_context rc22_rule2480 [] [])
  have r0 := holds_refl [-7, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2702 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [-9, 4, 9, 4, 8] [-9, 8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1328 [8, 7] [])) (holds_context rc22_rule1310 [] [-7, 8]))
  have l0 := holds_refl [8, 7, -5, 7, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule1798 [8] [])
  have l2 := holds_trans l1 (holds_context rc22_rule966 [] [])
  have l3 := holds_trans l2 (holds_context rc22_rule1289 [] [7, 3])
  have l4 := holds_trans l3 (holds_context rc22_rule1349 [] [3])
  have l5 := holds_trans l4 (holds_context rc22_rule2245 [] [3])
  have l6 := holds_trans l5 (holds_context rc22_rule198 [-9, 8, 9] [])
  have r0 := holds_refl [5, -7, 5, -7, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule2318 [5] [8])
  have r2 := holds_trans r1 (holds_context rc22_rule2391 [] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule2703 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [4, 9, 4, 8] [8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2702 [9] [])) (holds_context rc22_rule16 [] [4, 9, 4, 8]))
  have l0 := holds_refl [9, -9, 8, 9]
  have l1 := holds_trans l0 (holds_context rc22_rule16 [] [8, 9])
  have r0 := holds_refl [4, 9, 4, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2704 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [4, 8, 9] [9, 4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2703 [4] [])) (holds_context rc22_rule199 [] [9, 4, 8]))
  have l0 := holds_refl [4, 8, 9]
  have r0 := holds_refl [9, 4, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2705 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [8, 9, 8] [4, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2703 [] [8])) (holds_context rc22_rule201 [4, 9, 4] []))
  have l0 := holds_refl [8, 9, 8]
  have r0 := holds_refl [4, 9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2706 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [9, 4, 8, -9] [4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2704 [] [-9])) (holds_context rc22_rule16 [4, 8] []))
  have l0 := holds_refl [9, 4, 8, -9]
  have r0 := holds_refl [4, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2707 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [4, 8, -9] [-9, 4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2706 [-9] [])) (holds_context rc22_rule17 [] [4, 8, -9]))
  have l0 := holds_refl [-9, 4, 8]
  have r0 := holds_refl [4, 8, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2708 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [8, 9, 4, 8] [4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2704 [8] [])) (holds_context rc22_rule36 [] [8, 9]))
  have l0 := holds_refl [8, 9, 4, 8]
  have r0 := holds_refl [4, 8, 8, 9]
  have r1 := holds_trans r0 (holds_context rc22_rule201 [4] [9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule2709 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [8, 9, 4] [4, 9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2708 [] [8])) (holds_context rc22_rule201 [8, 9, 4] []))
  have l0 := holds_refl [4, 9, 8]
  have r0 := holds_refl [8, 9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2718 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [8, -9, 4, 8] [4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2707 [8] [])) (holds_context rc22_rule36 [] [8, -9]))
  have l0 := holds_refl [8, -9, 4, 8]
  have r0 := holds_refl [4, 8, 8, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule201 [4] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule2719 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [8, -9, 4] [4, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2718 [] [8])) (holds_context rc22_rule201 [8, -9, 4] []))
  have l0 := holds_refl [4, -9, 8]
  have r0 := holds_refl [8, -9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2721 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [6, -9, 4, 8] [10, 4, 10, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2707 [6] [])) (holds_context rc22_rule57 [] [-9]))
  have l0 := holds_refl [6, -9, 4, 8]
  have r0 := holds_refl [10, 4, 10, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2722 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [4, -9, 4, 8] [8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2707 [4] [])) (holds_context rc22_rule199 [] [8, -9]))
  have l0 := holds_refl [4, -9, 4, 8]
  have r0 := holds_refl [8, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2723 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [8, -9, 8] [4, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2722 [] [8])) (holds_context rc22_rule201 [4, -9, 4] []))
  have l0 := holds_refl [8, -9, 8]
  have r0 := holds_refl [4, -9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2741 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-11 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-5 : ℤ)) [-9, 6, 9, 8] [-7, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1328 [] [7, 8])) (holds_context rc22_rule1310 [8, -7] []))
  have l0 := holds_refl [-5, 7, -5, 7, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule2478 [] [8])
  have r0 := holds_refl [8, -7, 5, -7, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule2318 [8] [5])
  have r2 := holds_trans r1 (holds_context rc22_rule2365 [8] [])
  have r3 := holds_trans r2 (holds_context rc22_rule2368 [] [-7])
  have r4 := holds_trans r3 (holds_context rc22_rule33 [7, 3, 8] [])
  have r5 := holds_trans r4 (holds_context rc22_rule1291 [7] [3])
  have r6 := holds_trans r5 (holds_context rc22_rule1319 [7, 7] [])
  have r7 := holds_trans r6 (holds_context rc22_rule204 [] [8, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r7)) (by central_nf)

theorem rc22_rule2742 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (11 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [9, -7, 8, 7] [6, 9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2741 [9] [])) (holds_context rc22_rule16 [] [6, 9, 8]))
  have l0 := holds_refl [9, -7, 8, 7]
  have r0 := holds_refl [6, 9, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2744 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-11 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-5 : ℤ)) [6, 9, 8, -7] [9, -7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2742 [] [-7])) (holds_context rc22_rule12 [9, -7, 8] []))
  have l0 := holds_refl [6, 9, 8, -7]
  have r0 := holds_refl [9, -7, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2774 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 5, 8, -7, 5] [8, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1339 [] [-7])) (holds_context rc22_rule33 [6, 8, 5] []))
  have l0 := holds_refl [7, 8, 7, 5, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule2282 [7, 8] [])
  have l2 := holds_trans l1 (holds_context rc22_rule2311 [7] [])
  have l3 := holds_trans l2 (holds_context rc22_rule2406 [] [5])
  have r0 := holds_refl [6, 8, 5, -7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule1374 [6] [3])
  have r2 := holds_trans r1 (holds_context rc22_rule1665 [] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule2775 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_r3) [-5, 8, -7, -5] [5, 8, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2774 [-5] [])) (holds_context rc22_rule9 [] [5, 8, -7, 5]))
  have l0 := holds_refl [-5, 8, -7, -5]
  have r0 := holds_refl [5, 8, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2776 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-5, 8, -7, 5] [5, 8, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2774 [5] [])) (holds_context rc22_rule203 [] [8, -7, 5]))
  have l0 := holds_refl [5, 8, -7, -5]
  have r0 := holds_refl [-5, 8, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2783 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-9, 8, 9, -7, 3] [-7, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1340 [] [3])) (holds_context rc22_rule198 [-7, 3, 8] []))
  have l0 := holds_refl [7, 8, 7, 7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule2243 [] [3])
  have r0 := holds_refl [-7, 3, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2784 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [8, 9, -7, 3] [2, -5, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2783 [9] [])) (holds_context rc22_rule16 [] [8, 9, -7, 3]))
  have l0 := holds_refl [9, -7, 3, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule735 [] [])
  have r0 := holds_refl [8, 9, -7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2800 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [3, 6, 8] [-7, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1343 [] [6, -7])) (holds_context rc22_rule636 [8, 7] []))
  have l0 := holds_refl [-7, 6, 8, 6, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule280 [-7, 6] [-7])
  have l2 := holds_trans l1 (holds_context rc22_rule200 [-7] [8, -7])
  have r0 := holds_refl [8, 7, 5, -7, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule2282 [8] [5])
  have r2 := holds_trans r1 (holds_context rc22_rule2311 [] [5])
  have r3 := holds_trans r2 (holds_context rc22_rule986 [10] [])
  have r4 := holds_trans r3 (holds_context rc22_rule202 [] [3, 6, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r4))) (by central_nf)

theorem rc22_rule2806 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-5 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [-9, 8, 9, 3, 8] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1343 [] [8, -7])) (holds_context rc22_rule1291 [8, 7] []))
  have l0 := holds_refl [-7, 6, 8, 8, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule201 [-7, 6] [-7])
  have l2 := holds_trans l1 (holds_context rc22_rule1791 [] [])
  have r0 := holds_refl [8, 7, 7, 6, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule1801 [] [8])
  have r2 := holds_trans r1 (holds_context rc22_rule2245 [] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule2807 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-5 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [8, 9, 3, 8] [9, 7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2806 [9] [])) (holds_context rc22_rule16 [] [8, 9, 3, 8]))
  have l0 := holds_refl [9, 7, 6, 7]
  have r0 := holds_refl [8, 9, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2809 : Holds ((normalizedRelatorError .i_r8) ^ (16 : ℤ) * (normalizedRelatorError .i_s1) ^ (-10 : ℤ) * (normalizedRelatorError .i_s2) ^ (8 : ℤ) * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (7 : ℤ) * (normalizedRelatorError .i_s5) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-32 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-20 : ℤ)) [-9, 6, 9, 3] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1343 [8, -7] [])) (holds_context rc22_rule1328 [] [7, 3]))
  have l0 := holds_refl [8, -7, -7, 6, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [8] [6, 8])
  have l2 := holds_trans l1 (holds_context rc22_rule1801 [] [8])
  have l3 := holds_trans l2 (holds_context rc22_rule2245 [] [8])
  have l4 := holds_trans l3 (holds_context rc22_rule2807 [-9] [])
  have l5 := holds_trans l4 (holds_context rc22_rule17 [] [7, 6, 7])
  have r0 := holds_refl [-5, 7, -5, 7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule2478 [] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule2810 : Holds ((normalizedRelatorError .i_r8) ^ (-16 : ℤ) * (normalizedRelatorError .i_s1) ^ (10 : ℤ) * (normalizedRelatorError .i_s2) ^ (-8 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-7 : ℤ) * (normalizedRelatorError .i_s5) ^ (18 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (32 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (20 : ℤ)) [9, 7, 6, 7] [6, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2809 [9] [])) (holds_context rc22_rule16 [] [6, 9, 3]))
  have l0 := holds_refl [9, 7, 6, 7]
  have r0 := holds_refl [6, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2811 : Holds ((normalizedRelatorError .i_r8) ^ (16 : ℤ) * (normalizedRelatorError .i_s1) ^ (-10 : ℤ) * (normalizedRelatorError .i_s2) ^ (8 : ℤ) * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (7 : ℤ) * (normalizedRelatorError .i_s5) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-33 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-20 : ℤ)) [6, 9, -7, 3] [9, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2810 [] [-7])) (holds_context rc22_rule12 [9, 7, 6] []))
  have l0 := holds_refl [6, 9, 3, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule33 [6, 9] [])
  have r0 := holds_refl [9, 7, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2828 : Holds ((normalizedRelatorError .i_r8) ^ (18 : ℤ) * (normalizedRelatorError .i_s1) ^ (-14 : ℤ) * (normalizedRelatorError .i_s2) ^ (12 : ℤ) * (normalizedRelatorError .i_s4) ^ (-11 : ℤ) * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (11 : ℤ) * (normalizedRelatorError .i_s5) ^ (-25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-32 : ℤ)) [6, 9, 3, 8] [8, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1349 [9] [])) (holds_context rc22_rule735 [] [7]))
  have l0 := holds_refl [9, 7, 6, 7, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule2810 [] [8])
  have r0 := holds_refl [2, -5, 3, 2, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule2262 [2] [])
  have r2 := holds_trans r1 (holds_context rc22_rule197 [] [8, 9, 3])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule2829 : Holds ((normalizedRelatorError .i_r8) ^ (-18 : ℤ) * (normalizedRelatorError .i_s1) ^ (14 : ℤ) * (normalizedRelatorError .i_s2) ^ (-12 : ℤ) * (normalizedRelatorError .i_s4) ^ (12 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-11 : ℤ) * (normalizedRelatorError .i_s5) ^ (25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (32 : ℤ)) [6, 8, 9, 3] [9, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2828 [6] [])) (holds_context rc22_rule200 [] [9, 3, 8]))
  have l0 := holds_refl [6, 8, 9, 3]
  have r0 := holds_refl [9, 3, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2830 : Holds ((normalizedRelatorError .i_r8) ^ (18 : ℤ) * (normalizedRelatorError .i_s1) ^ (-13 : ℤ) * (normalizedRelatorError .i_s2) ^ (12 : ℤ) * (normalizedRelatorError .i_s4) ^ (-12 : ℤ) * (normalizedRelatorError .i_s6) ^ (-7 : ℤ) * (normalizedRelatorError .i_s3) ^ (11 : ℤ) * (normalizedRelatorError .i_s5) ^ (-25 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-42 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-32 : ℤ)) [9, 3, 8, 3] [6, 8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2829 [] [3])) (holds_context rc22_rule198 [6, 8, 9] []))
  have l0 := holds_refl [9, 3, 8, 3]
  have r0 := holds_refl [6, 8, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
