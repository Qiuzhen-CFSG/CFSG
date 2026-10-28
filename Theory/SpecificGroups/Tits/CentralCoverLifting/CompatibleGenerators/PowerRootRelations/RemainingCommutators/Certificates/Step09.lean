module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step08

/-! Central word identities for the remaining normalized commutators, chunk 9.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule1435 : Holds ((normalizedRelatorError .i_r1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (3 : ℤ)) [3, 1, 7, 7, 1] [7, 1, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule541 [1, -7] [])) (holds_context rc22_rule541 [] [-7, 1]))
  have l0 := holds_refl [1, -7, 3, 1, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule1430 [] [-7])
  have l2 := holds_trans l1 (holds_context rc22_rule33 [-7, 3, 1] [])
  have l3 := holds_trans l2 (holds_context rc22_rule542 [-7] [])
  have l4 := holds_trans l3 (holds_context rc22_rule28 [] [1, 3, 1])
  have l5 := holds_trans l4 (holds_context rc22_rule548 [7, 7] [])
  have l6 := holds_trans l5 (holds_context rc22_rule12 [7] [1, 7])
  have r0 := holds_refl [3, 1, -7, -7, 1]
  have r1 := holds_trans r0 (holds_context rc22_rule28 [3, 1] [1])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule1436 : Holds ((normalizedRelatorError .i_r1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ)) [3, 1, 7, 7] [7, 7, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1435 [] [1])) (holds_context rc22_rule196 [3, 1, 7, 7] []))
  have l0 := holds_refl [7, 1, 7, 1]
  have l1 := holds_trans l0 (holds_context rc22_rule557 [7] [])
  have r0 := holds_refl [3, 1, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1438 : Holds ((normalizedRelatorError .i_r1) ^ (5 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [7, 7, 1, 7, 7] [3, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule542 [] [7])) (holds_context rc22_rule34 [3, 1, -7] []))
  have l0 := holds_refl [-7, 1, 3, 1, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule548 [-7] [7])
  have l2 := holds_trans l1 (holds_context rc22_rule28 [] [1, 7, 7])
  have r0 := holds_refl [3, 1, -7, 7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule13 [3, 1] [3])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1440 : Holds ((normalizedRelatorError .i_r1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ) * normalizedRelatorError .vii_s5) [3, 1, 7, 3] [7, 7, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1438 [] [7])) (holds_context rc22_rule204 [7, 7, 1] []))
  have l0 := holds_refl [3, 1, 3, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [3, 1] [])
  have r0 := holds_refl [7, 7, 1, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1458 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s5) [1, 7, 3, 1, -7] [3, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule549 [1] [])) (holds_context rc22_rule541 [] [7, 3]))
  have l0 := holds_refl [1, 7, 3, 1, -7]
  have r0 := holds_refl [3, 1, -7, 7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule13 [3, 1] [3])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1459 : Holds ((normalizedRelatorError .i_r1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (3 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ)) [1, 7, 3, 1] [7, 7, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1458 [] [7])) (holds_context rc22_rule13 [1, 7, 3, 1] []))
  have l0 := holds_refl [3, 1, 3, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [3, 1] [])
  have l2 := holds_trans l1 (holds_context rc22_rule1440 [] [])
  have r0 := holds_refl [1, 7, 3, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1464 : Holds ((normalizedRelatorError .i_r1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ)) [7, 1, -7, 3, 4] [5, 1, -9, -7, 5] := by
  have h0 := rc22_rule194
  have l0 := holds_refl [3, 1, 3, 10, 1]
  have l1 := holds_trans l0 (holds_context rc22_rule552 [3] [])
  have l2 := holds_trans l1 (holds_context rc22_rule33 [] [1, 7, 4])
  have l3 := holds_trans l2 (holds_context rc22_rule558 [] [4])
  have r0 := holds_refl [5, 1, -9, -7, 5]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1469 : Holds ((normalizedRelatorError .i_r1) ^ (5 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [7, 7, 1, -7, 3] [3, 1, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule557 [1, 3] [])) (holds_context rc22_rule548 [] [7, 1]))
  have l0 := holds_refl [1, 3, 7, 1, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [1] [1, 3])
  have l2 := holds_trans l1 (holds_context rc22_rule1459 [] [3])
  have r0 := holds_refl [-7, 1, 7, 7, 1]
  have r1 := holds_trans r0 (holds_context rc22_rule559 [] [1])
  have r2 := holds_trans r1 (holds_context rc22_rule548 [7, 3] [])
  have r3 := holds_trans r2 (holds_context rc22_rule33 [7] [1, 7])
  have r4 := holds_trans r3 (holds_context rc22_rule12 [] [3, 1, 7])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r4)) (by central_nf)

theorem rc22_rule1484 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ)) [2, -7, 5, -9, 3] [3, 2, 8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule564 [-5] [])) (holds_context rc22_rule9 [] [3, 2, 8, 9]))
  have l0 := holds_refl [-5, 7, 2, -9, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule223 [] [-9, 3])
  have r0 := holds_refl [3, 2, 8, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1544 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ)) [6, 9, 5, 8] [-7, 5, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule589 [2] [])) (holds_context rc22_rule354 [] [8]))
  have l0 := holds_refl [2, -5, 7, 5, 2]
  have l1 := holds_trans l0 (holds_context rc22_rule759 [] [])
  have r0 := holds_refl [6, 9, 5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1579 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [9, 6, 7, 7, 4] [4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule610 [] [4])) (holds_context rc22_rule199 [4, 9, 3] []))
  have l0 := holds_refl [9, 6, 7, 7, 4]
  have r0 := holds_refl [4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1580 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [6, 7, 7, 4] [-9, 4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1579 [-9] [])) (holds_context rc22_rule17 [] [6, 7, 7, 4]))
  have l0 := holds_refl [-9, 4, 9, 3]
  have r0 := holds_refl [6, 7, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1665 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [6, 7, 8, -5, 3] [8, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule642 [] [3])) (holds_context rc22_rule198 [8, -7, -5] []))
  have l0 := holds_refl [6, 8, 5, -7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule1374 [6] [3])
  have r0 := holds_refl [8, -7, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1681 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-13 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-9 : ℤ)) [4, 8, -9, 4, 9] [7, 8, -7] := by
  have h0 := rc22_rule434
  have l0 := holds_refl [8, 7, 7, 3, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule1317 [] [6])
  have l2 := holds_trans l1 (holds_context rc22_rule1364 [] [6])
  have l3 := holds_trans l2 (holds_context rc22_rule280 [7, 7, 3] [])
  have l4 := holds_trans l3 (holds_context rc22_rule648 [7] [8])
  have l5 := holds_trans l4 (holds_context rc22_rule1301 [7, -5] [])
  have l6 := holds_trans l5 (holds_context rc22_rule9 [7] [8, -7])
  have r0 := holds_refl [4, 8, -9, 4, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1682 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-13 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-9 : ℤ)) [4, 8, -9, 4] [7, 8, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1681 [] [-9])) (holds_context rc22_rule16 [4, 8, -9, 4] []))
  have l0 := holds_refl [7, 8, -7, -9]
  have r0 := holds_refl [4, 8, -9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1697 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, 5, 6, 4, -5] [7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule648 [] [-7, -5])) (holds_context rc22_rule618 [7, 3] []))
  have l0 := holds_refl [-5, 7, -5, -7, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule1346 [] [-5])
  have r0 := holds_refl [7, 3, 5, -7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule32 [7] [-7, 3])
  have r2 := holds_trans r1 (holds_context rc22_rule33 [7, 5] [3])
  have r3 := holds_trans r2 (holds_context rc22_rule198 [7, 5, -7] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule1744 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ)) [7, 5, 5, 4, -7] [5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule656 [6, 7] [])) (holds_context rc22_rule469 [] [3]))
  have l0 := holds_refl [6, 7, 5, -7, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule673 [6] [])
  have l2 := holds_trans l1 (holds_context rc22_rule591 [] [-5, -7])
  have l3 := holds_trans l2 (holds_context rc22_rule27 [7, 4] [-7])
  have l4 := holds_trans l3 (holds_context rc22_rule377 [7] [-7])
  have r0 := holds_refl [7, 6, -7, 6, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule653 [7, 6, -7] [])
  have r2 := holds_trans r1 (holds_context rc22_rule656 [7] [6])
  have r3 := holds_trans r2 (holds_context rc22_rule673 [] [6])
  have r4 := holds_trans r3 (holds_context rc22_rule1346 [] [6])
  have r5 := holds_trans r4 (holds_context rc22_rule35 [5, 5, 6] [])
  have r6 := holds_trans r5 (holds_context rc22_rule200 [5, 5] [4])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r6)) (by central_nf)

theorem rc22_rule1745 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ)) [7, 5, 5, 4] [5, 5, 4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1744 [] [7])) (holds_context rc22_rule13 [7, 5, 5, 4] []))
  have l0 := holds_refl [5, 5, 4, 7]
  have r0 := holds_refl [7, 5, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1760 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 8, 7, 5, -7] [8, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule658 [] [5, -7])) (holds_context rc22_rule624 [8, 3] []))
  have l0 := holds_refl [6, 8, 3, 5, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule1319 [] [5, -7])
  have r0 := holds_refl [8, 3, -7, -5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule33 [8] [-5, 3])
  have r2 := holds_trans r1 (holds_context rc22_rule1296 [] [-5, 3])
  have r3 := holds_trans r2 (holds_context rc22_rule1665 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule1761 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [8, 7, 5, -7] [-7, 8, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1760 [-7] [])) (holds_context rc22_rule13 [] [8, 7, 5, -7]))
  have l0 := holds_refl [-7, 8, -7, -5]
  have r0 := holds_refl [8, 7, 5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1769 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2) [3, -9, 4, 9, 4] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule660 [] [3])) (holds_context rc22_rule71 [3] []))
  have l0 := holds_refl [5, -7, 5, -7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule680 [] [3])
  have l2 := holds_trans l1 (holds_context rc22_rule30 [-9, 4, 9] [])
  have l3 := holds_trans l2 (holds_context rc22_rule610 [-9] [])
  have l4 := holds_trans l3 (holds_context rc22_rule17 [] [6, 7, 7])
  have r0 := holds_refl [3, -9, 4, 9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1770 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ)) [3, -9, 4, 9] [-9, 4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1769 [] [4])) (holds_context rc22_rule199 [3, -9, 4, 9] []))
  have l0 := holds_refl [6, 7, 7, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule1580 [] [])
  have r0 := holds_refl [3, -9, 4, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1772 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-5, 7, -5, 7, 7] [-7, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule660 [7] [])) (holds_context rc22_rule648 [] [7, 7]))
  have l0 := holds_refl [7, 5, -7, 5, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule673 [] [-7])
  have l2 := holds_trans l1 (holds_context rc22_rule1346 [] [-7])
  have l3 := holds_trans l2 (holds_context rc22_rule474 [] [])
  have r0 := holds_refl [-5, 7, -5, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1773 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, -5, 7, 7] [5, -7, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1772 [5] [])) (holds_context rc22_rule8 [] [7, -5, 7, 7]))
  have l0 := holds_refl [5, -7, 3, 6]
  have r0 := holds_refl [7, -5, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1778 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, -5, 7, 7, 6] [6, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule663 [] [6])) (holds_context rc22_rule648 [6, 5] []))
  have l0 := holds_refl [-7, -5, 7, 7, 6]
  have r0 := holds_refl [6, 5, -5, 7, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule8 [6] [7, -5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1789 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 7, 6, 7, 7] [5, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule668 [] [-7])) (holds_context rc22_rule33 [7, -5, -7] []))
  have l0 := holds_refl [5, 7, 6, -7, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [5, 7, 6] [])
  have r0 := holds_refl [7, -5, -7, -7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule28 [7, -5] [3])
  have r2 := holds_trans r1 (holds_context rc22_rule1773 [] [3])
  have r3 := holds_trans r2 (holds_context rc22_rule653 [5, -7, 3] [])
  have r4 := holds_trans r3 (holds_context rc22_rule198 [5, -7] [6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r4)) (by central_nf)

theorem rc22_rule1790 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 7, 7] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1789 [-5] [])) (holds_context rc22_rule9 [] [7, 6, 7, 7]))
  have l0 := holds_refl [-5, 5, -7, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule9 [] [-7, 6])
  have r0 := holds_refl [7, 6, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1791 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, -7] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1790 [] [-7])) (holds_context rc22_rule12 [7, 6, 7] []))
  have l0 := holds_refl [-7, 6, -7]
  have r0 := holds_refl [7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1792 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 7, 7] [7, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1790 [-7] [])) (holds_context rc22_rule13 [] [6, 7, 7]))
  have l0 := holds_refl [-7, -7, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [] [6])
  have r0 := holds_refl [6, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1793 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 7, 6, 7] [6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1791 [7] [])) (holds_context rc22_rule12 [] [6, -7]))
  have l0 := holds_refl [7, 7, 6, 7]
  have r0 := holds_refl [6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1794 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, 7] [7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1793 [7] [])) (holds_context rc22_rule204 [] [6, 7]))
  have l0 := holds_refl [7, 6, -7]
  have r0 := holds_refl [-7, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1795 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 7, 6, -7] [6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1791 [-7] [])) (holds_context rc22_rule28 [] [6, -7]))
  have l0 := holds_refl [-7, 7, 6, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule13 [] [6, 7])
  have r0 := holds_refl [7, 7, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1796 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, -7, 5] [-5, 7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1791 [3] [])) (holds_context rc22_rule33 [] [6, -7]))
  have l0 := holds_refl [3, 7, 6, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [] [6, 7])
  have l2 := holds_trans l1 (holds_context rc22_rule648 [] [7])
  have r0 := holds_refl [-7, 3, 6, -7]
  have r1 := holds_trans r0 (holds_context rc22_rule636 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule1798 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, -5, 7, -5] [-9, 4, 9, 4] := by
  have h0 := rc22_rule71
  have l0 := holds_refl [6, 7, 7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule1792 [] [3])
  have l2 := holds_trans l1 (holds_context rc22_rule653 [7, 7] [])
  have l3 := holds_trans l2 (holds_context rc22_rule648 [7] [])
  have r0 := holds_refl [-9, 4, 9, 4]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1799 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 7, 6, 4] [-9, 4, 9, 3] := by
  have h0 := rc22_rule1580
  have l0 := holds_refl [6, 7, 7, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule1792 [] [4])
  have r0 := holds_refl [-9, 4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1800 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s5_s4) [6, 4, 7, 7] [-9, 4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1792 [4] [])) (holds_context rc22_rule35 [] [7, 7]))
  have l0 := holds_refl [4, 7, 7, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule1023 [] [])
  have l2 := holds_trans l1 (holds_context rc22_rule1770 [] [])
  have r0 := holds_refl [6, 4, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1801 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (5 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [8, 7, 7, 6] [7, 6, 7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1792 [8] [])) (holds_context rc22_rule280 [] [7, 7]))
  have l0 := holds_refl [8, 7, 7, 6]
  have r0 := holds_refl [6, 8, 7, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule1289 [] [7])
  have r2 := holds_trans r1 (holds_context rc22_rule1349 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule1803 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-7, 3, 6, 8] [7, 7, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1793 [] [8, 3])) (holds_context rc22_rule1321 [7, 7] []))
  have l0 := holds_refl [6, -7, 8, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule1372 [] [])
  have r0 := holds_refl [7, 7, 8, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1810 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, -5, -7] [-7, -5, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1795 [-7, -5] [])) (holds_context rc22_rule1778 [] [-7]))
  have l0 := holds_refl [-7, -5, 6, 7]
  have r0 := holds_refl [6, 7, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1832 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * normalizedRelatorError .iv_s2_s8 * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 10, 4, 10, -5] [8, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule675 [7] [])) (holds_context rc22_rule648 [] [8, 5]))
  have l0 := holds_refl [7, 10, 4, 10, -5]
  have r0 := holds_refl [-5, 7, -5, 8, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule1301 [-5] [5])
  have r2 := holds_trans r1 (holds_context rc22_rule9 [] [8, -7, 5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
