module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Certificates.Step01

/-! Additional kernel-checked central word identities, chunk 2.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p20_rule688 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [5, 6, 5] [4, 3, 6] := by
  have h0 := c9_rule1250
  have l0 := holds_refl [6, -7, 5, 5, 7]
  have l1 := holds_trans l0 (holds_context p20_rule480 [] [5, 7])
  have l2 := holds_trans l1 (holds_context p20_rule425 [4] [7])
  have l3 := holds_trans l2 (holds_context p20_rule432 [4, 8] [])
  have l4 := holds_trans l3 (holds_context p20_rule230 [4] [3, 6])
  have r0 := holds_refl [5, 6, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule714 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ)) [-5, 3, 6] [4, 6, 5] := by
  have h0 := c9_rule2416
  have l0 := holds_refl [3, -5, 6]
  have l1 := holds_trans l0 (holds_context p20_rule31 [] [6])
  have r0 := holds_refl [6, 4, 5]
  have r1 := holds_trans r0 (holds_context p20_rule35 [] [5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem p20_rule718 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-11 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ)) [3, 6, 7] [5, 7, 5] := by
  have h0 := c9_rule2497
  have l0 := holds_refl [5, 7, 5]
  have r0 := holds_refl [6, 3, 7]
  have r1 := holds_trans r0 (holds_context p20_rule305 [] [7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule721 : Holds ((normalizedRelatorError .i_s1) ^ (-8 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-15 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (29 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-10 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (14 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 5, -9, 6] [-5, -7, -9] := by
  have h0 := c9_rule2595
  have l0 := holds_refl [7, -9, 7, 6]
  have l1 := holds_trans l0 (holds_context p20_rule470 [7] [6])
  have r0 := holds_refl [-5, -7, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule726 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [8, -5, -9, 6] [-9, 8, -7] := by
  have h0 := c9_rule2679
  have l0 := holds_refl [-7, -9, -5, 7]
  have l1 := holds_trans l0 (holds_context p20_rule681 [] [])
  have r0 := holds_refl [-9, 8, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule727 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-9, 8, 7, 7] [-7, -9, -5] := by
  have h0 := c9_rule2681
  have l0 := holds_refl [-9, 8, 7, 7]
  have r0 := holds_refl [-7, -9, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule734 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * normalizedRelatorError .viii_r3) [5, 3, 6] [4, 6, -5] := by
  have h0 := c10_rule1044
  have l0 := holds_refl [3, -7, 6, 7, 5]
  have l1 := holds_trans l0 (holds_context p20_rule453 [3] [5])
  have l2 := holds_trans l1 (holds_context p20_rule394 [] [-7, 5])
  have l3 := holds_trans l2 (holds_context p20_rule429 [] [-7, 5])
  have l4 := holds_trans l3 (holds_context p20_rule423 [8] [5])
  have l5 := holds_trans l4 (holds_context p20_rule258 [] [6, 5])
  have l6 := holds_trans l5 (holds_context p20_rule688 [4, 5] [])
  have l7 := holds_trans l6 (holds_context p20_rule465 [4] [3, 6])
  have l8 := holds_trans l7 (holds_context p20_rule228 [] [5, 3, 6])
  have r0 := holds_refl [4, 6, -5]
  exact holds_factor (holds_trans (holds_symm l8) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule737 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 4, 3] [3, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule33 [] [4])) (holds_context p20_rule30 [-7] []))
  have l0 := holds_refl [3, -7, 4]
  have r0 := holds_refl [-7, 4, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule739 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ)) [3, 2, 8] [4, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule42 [3] [])) (holds_context p20_rule30 [] [2]))
  have l0 := holds_refl [3, 2, 8]
  have r0 := holds_refl [4, 3, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule766 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 4, -5, 2] [8, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule49 [8] [])) (holds_context p20_rule41 [] [-5, 2]))
  have l0 := holds_refl [8, -7, -9]
  have r0 := holds_refl [2, 4, -5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule805 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-9, 3, 8, 3] [8, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule285 [-9] [])) (holds_context p20_rule17 [] [8, -9, 6]))
  have l0 := holds_refl [-9, 3, 8, 3]
  have r0 := holds_refl [8, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule807 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-12 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (9 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [-5, -9, 6, 7] [8, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule286 [-9] [])) (holds_context p20_rule17 [] [8, -9, 8]))
  have l0 := holds_refl [-9, -7, 6, 7]
  have l1 := holds_trans l0 (holds_context p20_rule469 [] [6, 7])
  have r0 := holds_refl [8, -9, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule835 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .vii_s4) [1, 7, 4, -5] [8, 1, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule339 [1] [])) (holds_context p20_rule39 [] [-5, 7]))
  have l0 := holds_refl [1, 7, 4, -5]
  have r0 := holds_refl [8, 1, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule843 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [7, 2, 4, -5] [2, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule365 [7, 2] [])) (holds_context p20_rule50 [] [4]))
  have l0 := holds_refl [7, 2, 4, -5]
  have r0 := holds_refl [2, 9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule873 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ)) [4, 3, -7, -5] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule393 [] [-7])) (holds_context p20_rule12 [-7, 5] []))
  have l0 := holds_refl [-5, 3, 6, -7]
  have l1 := holds_trans l0 (holds_context p20_rule714 [] [-7])
  have l2 := holds_trans l1 (holds_context p20_rule514 [4] [])
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule874 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ)) [3, -7, -5] [4, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule873 [4] [])) (holds_context p20_rule228 [] [3, -7, -5]))
  have l0 := holds_refl [4, -7, 5]
  have r0 := holds_refl [3, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule889 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [8, 7, 8, 3] [6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule397 [] [3])) (holds_context p20_rule33 [3, 6] []))
  have l0 := holds_refl [5, -7, 5, 3]
  have l1 := holds_trans l0 (holds_context p20_rule425 [] [3])
  have r0 := holds_refl [3, 6, 3, -7]
  have r1 := holds_trans r0 (holds_context p20_rule305 [3] [-7])
  have r2 := holds_trans r1 (holds_context p20_rule227 [] [6, -7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem p20_rule890 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 8, 3] [8, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule889 [8] [])) (holds_context p20_rule230 [] [7, 8, 3]))
  have l0 := holds_refl [8, 6, -7]
  have r0 := holds_refl [7, 8, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule907 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [3, 8, 7, 8] [6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule425 [3] [])) (holds_context p20_rule32 [] [-7, 5]))
  have l0 := holds_refl [3, 8, 7, 8]
  have r0 := holds_refl [5, 3, -7, 5]
  have r1 := holds_trans r0 (holds_context p20_rule396 [5] [])
  have r2 := holds_trans r1 (holds_context p20_rule8 [] [6, -7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem p20_rule908 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [6, -7, 8] [3, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule907 [] [8])) (holds_context p20_rule230 [3, 8, 7] []))
  have l0 := holds_refl [6, -7, 8]
  have r0 := holds_refl [3, 8, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule932 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (19 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-5, 3, -7, 4] [5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule446 [] [3])) (holds_context p20_rule305 [-7, -5] []))
  have l0 := holds_refl [-5, -7, 4, 3]
  have l1 := holds_trans l0 (holds_context p20_rule737 [-5] [])
  have r0 := holds_refl [-7, -5, 3, 6]
  have r1 := holds_trans r0 (holds_context p20_rule499 [] [6])
  have r2 := holds_trans r1 (holds_context p20_rule874 [] [6])
  have r3 := holds_trans r2 (holds_context p20_rule508 [4] [])
  have r4 := holds_trans r3 (holds_context p20_rule228 [] [5, -7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r4)) (by central_nf)

theorem p20_rule933 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (19 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, -7, 4] [5, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule932 [5] [])) (holds_context p20_rule8 [] [3, -7, 4]))
  have l0 := holds_refl [5, 5, -7]
  have r0 := holds_refl [3, -7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule939 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (18 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 7, 4, -7] [5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule456 [] [3])) (holds_context p20_rule34 [-7, 4] []))
  have l0 := holds_refl [7, 4, -7, 3]
  have l1 := holds_trans l0 (holds_context p20_rule33 [7, 4] [])
  have l2 := holds_trans l1 (holds_context p20_rule368 [] [-7])
  have r0 := holds_refl [-7, 4, 3, 7]
  have r1 := holds_trans r0 (holds_context p20_rule737 [] [7])
  have r2 := holds_trans r1 (holds_context p20_rule933 [] [7])
  have r3 := holds_trans r2 (holds_context p20_rule13 [5, 5] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r3)) (by central_nf)

theorem p20_rule940 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (18 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 7, 4] [5, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule939 [] [7])) (holds_context p20_rule13 [3, 7, 4] []))
  have l0 := holds_refl [5, 5, 7]
  have r0 := holds_refl [3, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule959 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-17 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-5, -9, 6, -7] [6, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule469 [] [6, -7])) (holds_context p20_rule452 [-9] []))
  have l0 := holds_refl [-5, -9, 6, -7]
  have r0 := holds_refl [-9, 7, 6, 7]
  have r1 := holds_trans r0 (holds_context p20_rule470 [] [6, 7])
  have r2 := holds_trans r1 (holds_context p20_rule620 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem p20_rule960 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [5, -9, 6, -7] [8, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule469 [] [6, 7])) (holds_context p20_rule453 [-9] []))
  have l0 := holds_refl [-5, -9, 6, 7]
  have l1 := holds_trans l0 (holds_context p20_rule807 [] [])
  have r0 := holds_refl [-9, 7, 6, -7]
  have r1 := holds_trans r0 (holds_context p20_rule470 [] [6, -7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule963 : Holds ((normalizedRelatorError .i_r8) ^ (16 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (6 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-22 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [-9, 4, 7, 7] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule470 [] [7, 4])) (holds_context p20_rule336 [-9] []))
  have l0 := holds_refl [5, -9, 7, 4]
  have l1 := holds_trans l0 (holds_context p20_rule470 [5] [4])
  have l2 := holds_trans l1 (holds_context p20_rule545 [] [])
  have r0 := holds_refl [-9, 4, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule992 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-5, -9, 5, -7] [3, -9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule476 [-5] [])) (holds_context p20_rule9 [] [3, -9, 5]))
  have l0 := holds_refl [-5, -9, 5, -7]
  have r0 := holds_refl [3, -9, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule1053 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, -9, 6] [3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule578 [] [6])) (holds_context p20_rule229 [3, 7, -9] []))
  have l0 := holds_refl [6, -7, -9, 6]
  have r0 := holds_refl [3, 7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule1058 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 5, 7, 7] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule585 [] [-7])) (holds_context p20_rule28 [7, 5] []))
  have l0 := holds_refl [4, 6, 5, -7]
  have l1 := holds_trans l0 (holds_context p20_rule514 [4] [])
  have l2 := holds_trans l1 (holds_context p20_rule874 [4] [])
  have l3 := holds_trans l2 (holds_context p20_rule228 [] [-7, 5])
  have r0 := holds_refl [7, 5, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule1059 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, -7] [7, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1058 [] [-7])) (holds_context p20_rule12 [7, 5, 7] []))
  have l0 := holds_refl [-7, 5, -7]
  have r0 := holds_refl [7, 5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule1077 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (13 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (11 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-5, 6, -9, 3] [-9, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule620 [-5] [])) (holds_context p20_rule9 [] [-9, 6, 7]))
  have l0 := holds_refl [-5, 6, -9, 3]
  have r0 := holds_refl [-9, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule1109 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (7 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (8 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (20 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (7 : ℤ)) [7, 4, -5, 6] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule657 [] [4])) (holds_context p20_rule35 [7, -5] []))
  have l0 := holds_refl [5, 3, 7, 4]
  have l1 := holds_trans l0 (holds_context p20_rule940 [5] [])
  have l2 := holds_trans l1 (holds_context p20_rule246 [] [7])
  have r0 := holds_refl [7, -5, 4, 6]
  have r1 := holds_trans r0 (holds_context p20_rule365 [7] [6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule1110 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (7 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (20 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (7 : ℤ)) [7, 4, -5] [-5, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule1109 [] [6])) (holds_context p20_rule229 [7, 4, -5] []))
  have l0 := holds_refl [-5, 7, 6]
  have r0 := holds_refl [7, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule1152 : Holds ((normalizedRelatorError .i_r8) ^ (16 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [7, 6, -9, 3] [4, -7, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule721 [] [7])) (holds_context p20_rule620 [7] []))
  have l0 := holds_refl [-5, -7, -9, 7]
  have l1 := holds_trans l0 (holds_context p20_rule470 [-5, -7] [])
  have l2 := holds_trans l1 (holds_context p20_rule400 [] [-9])
  have r0 := holds_refl [7, 6, -9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule1221 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, -9, 3, 6] [-9, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule805 [] [3])) (holds_context p20_rule227 [-9, 3, 8] []))
  have l0 := holds_refl [8, -9, 6, 3]
  have l1 := holds_trans l0 (holds_context p20_rule305 [8, -9] [])
  have r0 := holds_refl [-9, 3, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule1246 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [7, 8, -7, -9] [-9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule843 [] [2])) (holds_context p20_rule766 [7] []))
  have l0 := holds_refl [2, 9, 4, 2]
  have l1 := holds_trans l0 (holds_context p20_rule42 [2, 9] [])
  have l2 := holds_trans l1 (holds_context p20_rule45 [2] [8])
  have l3 := holds_trans l2 (holds_context p20_rule226 [] [-9, 8])
  have r0 := holds_refl [7, 8, -7, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule1295 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (17 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [8, 6, -9, 3] [-7, -9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule959 [8] [])) (holds_context p20_rule726 [] [-7]))
  have l0 := holds_refl [8, 6, -9, 3]
  have r0 := holds_refl [-9, 8, -7, -7]
  have r1 := holds_trans r0 (holds_context p20_rule28 [-9, 8] [])
  have r2 := holds_trans r1 (holds_context p20_rule727 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem p20_rule1296 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-5, 8, -9, 8] [-9, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule960 [-5] [])) (holds_context p20_rule9 [] [-9, 6, -7]))
  have l0 := holds_refl [-5, 8, -9, 8]
  have r0 := holds_refl [-9, 6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule1301 : Holds ((normalizedRelatorError .i_r8) ^ (-24 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (26 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-27 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-17 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (10 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (12 : ℤ) * (normalizedRelatorError .viii_s3) ^ (18 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-12 : ℤ)) [4, 5, -9, 6] [-9, 4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p20_rule963 [] [-7])) (holds_context p20_rule12 [-9, 4, 7] []))
  have l0 := holds_refl [3, -9, 6, -7]
  have l1 := holds_trans l0 (holds_context p20_rule625 [] [])
  have r0 := holds_refl [-9, 4, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
