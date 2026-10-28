module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Certificates.Step08

/-! Additional kernel-checked central word identities, chunk 9.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p21_rule977 : Holds ((normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (14 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ)) [5, 6, -5] [7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule976 [] [5])) (holds_context p21_rule9 [7, 6, -7] []))
  have l0 := holds_refl [-5, 6, 5]
  have l1 := holds_trans l0 (holds_context p21_rule492 [] [])
  have r0 := holds_refl [7, 6, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule987 : Holds ((normalizedRelatorError .i_r8) ^ (-16 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-20 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-16 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [4, -9, 7, 6] [-9, 4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule516 [] [-7])) (holds_context p21_rule12 [-9, 4, 7] []))
  have l0 := holds_refl [3, -9, 6, -7]
  have l1 := holds_trans l0 (holds_context p21_rule596 [] [])
  have r0 := holds_refl [-9, 4, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule991 : Holds ((normalizedRelatorError .i_r8) ^ (-10 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ)) [7, 6, 9, 5] [3, 9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule528 [] [9])) (holds_context p21_rule17 [3, 9, 6] []))
  have l0 := holds_refl [7, 6, 7, 9]
  have l1 := holds_trans l0 (holds_context p21_rule450 [7, 6] [])
  have r0 := holds_refl [3, 9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule992 : Holds ((normalizedRelatorError .i_r8) ^ (-18 : ℤ) * (normalizedRelatorError .i_s1) ^ (-8 : ℤ) * (normalizedRelatorError .i_s4) ^ (-17 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (28 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-38 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-16 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-12 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (12 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (14 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [-9, 6, 3, 7] [-5, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule534 [-9] [])) (holds_context p21_rule17 [] [-5, 6, -9]))
  have l0 := holds_refl [-9, 6, 3, 7]
  have r0 := holds_refl [-5, 6, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule994 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, -9, 6] [3, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule535 [6] [])) (holds_context p21_rule200 [] [3, 7, -9]))
  have l0 := holds_refl [6, -7, -9, 6]
  have r0 := holds_refl [3, 7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule995 : Holds ((normalizedRelatorError .i_r8) ^ (-16 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-9 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (14 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [4, 9, 4, 5] [7, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule536 [9] [])) (holds_context p21_rule16 [] [7, 6, 9]))
  have l0 := holds_refl [9, 7, -5, 7]
  have l1 := holds_trans l0 (holds_context p21_rule669 [] [])
  have r0 := holds_refl [7, 6, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1004 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 9, -7, 6] [9, 3, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule550 [6] [])) (holds_context p21_rule200 [] [9, 3, 7]))
  have l0 := holds_refl [6, 9, -7, 6]
  have r0 := holds_refl [9, 3, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1006 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [7, -5, 7, 7] [-7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule553 [] [-7])) (holds_context p21_rule28 [7, -5] []))
  have l0 := holds_refl [4, -5, 6, -7]
  have l1 := holds_trans l0 (holds_context p21_rule362 [4] [])
  have l2 := holds_trans l1 (holds_context p21_rule942 [4] [])
  have l3 := holds_trans l2 (holds_context p21_rule199 [] [-7, -5])
  have r0 := holds_refl [7, -5, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1008 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [-5, 7, 7] [7, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1006 [-7] [])) (holds_context p21_rule13 [] [-5, 7, 7]))
  have l0 := holds_refl [-7, -7, -5]
  have l1 := holds_trans l0 (holds_context p21_rule28 [] [-5])
  have r0 := holds_refl [-5, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1010 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-9 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 4, -7, 5] [3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule556 [] [6])) (holds_context p21_rule435 [7] []))
  have l0 := holds_refl [4, 6, 5, 6]
  have l1 := holds_trans l0 (holds_context p21_rule850 [4] [])
  have l2 := holds_trans l1 (holds_context p21_rule199 [] [3, -5])
  have r0 := holds_refl [7, 4, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1011 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-9 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 4, -7] [3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1010 [] [-5])) (holds_context p21_rule8 [7, 4, -7] []))
  have l0 := holds_refl [3, -5, -5]
  have l1 := holds_trans l0 (holds_context p21_rule27 [3] [])
  have r0 := holds_refl [7, 4, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1014 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * normalizedRelatorError .viii_r3) [3, -7, 6, 5] [-5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule558 [3] [])) (holds_context p21_rule490 [] [4]))
  have l0 := holds_refl [3, -7, 6, 5]
  have r0 := holds_refl [6, -7, -5, 4]
  have r1 := holds_trans r0 (holds_context p21_rule438 [6, -7] [])
  have r2 := holds_trans r1 (holds_context p21_rule679 [] [-5])
  have r3 := holds_trans r2 (holds_context p21_rule368 [4] [])
  have r4 := holds_trans r3 (holds_context p21_rule199 [] [-5, -7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem p21_rule1016 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * normalizedRelatorError .viii_r3) [-7, 6, 5] [3, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1014 [3] [])) (holds_context p21_rule198 [] [-7, 6, 5]))
  have l0 := holds_refl [3, -5, -7]
  have r0 := holds_refl [-7, 6, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1020 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [4, -9, 6, 3] [6, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule577 [4] [])) (holds_context p21_rule199 [] [6, 3, -9]))
  have l0 := holds_refl [4, -9, 6, 3]
  have r0 := holds_refl [6, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1021 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ)) [4, 3, -9, 3] [6, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule579 [4] [])) (holds_context p21_rule199 [] [6, -9, 6]))
  have l0 := holds_refl [4, 3, -9, 3]
  have r0 := holds_refl [6, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1023 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-15 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-5 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [10, 3, 10, -9] [9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule587 [] [-9])) (holds_context p21_rule29 [-9, 6] []))
  have l0 := holds_refl [9, 6, 9, -9]
  have l1 := holds_trans l0 (holds_context p21_rule593 [] [-9])
  have r0 := holds_refl [-9, 6, 9, 9]
  have r1 := holds_trans r0 (holds_context p21_rule315 [] [9])
  have r2 := holds_trans r1 (holds_context p21_rule17 [9, 6] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem p21_rule1024 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (15 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (5 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [10, 9, 6] [3, 10, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1023 [10] [])) (holds_context p21_rule202 [] [3, 10, -9]))
  have l0 := holds_refl [10, 9, 6]
  have r0 := holds_refl [3, 10, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1030 : Holds ((normalizedRelatorError .i_r8) ^ (-12 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (24 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-5 : ℤ)) [-9, 3, 5, 5] [4, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule591 [3] [])) (holds_context p21_rule518 [] [7]))
  have l0 := holds_refl [3, 6, -9, 3]
  have l1 := holds_trans l0 (holds_context p21_rule274 [] [-9, 3])
  have l2 := holds_trans l1 (holds_context p21_rule580 [] [])
  have r0 := holds_refl [-9, -7, 4, 7]
  have r1 := holds_trans r0 (holds_context p21_rule429 [-9] [])
  have r2 := holds_trans r1 (holds_context p21_rule1011 [-9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem p21_rule1031 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [-9, 10, 3, 10] [6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule593 [-9] [])) (holds_context p21_rule17 [] [6, 9]))
  have l0 := holds_refl [-9, 10, 3, 10]
  have r0 := holds_refl [6, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1032 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [-9, 10, 3] [6, 9, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1031 [] [10])) (holds_context p21_rule202 [-9, 10, 3] []))
  have l0 := holds_refl [6, 9, 10]
  have r0 := holds_refl [-9, 10, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1036 : Holds ((normalizedRelatorError .i_r8) ^ (-16 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-12 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (16 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-23 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-14 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (7 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-8 : ℤ)) [4, -9, -5, 6] [-9, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule599 [] [6])) (holds_context p21_rule200 [-9, 4, -5] []))
  have l0 := holds_refl [4, -9, -5, 6]
  have r0 := holds_refl [-9, 4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1039 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s2) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [1, 3, 1, 3] [4, -5, 1, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule614 [4] [])) (holds_context p21_rule199 [] [1, 3, 1, 3]))
  have l0 := holds_refl [4, -5, 1, 9]
  have r0 := holds_refl [1, 3, 1, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1047 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * normalizedRelatorError .vi_s1_r1 * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [9, -5, 1, -9] [1, -7, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule619 [-7] [])) (holds_context p21_rule448 [] [1, -9]))
  have l0 := holds_refl [-7, 1, 3, 1]
  have l1 := holds_trans l0 (holds_context p21_rule89 [] [])
  have r0 := holds_refl [9, -5, 1, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1070 : Holds ((normalizedRelatorError .i_r8) ^ (-12 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [4, 3, 5, 6] [6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule665 [5] [])) (holds_context p21_rule290 [] [5]))
  have l0 := holds_refl [5, 4, 6, 3]
  have l1 := holds_trans l0 (holds_context p21_rule439 [] [6, 3])
  have l2 := holds_trans l1 (holds_context p21_rule645 [4] [])
  have r0 := holds_refl [6, 5, 5, 5]
  have r1 := holds_trans r0 (holds_context p21_rule216 [6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule1071 : Holds ((normalizedRelatorError .i_r8) ^ (-12 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [3, 5, 6] [4, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1070 [4] [])) (holds_context p21_rule199 [] [3, 5, 6]))
  have l0 := holds_refl [4, 6, -5]
  have r0 := holds_refl [3, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1074 : Holds ((normalizedRelatorError .i_r8) ^ (20 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (11 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-15 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (9 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (8 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-9 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-7, -9, 7, 7] [4, 3, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule671 [] [-9])) (holds_context p21_rule445 [-7, 5] []))
  have l0 := holds_refl [4, 3, -7, -9]
  have r0 := holds_refl [-7, 5, -9, 7]
  have r1 := holds_trans r0 (holds_context p21_rule445 [-7] [7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule1077 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [8, 3, 9, -5] [6, 7, 8, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule673 [] [9])) (holds_context p21_rule448 [8, 3] []))
  have l0 := holds_refl [6, 7, 8, 9]
  have r0 := holds_refl [8, 3, 9, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1092 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [3, -5, 1, 8] [4, 6, 5, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule689 [] [1])) (holds_context p21_rule40 [3, -5] []))
  have l0 := holds_refl [4, 6, 5, 1]
  have r0 := holds_refl [3, -5, 1, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1099 : Holds ((normalizedRelatorError .i_r8) ^ (9 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (9 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [-9, 8, -7, 6] [8, -9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule701 [] [6])) (holds_context p21_rule200 [8, -9, -7] []))
  have l0 := holds_refl [-9, 8, -7, 6]
  have r0 := holds_refl [8, -9, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1100 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-7, -9, -5, -7] [-9, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule702 [] [-7])) (holds_context p21_rule12 [-9, 8, 7] []))
  have l0 := holds_refl [-7, -9, -5, -7]
  have r0 := holds_refl [-9, 8, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1101 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [9, -7, -9, -5] [8, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule702 [9] [])) (holds_context p21_rule16 [] [8, 7, 7]))
  have l0 := holds_refl [9, -7, -9, -5]
  have r0 := holds_refl [8, 7, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1105 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [10, 4, 3, 8] [8, 10, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule705 [] [5, 5])) (holds_context p21_rule338 [10] []))
  have l0 := holds_refl [8, 10, 5, 5]
  have r0 := holds_refl [10, 4, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1172 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, -9, 6, 3] [-9, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule786 [] [3])) (holds_context p21_rule198 [-9, 3, 8] []))
  have l0 := holds_refl [8, -9, 6, 3]
  have r0 := holds_refl [-9, 3, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1174 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 9, 8, -9] [3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule787 [6] [])) (holds_context p21_rule200 [] [3, 8, 3]))
  have l0 := holds_refl [6, 9, 8, -9]
  have r0 := holds_refl [3, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1179 : Holds ((normalizedRelatorError .i_r8) ^ (10 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [9, -5, 8, -9] [6, -7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule789 [-7] [])) (holds_context p21_rule13 [] [6, -7, 8]))
  have l0 := holds_refl [-7, 9, 8, -9]
  have l1 := holds_trans l0 (holds_context p21_rule448 [] [8, -9])
  have r0 := holds_refl [6, -7, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1183 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (5 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ)) [4, 6, -5, 6] [3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule810 [6] [])) (holds_context p21_rule200 [] [3, 5]))
  have l0 := holds_refl [6, 4, -5, 6]
  have l1 := holds_trans l0 (holds_context p21_rule35 [] [-5, 6])
  have r0 := holds_refl [3, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule1184 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (5 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ)) [6, -5, 6] [4, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1183 [4] [])) (holds_context p21_rule199 [] [6, -5, 6]))
  have l0 := holds_refl [4, 3, 5]
  have r0 := holds_refl [6, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1188 : Holds ((normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (5 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [6, -5, 7, 6] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule810 [7] [])) (holds_context p21_rule627 [] [5]))
  have l0 := holds_refl [7, 4, -5, 6]
  have l1 := holds_trans l0 (holds_context p21_rule306 [] [6])
  have r0 := holds_refl [8, -7, 8, 5]
  have r1 := holds_trans r0 (holds_context p21_rule402 [8] [])
  have r2 := holds_trans r1 (holds_context p21_rule201 [] [-5, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem p21_rule1189 : Holds ((normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [-5, 7, 6] [6, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule1188 [6] [])) (holds_context p21_rule200 [] [-5, 7, 6]))
  have l0 := holds_refl [6, -5, 7]
  have r0 := holds_refl [-5, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule1222 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (13 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [9, 6, 8, -7] [8, 9, 3, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context p21_rule885 [9] [])) (holds_context p21_rule753 [] [3]))
  have l0 := holds_refl [9, 6, 8, -7]
  have r0 := holds_refl [8, 9, 7, 3]
  have r1 := holds_trans r0 (holds_context p21_rule34 [8, 9] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
