module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step34

/-! Kernel-checked central word identities, chunk 35.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c10_rule1282 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [3, -5, -7, 2, 4] [2, 3, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule531 [-5] [])) (holds_context c10_rule48 [] [3, -5]))
  have l0 := holds_refl [-5, 3, -7, 2, 4]
  have l1 := holds_trans l0 (holds_context c10_rule31 [] [-7, 2, 4])
  have r0 := holds_refl [2, -7, 3, -5]
  have r1 := holds_trans r0 (holds_context c10_rule33 [2] [-5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule1291 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [3, 2, 3, -5, -7] [-7, -5, 2, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule552 [3] [])) (holds_context c10_rule225 [] [-7, -5, 2, 8]))
  have l0 := holds_refl [3, 2, 3, -5, -7]
  have r0 := holds_refl [-7, -5, 2, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1504 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, -7, 8, -7] [2, 6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule627 [] [2, 9])) (holds_context c10_rule250 [9, 3] []))
  have l0 := holds_refl [4, 6, 9, 2, 9]
  have l1 := holds_trans l0 (holds_context c10_rule45 [4, 6] [9])
  have l2 := holds_trans l1 (holds_context c10_rule43 [4] [-9, 9])
  have l3 := holds_trans l2 (holds_context c10_rule42 [] [6, -9, 9])
  have l4 := holds_trans l3 (holds_context c10_rule285 [2] [-9, 9])
  have l5 := holds_trans l4 (holds_context c10_rule17 [2, 6, 8] [])
  have r0 := holds_refl [9, 3, -5, 2, -7]
  have r1 := holds_trans r0 (holds_context c10_rule551 [] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r1))) (by central_nf)

theorem c10_rule1505 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -7, 8, -7] [6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1504 [2] [])) (holds_context c10_rule224 [] [3, -7, 8, -7]))
  have l0 := holds_refl [2, 2, 6, 8]
  have l1 := holds_trans l0 (holds_context c10_rule224 [] [6, 8])
  have r0 := holds_refl [3, -7, 8, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule1506 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_r3) [6, 8, 7] [3, -7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1505 [] [7])) (holds_context c10_rule13 [3, -7, 8] []))
  have l0 := holds_refl [6, 8, 7]
  have r0 := holds_refl [3, -7, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1510 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 6, -7, 8] [8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1506 [6] [])) (holds_context c10_rule227 [] [8, 7]))
  have l0 := holds_refl [6, 3, -7, 8]
  have l1 := holds_trans l0 (holds_context c10_rule422 [] [-7, 8])
  have r0 := holds_refl [8, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1512 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_r3) [8, 7, 8] [3, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1510 [] [8])) (holds_context c10_rule228 [3, 6, -7] []))
  have l0 := holds_refl [8, 7, 8]
  have r0 := holds_refl [3, 6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1513 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, 3, -7, 8] [6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1506 [8] [])) (holds_context c10_rule285 [] [8, 7]))
  have l0 := holds_refl [8, 3, -7, 8]
  have r0 := holds_refl [6, 8, 8, 7]
  have r1 := holds_trans r0 (holds_context c10_rule228 [6] [7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule1514 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, 3, -7] [6, 7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1513 [] [8])) (holds_context c10_rule228 [8, 3, -7] []))
  have l0 := holds_refl [6, 7, 8]
  have r0 := holds_refl [8, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule1532 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_r3) [6, 7, 8, 7] [8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1514 [] [7])) (holds_context c10_rule13 [8, 3] []))
  have l0 := holds_refl [6, 7, 8, 7]
  have r0 := holds_refl [8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1533 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 8, 3] [7, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1532 [6] [])) (holds_context c10_rule227 [] [7, 8, 7]))
  have l0 := holds_refl [6, 8, 3]
  have r0 := holds_refl [7, 8, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1734 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, 7] [7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule884 [8] [])) (holds_context c10_rule228 [] [-7, 6, 7]))
  have l0 := holds_refl [8, 3, 6, 8, 3]
  have l1 := holds_trans l0 (holds_context c10_rule423 [] [8, 3])
  have l2 := holds_trans l1 (holds_context c10_rule1533 [] [8, 3])
  have l3 := holds_trans l2 (holds_context c10_rule1512 [7] [3])
  have l4 := holds_trans l3 (holds_context c10_rule34 [] [6, -7, 3])
  have l5 := holds_trans l4 (holds_context c10_rule33 [3, 7, 6] [])
  have l6 := holds_trans l5 (holds_context c10_rule422 [3, 7] [-7])
  have l7 := holds_trans l6 (holds_context c10_rule34 [3] [6, -7])
  have l8 := holds_trans l7 (holds_context c10_rule225 [] [7, 6, -7])
  have r0 := holds_refl [-7, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l8) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule1818 : Holds ((normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [4, 6, 5] [7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1044 [] [5, 5])) (holds_context c10_rule230 [3, -7, 6, 7] []))
  have l0 := holds_refl [4, 6, -5, 5, 5]
  have l1 := holds_trans l0 (holds_context c10_rule9 [4, 6] [5])
  have r0 := holds_refl [3, -7, 6, 7, -5]
  have r1 := holds_trans r0 (holds_context c10_rule1734 [3] [-5])
  have r2 := holds_trans r1 (holds_context c10_rule592 [3, 7] [])
  have r3 := holds_trans r2 (holds_context c10_rule34 [3] [5, -7])
  have r4 := holds_trans r3 (holds_context c10_rule225 [] [7, 5, -7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r4)) (by central_nf)

theorem c10_rule1820 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 5, -7, -5] [4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1818 [] [-5])) (holds_context c10_rule8 [4, 6] []))
  have l0 := holds_refl [7, 5, -7, -5]
  have r0 := holds_refl [4, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1821 : Holds ((normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, 4, 6] [5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1820 [-7] [])) (holds_context c10_rule13 [] [5, -7, -5]))
  have l0 := holds_refl [-7, 4, 6]
  have r0 := holds_refl [5, -7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule1830 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, -5, 4] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1821 [] [4])) (holds_context c10_rule35 [-7, 4] []))
  have l0 := holds_refl [5, -7, -5, 4]
  have r0 := holds_refl [-7, 4, 4, 6]
  have r1 := holds_trans r0 (holds_context c10_rule226 [-7] [6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule1831 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, -5, 4] [-5, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1830 [-5] [])) (holds_context c10_rule9 [] [-7, -5, 4]))
  have l0 := holds_refl [-5, -7, 6]
  have r0 := holds_refl [-7, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule1855 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ)) [-7, -5, 2, 8] [-5, -7, 2, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1831 [] [2])) (holds_context c10_rule42 [-7, -5] []))
  have l0 := holds_refl [-5, -7, 6, 2]
  have l1 := holds_trans l0 (holds_context c10_rule43 [-5, -7] [])
  have r0 := holds_refl [-7, -5, 2, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule1990 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, -5, -7, 6] [3, -5, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1282 [] [4])) (holds_context c10_rule226 [3, -5, -7, 2] []))
  have l0 := holds_refl [2, 3, -7, -5, 4]
  have l1 := holds_trans l0 (holds_context c10_rule1831 [2, 3] [])
  have r0 := holds_refl [3, -5, -7, 2]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem equation_r10_489 : normalizedRelatorError .i_r8 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule236 [] [2, 10])) (holds_context c10_rule62 [1, 6] []))
  have l0 := holds_refl [1, 10, 6, 2, 10]
  have l1 := holds_trans l0 (holds_context c10_rule43 [1, 10] [10])
  have l2 := holds_trans l1 (holds_context c10_rule325 [1, 10, 2] [])
  have l3 := holds_trans l2 (holds_context c10_rule62 [1] [6])
  have r0 := holds_refl [1, 6, 2, 10, 2]
  have r1 := holds_trans r0 (holds_context c10_rule43 [1] [10, 2])
  have r2 := holds_trans r1 (holds_context c10_rule325 [1, 2] [2])
  have r3 := holds_trans r2 (holds_context c10_rule43 [1, 2, 10] [])
  have hh : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ)) [1, 2, 10, 2, 6] [1, 2, 10, 2, 6] := holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r10_6293 : (normalizedRelatorError .i_r8) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule1990 [3] [])) (holds_context c10_rule1291 [] [6]))
  have l0 := holds_refl [3, 3, -5, -7, 2]
  have l1 := holds_trans l0 (holds_context c10_rule225 [] [-5, -7, 2])
  have r0 := holds_refl [-7, -5, 2, 8, 6]
  have r1 := holds_trans r0 (holds_context c10_rule1855 [] [6])
  have r2 := holds_trans r1 (holds_context c10_rule227 [-5, -7, 2] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (5 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, -7, 2] [-5, -7, 2] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem c11_rule20 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ)) [-2] [2] := by
  have h0 := (split [2] [2] (rotate [] [2, 2] source1))
  have l0 := holds_refl [2]
  have r0 := holds_refl [-2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c11_rule22 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c11_rule24 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c11_rule25 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ)) [-10] [10] := by
  have h0 := (split [10] [10] (rotate [] [10, 10] source6))
  have l0 := holds_refl [10]
  have r0 := holds_refl [-10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c11_rule28 : Holds ((normalizedRelatorError .i_s7) ^ (-1 : ℤ)) [-9, -9] [9, 9] := by
  have h0 := (split [9, 9] [9, 9] (rotate [] [9, 9, 9, 9] source9))
  have l0 := holds_refl [9, 9]
  have r0 := holds_refl [-9, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c11_rule36 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2) [2, 4] [8, 2] := by
  have h0 := (split [2, 4] [2, -8] (rotate [] [2, 4, 2, -8] source31))
  have l0 := holds_refl [2, 4]
  have r0 := holds_refl [8, -2]
  have r1 := holds_trans r0 (holds_context c11_rule20 [8] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c11_rule38 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4) [2, 6] [6, 2] := by
  have h0 := (split [2, 6] [2, -6] (rotate [] [2, 6, 2, -6] source32))
  have l0 := holds_refl [2, 6]
  have r0 := holds_refl [6, -2]
  have r1 := holds_trans r0 (holds_context c11_rule20 [6] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c11_rule39 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7) [2, 9] [-9, 2] := by
  have h0 := (split [2, 9] [2, 9] (rotate [] [2, 9, 2, 9] source34))
  have l0 := holds_refl [2, 9]
  have r0 := holds_refl [-9, -2]
  have r1 := holds_trans r0 (holds_context c11_rule20 [-9] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c11_rule40 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ)) [2, -9] [9, 2] := by
  have h0 := (split [9, 2] [9, 2] (rotate [2] [9, 2, 9] source34))
  have l0 := holds_refl [9, 2]
  have r0 := holds_refl [-2, -9]
  have r1 := holds_trans r0 (holds_context c11_rule20 [] [-9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c11_rule57 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s8) ^ (-2 : ℤ) * normalizedRelatorError .vi_r8_s8) [2, 10, 2] [10, 2, 10] := by
  have h0 := (split [2, 10, 2] [10, 2, 10] (rotate [] [2, 10, 2, 10, 2, 10] source25))
  have l0 := holds_refl [2, 10, 2]
  have r0 := holds_refl [-10, -2, -10]
  have r1 := holds_trans r0 (holds_context c11_rule25 [] [-2, -10])
  have r2 := holds_trans r1 (holds_context c11_rule20 [10] [-10])
  have r3 := holds_trans r2 (holds_context c11_rule25 [10, 2] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem equation_r11_21 : (normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) = 1 := by
  have h0 := (split [-8, 2] [4, 2] (rotate [2, 4, 2] [-8] source31))
  have l0 := holds_refl [-8, 2]
  have l1 := holds_trans l0 (holds_context c11_rule24 [] [2])
  have r0 := holds_refl [-2, -4]
  have r1 := holds_trans r0 (holds_context c11_rule20 [] [-4])
  have r2 := holds_trans r1 (holds_context c11_rule22 [2] [])
  have r3 := holds_trans r2 (holds_context c11_rule36 [] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .viii_s2) ^ (2 : ℤ)) [8, 2] [8, 2] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r11_24 : (normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) = 1 := by
  have h0 := (split [6, 2] [-6, 2] (rotate [2] [6, 2, -6] source32))
  have l0 := holds_refl [6, 2]
  have r0 := holds_refl [-2, 6]
  have r1 := holds_trans r0 (holds_context c11_rule20 [] [6])
  have r2 := holds_trans r1 (holds_context c11_rule38 [] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ)) [6, 2] [6, 2] := holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r11_28 : (normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s8) ^ (-3 : ℤ) * (normalizedRelatorError .vi_r8_s8) ^ (2 : ℤ) = 1 := by
  have h0 := (split [10, 2, 10] [2, 10, 2] (rotate [2] [10, 2, 10, 2, 10] source25))
  have l0 := holds_refl [10, 2, 10]
  have r0 := holds_refl [-2, -10, -2]
  have r1 := holds_trans r0 (holds_context c11_rule20 [] [-10, -2])
  have r2 := holds_trans r1 (holds_context c11_rule25 [2] [-2])
  have r3 := holds_trans r2 (holds_context c11_rule20 [2, 10] [])
  have r4 := holds_trans r3 (holds_context c11_rule57 [] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s8) ^ (-3 : ℤ) * (normalizedRelatorError .vi_r8_s8) ^ (2 : ℤ)) [10, 2, 10] [10, 2, 10] := holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)
  exact holds_cancel hh

theorem equation_r11_39 : (normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c11_rule40 [] [-9])) (holds_context c11_rule28 [2] []))
  have l0 := holds_refl [9, 2, -9]
  have l1 := holds_trans l0 (holds_context c11_rule40 [9] [])
  have r0 := holds_refl [2, 9, 9]
  have r1 := holds_trans r0 (holds_context c11_rule39 [] [9])
  have r2 := holds_trans r1 (holds_context c11_rule39 [-9] [])
  have r3 := holds_trans r2 (holds_context c11_rule28 [] [2])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ)) [9, 9, 2] [9, 9, 2] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem c12_rule4 : Holds ((1 : C)) [3, -3] [] := by
  have h0 := (show Holds 1 [3, -3] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [3, -3]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c12_rule14 : Holds ((1 : C)) [8, -8] [] := by
  have h0 := (show Holds 1 [8, -8] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [8, -8]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c12_rule20 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ)) [-2] [2] := by
  have h0 := (split [2] [2] (rotate [] [2, 2] source1))
  have l0 := holds_refl [2]
  have r0 := holds_refl [-2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c12_rule21 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c12_rule22 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
