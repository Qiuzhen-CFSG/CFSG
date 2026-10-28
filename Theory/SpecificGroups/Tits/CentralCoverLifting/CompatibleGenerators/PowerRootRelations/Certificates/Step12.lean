module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step11

/-! Kernel-checked central word identities, chunk 12.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c2_rule1976 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [2, 7, 9] [7, 2] := by
  have h0 := c2_rule52
  have l0 := holds_refl [2, 9, 5]
  have l1 := holds_trans l0 (holds_context c2_rule1970 [2] [])
  have r0 := holds_refl [7, 2]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1977 : Holds ((normalizedRelatorError .i_r8) ^ (7 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-5 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [7, 2, -9] [2, 7] := by
  have h0 := c2_rule256
  have l0 := holds_refl [9, 5, 2]
  have l1 := holds_trans l0 (holds_context c2_rule1970 [] [2])
  have l2 := holds_trans l1 (holds_context c2_rule45 [7] [])
  have r0 := holds_refl [2, 7]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1978 : Holds ((normalizedRelatorError .i_r8) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * normalizedRelatorError .viii_s4 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (6 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [9, 3, 5] [7, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1970 [] [3])) (holds_context c2_rule32 [9] []))
  have l0 := holds_refl [7, 9, 3]
  have r0 := holds_refl [9, 3, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1982 : Holds ((normalizedRelatorError .i_r8) ^ (18 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [7, 9, 3, -9] [-7, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1959 [9] [])) (holds_context c2_rule16 [] [-7, 4, 6]))
  have l0 := holds_refl [9, 3, 5, -9]
  have l1 := holds_trans l0 (holds_context c2_rule1978 [] [-9])
  have r0 := holds_refl [-7, 4, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1983 : Holds ((normalizedRelatorError .i_r8) ^ (18 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (9 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-15 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (17 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [3, -9, 7, 5] [-9, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1959 [] [5])) (holds_context c2_rule1391 [-9] []))
  have l0 := holds_refl [3, 5, -9, 5]
  have l1 := holds_trans l0 (holds_context c2_rule1963 [3] [5])
  have r0 := holds_refl [-9, 5, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1985 : Holds ((normalizedRelatorError .i_r8) ^ (-14 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-8 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-18 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-5 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-10 : ℤ)) [-9, 4, 6, -7] [3, -9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1961 [3, 5] [])) (holds_context c2_rule612 [] [-7]))
  have l0 := holds_refl [3, 5, -9]
  have l1 := holds_trans l0 (holds_context c2_rule1963 [3] [])
  have r0 := holds_refl [-9, 4, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule2097 : Holds ((normalizedRelatorError .i_r8) ^ (18 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-19 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-12 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [9, 3, -9, 7] [-7, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1978 [] [-9])) (holds_context c2_rule1963 [9, 3] []))
  have l0 := holds_refl [7, 9, 3, -9]
  have l1 := holds_trans l0 (holds_context c2_rule1982 [] [])
  have r0 := holds_refl [9, 3, -9, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule2106 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-7, 4, 6] [4, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1985 [9] [])) (holds_context c2_rule16 [] [4, 6, -7]))
  have l0 := holds_refl [9, 3, -9, 7]
  have l1 := holds_trans l0 (holds_context c2_rule2097 [] [])
  have r0 := holds_refl [4, 6, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule2136 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [4, 6, -7, 5] [5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule2097 [] [5])) (holds_context c2_rule1983 [9] []))
  have l0 := holds_refl [-7, 4, 6, 5]
  have l1 := holds_trans l0 (holds_context c2_rule2106 [] [5])
  have r0 := holds_refl [9, -9, 5, -7]
  have r1 := holds_trans r0 (holds_context c2_rule16 [] [5, -7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule2137 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [6, -7, 5] [4, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule2136 [4] [])) (holds_context c2_rule230 [] [6, -7, 5]))
  have l0 := holds_refl [4, 5, -7]
  have r0 := holds_refl [6, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem equation_r2_112 : normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule60 [] [2])) (holds_context c2_rule41 [4, 6] []))
  have l0 := holds_refl [4, 8, 6, 2]
  have l1 := holds_trans l0 (holds_context c2_rule43 [4, 8] [])
  have l2 := holds_trans l1 (holds_context c2_rule41 [4] [6])
  have l3 := holds_trans l2 (holds_context c2_rule42 [] [4, 6])
  have l4 := holds_trans l3 (holds_context c2_rule36 [2] [6])
  have r0 := holds_refl [4, 6, 2, 4]
  have r1 := holds_trans r0 (holds_context c2_rule43 [4] [4])
  have r2 := holds_trans r1 (holds_context c2_rule42 [] [6, 4])
  have r3 := holds_trans r2 (holds_context c2_rule35 [2, 8] [])
  have r4 := holds_trans r3 (holds_context c2_rule36 [2] [6])
  have hh : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [2, 4, 8, 6] [2, 4, 8, 6] := holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r4)) (by central_nf)
  exact holds_cancel hh

theorem equation_r2_1537 : (normalizedRelatorError .i_r8) ^ (-12 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-6 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule586 [-7] [])) (holds_context c2_rule252 [] [-5, 7]))
  have l0 := holds_refl [-7, 3, 6, -7, 2]
  have l1 := holds_trans l0 (holds_context c2_rule33 [] [6, -7, 2])
  have l2 := holds_trans l1 (holds_context c2_rule1443 [3] [2])
  have l3 := holds_trans l2 (holds_context c2_rule1145 [] [7, 2])
  have l4 := holds_trans l3 (holds_context c2_rule1299 [] [])
  have l5 := holds_trans l4 (holds_context c2_rule1443 [2, 3] [])
  have l6 := holds_trans l5 (holds_context c2_rule1145 [2] [7])
  have r0 := holds_refl [2, -5, 7, -5, 7]
  have r1 := holds_trans r0 (holds_context c2_rule538 [2] [7])
  have r2 := holds_trans r1 (holds_context c2_rule1145 [2] [7])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-12 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-6 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ)) [2, 8, -7, 8, 7] [2, 8, -7, 8, 7] := holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r2_2281 : normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1075 [] [6])) (holds_context c2_rule231 [5, 5, -7] []))
  have l0 := holds_refl [4, 3, 6, -7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule1137 [4] [6])
  have l2 := holds_trans l1 (holds_context c2_rule1129 [4, 8] [])
  have l3 := holds_trans l2 (holds_context c2_rule322 [4] [-7])
  have l4 := holds_trans l3 (holds_context c2_rule230 [] [5, 5, -7])
  have r0 := holds_refl [5, 5, -7]
  have hh : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, -7] [5, 5, -7] := holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r0)) (by central_nf)
  exact holds_cancel hh

theorem equation_r2_6320 : (normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1587 [] [-7])) (holds_context c2_rule1456 [-5] []))
  have l0 := holds_refl [4, 3, 5, 7, -7]
  have l1 := holds_trans l0 (holds_context c2_rule12 [4, 3, 5] [])
  have r0 := holds_refl [-5, 4, 3, 5, 5]
  have r1 := holds_trans r0 (holds_context c2_rule1764 [] [3, 5, 5])
  have r2 := holds_trans r1 (holds_context c2_rule31 [4] [5, 5])
  have r3 := holds_trans r2 (holds_context c2_rule9 [4, 3] [5])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [4, 3, 5] [4, 3, 5] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r2_7170 : (normalizedRelatorError .i_r8) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ) = 1 := by
  have h0 := c2_rule1723
  have l0 := holds_refl [9, 4, 3, -5, -9]
  have l1 := holds_trans l0 (holds_context c2_rule1781 [] [-9])
  have r0 := holds_refl [2, 3, 9, -5, 2]
  have r1 := holds_trans r0 (holds_context c2_rule1966 [2, 3] [2])
  have r2 := holds_trans r1 (holds_context c2_rule45 [2, 3, -7] [])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [2, 3, -7, 2, -9] [2, 3, -7, 2, -9] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r2_7445 : (normalizedRelatorError .i_r8) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (6 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1802 [7] [])) (holds_context c2_rule34 [] [2, 9, 3]))
  have l0 := holds_refl [7, 4, -5, 2, 7]
  have l1 := holds_trans l0 (holds_context c2_rule556 [] [2, 7])
  have l2 := holds_trans l1 (holds_context c2_rule250 [6] [7])
  have l3 := holds_trans l2 (holds_context c2_rule43 [] [-7, 5, 7])
  have l4 := holds_trans l3 (holds_context c2_rule2137 [2] [7])
  have l5 := holds_trans l4 (holds_context c2_rule13 [2, 4, 5] [])
  have r0 := holds_refl [3, 7, 2, 9, 3]
  have r1 := holds_trans r0 (holds_context c2_rule91 [] [3])
  have r2 := holds_trans r1 (holds_context c2_rule32 [2, 4, 3] [])
  have r3 := holds_trans r2 (holds_context c2_rule229 [2, 4] [5])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (6 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [2, 4, 5] [2, 4, 5] := holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r2_8340 : (normalizedRelatorError .i_r8) ^ (6 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1970 [] [5, 2, 9])) (holds_context c2_rule263 [9] []))
  have l0 := holds_refl [7, 9, 5, 2, 9]
  have l1 := holds_trans l0 (holds_context c2_rule1970 [7] [2, 9])
  have l2 := holds_trans l1 (holds_context c2_rule45 [7, 7] [9])
  have l3 := holds_trans l2 (holds_context c2_rule1977 [7] [9])
  have l4 := holds_trans l3 (holds_context c2_rule1976 [7] [])
  have r0 := holds_refl [9, -5, 2, -7]
  have r1 := holds_trans r0 (holds_context c2_rule1966 [] [2, -7])
  have r2 := holds_trans r1 (holds_context c2_rule45 [-7] [-7])
  have r3 := holds_trans r2 (holds_context c2_rule1964 [-7] [])
  have r4 := holds_trans r3 (holds_context c2_rule28 [] [2])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ)) [7, 7, 2] [7, 7, 2] := holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r4)) (by central_nf)
  exact holds_cancel hh

theorem c5_rule0 : Holds ((1 : C)) [1, -1] [] := by
  have h0 := (show Holds 1 [1, -1] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [1, -1]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule4 : Holds ((1 : C)) [3, -3] [] := by
  have h0 := (show Holds 1 [3, -3] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [3, -3]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule12 : Holds ((1 : C)) [7, -7] [] := by
  have h0 := (show Holds 1 [7, -7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [7, -7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule13 : Holds ((1 : C)) [-7, 7] [] := by
  have h0 := (show Holds 1 [-7, 7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-7, 7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule20 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ)) [-1] [1] := by
  have h0 := (split [1] [1] (rotate [] [1, 1] source0))
  have l0 := holds_refl [1]
  have r0 := holds_refl [-1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c5_rule21 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c5_rule23 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 3] [3, -7] := by
  have h0 := (split [-3, -7] [3, 7] (rotate [] [-3, -7, 3, 7] source12))
  have l0 := holds_refl [-3, -7]
  have l1 := holds_trans l0 (holds_context c5_rule21 [] [-7])
  have r0 := holds_refl [-7, -3]
  have r1 := holds_trans r0 (holds_context c5_rule21 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c5_rule25 : Holds ((normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [3, 1, 3, 1] [1, 7, 1, -7] := by
  have h0 := (split [1, 7, 1, -7] [-1, -3, -1, -3] (rotate [] [1, 7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, 7, 1, -7]
  have r0 := holds_refl [3, 1, 3, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c5_rule26 : Holds (normalizedRelatorError .vii_s5) [7, 1, -7, 1] [1, 3, 1, 3] := by
  have h0 := (split [7, 1, -7, -1] [-3, -1, -3, 1] (rotate [1] [7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [7, 1, -7, -1]
  have l1 := holds_trans l0 (holds_context c5_rule20 [7, 1, -7] [])
  have r0 := holds_refl [-1, 3, 1, 3]
  have r1 := holds_trans r0 (holds_context c5_rule20 [] [3, 1, 3])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c5_rule27 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [-7, 1, 3, 1] [1, -7, 1, 3] := by
  have h0 := (split [1, -7, -1, -3] [-1, -3, 1, 7] (rotate [1, 7] [1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, -7, -1, -3]
  have l1 := holds_trans l0 (holds_context c5_rule20 [1, -7] [-3])
  have l2 := holds_trans l1 (holds_context c5_rule21 [1, -7, 1] [])
  have r0 := holds_refl [-7, -1, 3, 1]
  have r1 := holds_trans r0 (holds_context c5_rule20 [-7] [3, 1])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c5_rule29 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1) [1, 7, 1, 3, -7] [1, 1, 7, 1, -7] := by
  have h0 := (split [3, 1, 3, 1, 3] [1, 3, 1, 3, 1] (rotate [] [3, 1, 3, 1, 3, 1, 3, 1, 3, 1] source24))
  have l0 := holds_refl [3, 1, 3, 1, 3]
  have l1 := holds_trans l0 (holds_context c5_rule25 [] [3])
  have l2 := holds_trans l1 (holds_context c5_rule23 [1, 7, 1] [])
  have r0 := holds_refl [-1, -3, -1, -3, -1]
  have r1 := holds_trans r0 (holds_context c5_rule20 [] [-3, -1, -3, -1])
  have r2 := holds_trans r1 (holds_context c5_rule21 [1] [-1, -3, -1])
  have r3 := holds_trans r2 (holds_context c5_rule20 [1, 3] [-3, -1])
  have r4 := holds_trans r3 (holds_context c5_rule21 [1, 3, 1] [-1])
  have r5 := holds_trans r4 (holds_context c5_rule20 [1, 3, 1, 3] [])
  have r6 := holds_trans r5 (holds_context c5_rule25 [1] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r6)) (by central_nf)

theorem c5_rule30 : Holds (normalizedRelatorError .i_r1) [1, 1] [] := by
  have h0 := c5_rule0
  have l0 := holds_refl [1, -1]
  have l1 := holds_trans l0 (holds_context c5_rule20 [1] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule31 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c5_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c5_rule21 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule38 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s5) [3, 7, 1, -7] [1, 3, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule25 [3, 1] [])) (holds_context c5_rule25 [] [3, 1]))
  have l0 := holds_refl [3, 1, 1, 7, 1, -7]
  have l1 := holds_trans l0 (holds_context c5_rule30 [3] [7, 1, -7])
  have r0 := holds_refl [1, 7, 1, -7, 3, 1]
  have r1 := holds_trans r0 (holds_context c5_rule23 [1, 7, 1] [1])
  have r2 := holds_trans r1 (holds_context c5_rule29 [] [1])
  have r3 := holds_trans r2 (holds_context c5_rule30 [] [7, 1, -7, 1])
  have r4 := holds_trans r3 (holds_context c5_rule26 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r4)) (by central_nf)

theorem c5_rule42 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1) [3, 1, -7] [1, -7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule38 [-7] [])) (holds_context c5_rule23 [] [7, 1, -7]))
  have l0 := holds_refl [-7, 1, 3, 1, 3]
  have l1 := holds_trans l0 (holds_context c5_rule27 [] [3])
  have l2 := holds_trans l1 (holds_context c5_rule31 [1, -7, 1] [])
  have r0 := holds_refl [3, -7, 7, 1, -7]
  have r1 := holds_trans r0 (holds_context c5_rule13 [3] [1, -7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c5_rule43 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [1, -7, 1, 7] [3, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule42 [] [7])) (holds_context c5_rule13 [3, 1] []))
  have l0 := holds_refl [1, -7, 1, 7]
  have r0 := holds_refl [3, 1]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule44 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [-7, 1, 7] [1, 3, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule43 [1] [])) (holds_context c5_rule30 [] [-7, 1, 7]))
  have l0 := holds_refl [1, 3, 1]
  have r0 := holds_refl [-7, 1, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c5_rule46 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [-7, 1, -7, 1] [3, -7, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule42 [-7] [])) (holds_context c5_rule23 [] [1, -7]))
  have l0 := holds_refl [-7, 1, -7, 1]
  have r0 := holds_refl [3, -7, 1, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule47 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .vi_s1_r1) [3, 1, 3, -7] [1, -7, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule42 [] [3])) (holds_context c5_rule23 [3, 1] []))
  have l0 := holds_refl [1, -7, 1, 3]
  have r0 := holds_refl [3, 1, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c5_rule48 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1) [7, 1, 3, 1] [1, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule44 [7] [])) (holds_context c5_rule12 [] [1, 7]))
  have l0 := holds_refl [7, 1, 3, 1]
  have r0 := holds_refl [1, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c5_rule49 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1) [7, 1, 3] [1, 7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule48 [] [1])) (holds_context c5_rule30 [7, 1, 3] []))
  have l0 := holds_refl [1, 7, 1]
  have r0 := holds_refl [7, 1, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem equation_r5_0 : (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) = 1 := by
  have h0 := (split [-7, 3] [7, -3] (rotate [-3] [-7, 3, 7] source12))
  have l0 := holds_refl [-7, 3]
  have l1 := holds_trans l0 (holds_context c5_rule23 [] [])
  have r0 := holds_refl [3, -7]
  have hh : Holds ((normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ)) [3, -7] [3, -7] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)
  exact holds_cancel hh

theorem equation_r5_12 : (normalizedRelatorError .i_r1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ) = 1 := by
  have h0 := (split [1, 3, 1, 3, 1] [3, 1, 3, 1, 3] (rotate [3] [1, 3, 1, 3, 1, 3, 1, 3, 1] source24))
  have l0 := holds_refl [1, 3, 1, 3, 1]
  have l1 := holds_trans l0 (holds_context c5_rule25 [1] [])
  have r0 := holds_refl [-3, -1, -3, -1, -3]
  have r1 := holds_trans r0 (holds_context c5_rule21 [] [-1, -3, -1, -3])
  have r2 := holds_trans r1 (holds_context c5_rule20 [3] [-3, -1, -3])
  have r3 := holds_trans r2 (holds_context c5_rule21 [3, 1] [-1, -3])
  have r4 := holds_trans r3 (holds_context c5_rule20 [3, 1, 3] [-3])
  have r5 := holds_trans r4 (holds_context c5_rule25 [] [-3])
  have r6 := holds_trans r5 (holds_context c5_rule21 [1, 7, 1, -7] [])
  have r7 := holds_trans r6 (holds_context c5_rule23 [1, 7, 1] [])
  have r8 := holds_trans r7 (holds_context c5_rule29 [] [])
  have hh : Holds ((normalizedRelatorError .i_r1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ)) [1, 1, 7, 1, -7] [1, 1, 7, 1, -7] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r8)) (by central_nf)
  exact holds_cancel hh

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
