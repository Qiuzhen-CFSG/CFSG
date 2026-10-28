module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step20

/-! Kernel-checked central word identities, chunk 21.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule4263 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1) [1, 9, 1, -9] [3, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4261 [] [-9])) (holds_context c6_rule16 [3, 1] []))
  have l0 := holds_refl [1, 9, 1, -9]
  have r0 := holds_refl [3, 1]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4264 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1) [9, 1, -9] [1, 3, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4263 [1] [])) (holds_context c6_rule169 [] [9, 1, -9]))
  have l0 := holds_refl [1, 3, 1]
  have r0 := holds_refl [9, 1, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4269 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [-9, 1, 3, 1] [1, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4264 [-9] [])) (holds_context c6_rule17 [] [1, -9]))
  have l0 := holds_refl [-9, 1, 3, 1]
  have r0 := holds_refl [1, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4270 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [-9, 1, 3] [1, -9, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4269 [] [1])) (holds_context c6_rule169 [-9, 1, 3] []))
  have l0 := holds_refl [1, -9, 1]
  have r0 := holds_refl [-9, 1, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4311 : Holds ((normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [-5, 1, 10, -7, -9] [6, -7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4248 [4] [])) (holds_context c6_rule34 [] [4, -7, 1]))
  have l0 := holds_refl [4, -5, 1, -7, -9]
  have l1 := holds_trans l0 (holds_context c6_rule1412 [] [1, -7, -9])
  have l2 := holds_trans l1 (holds_context c6_rule37 [-5] [-7, -9])
  have r0 := holds_refl [6, 4, 4, -7, 1]
  have r1 := holds_trans r0 (holds_context c6_rule171 [6] [-7, 1])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule4314 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-18 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-2 : ℤ) * normalizedRelatorError .vii_r3) [9, 1, -5, -9] [-7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4311 [6] [])) (holds_context c6_rule4055 [] [-9]))
  have l0 := holds_refl [6, 6, -7, 1]
  have l1 := holds_trans l0 (holds_context c6_rule172 [] [-7, 1])
  have r0 := holds_refl [9, 1, -5, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4315 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (18 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (2 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [-9, -7, 1] [1, -5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4314 [-9] [])) (holds_context c6_rule17 [] [1, -5, -9]))
  have l0 := holds_refl [-9, -7, 1]
  have r0 := holds_refl [1, -5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4320 : Holds ((normalizedRelatorError .i_r1) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-19 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-2 : ℤ) * normalizedRelatorError .vii_r3) [1, -5, -9, 7] [1, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4315 [] [7])) (holds_context c6_rule909 [-9] []))
  have l0 := holds_refl [1, -5, -9, 7]
  have r0 := holds_refl [-9, 1, 3, 1]
  have r1 := holds_trans r0 (holds_context c6_rule4270 [] [1])
  have r2 := holds_trans r1 (holds_context c6_rule169 [1, -9] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule4322 : Holds ((normalizedRelatorError .i_r1) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-19 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-2 : ℤ) * normalizedRelatorError .vii_r3) [-5, -9, 7] [-9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4320 [1] [])) (holds_context c6_rule169 [] [-5, -9, 7]))
  have l0 := holds_refl [1, 1, -9]
  have l1 := holds_trans l0 (holds_context c6_rule169 [] [-9])
  have r0 := holds_refl [-5, -9, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4323 : Holds ((normalizedRelatorError .i_r1) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-19 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-2 : ℤ) * normalizedRelatorError .vii_r3) [-9, 7] [5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4322 [5] [])) (holds_context c6_rule8 [] [-9, 7]))
  have l0 := holds_refl [5, -9]
  have r0 := holds_refl [-9, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4324 : Holds ((normalizedRelatorError .i_r1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (19 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (2 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [-9, -7] [-5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4322 [] [-7])) (holds_context c6_rule12 [-5, -9] []))
  have l0 := holds_refl [-9, -7]
  have r0 := holds_refl [-5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4353 : Holds ((normalizedRelatorError .i_r1) ^ (4 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-2 : ℤ) * normalizedRelatorError .vii_r3) [3, -9, 6, -7] [5, 4, -9, 6] := by
  have h0 := c6_rule3164
  have l0 := holds_refl [4, -9, 7, 6]
  have l1 := holds_trans l0 (holds_context c6_rule4323 [4] [6])
  have l2 := holds_trans l1 (holds_context c6_rule1410 [] [-9, 6])
  have r0 := holds_refl [3, -9, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem equation_r6_10389 : (normalizedRelatorError .i_r1) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-7 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (23 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (12 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-8 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-10 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (4 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-4 : ℤ) * (normalizedRelatorError .vii_s3) ^ (4 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4353 [7] [])) (holds_context c6_rule33 [] [-9, 6, -7]))
  have l0 := holds_refl [7, 5, 4, -9, 6]
  have l1 := holds_trans l0 (holds_context c6_rule273 [] [-9, 6])
  have l2 := holds_trans l1 (holds_context c6_rule1242 [5] [])
  have r0 := holds_refl [3, 7, -9, 6, -7]
  have r1 := holds_trans r0 (holds_context c6_rule1269 [] [-7])
  have r2 := holds_trans r1 (holds_context c6_rule4324 [6, -7] [])
  have r3 := holds_trans r2 (holds_context c6_rule343 [] [-9])
  have hh : Holds ((normalizedRelatorError .i_r1) ^ (-8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-7 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (23 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (12 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-8 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-10 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (4 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-4 : ℤ) * (normalizedRelatorError .vii_s3) ^ (4 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-2 : ℤ)) [5, 3, -7, -9] [5, 3, -7, -9] := holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r6_21 : (normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .vii_s2) ^ (2 : ℤ) = 1 := by
  have h0 := (split [-10, 1] [4, 1] (rotate [1, 4, 1] [-10] source26))
  have l0 := holds_refl [-10, 1]
  have l1 := holds_trans l0 (holds_context c6_rule25 [] [1])
  have l2 := holds_trans l1 (holds_context c6_rule36 [] [])
  have r0 := holds_refl [-1, -4]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [-4])
  have r2 := holds_trans r1 (holds_context c6_rule22 [1] [])
  have hh : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .vii_s2) ^ (2 : ℤ)) [1, 4] [1, 4] := holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r6_25 : (normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .vii_s4) ^ (2 : ℤ) = 1 := by
  have h0 := (split [-8, 1] [6, 1] (rotate [1, 6, 1] [-8] source27))
  have l0 := holds_refl [-8, 1]
  have l1 := holds_trans l0 (holds_context c6_rule24 [] [1])
  have l2 := holds_trans l1 (holds_context c6_rule38 [] [])
  have r0 := holds_refl [-1, -6]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [-6])
  have r2 := holds_trans r1 (holds_context c6_rule23 [1] [])
  have hh : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .vii_s4) ^ (2 : ℤ)) [1, 6] [1, 6] := holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r6_421 : normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule192 [] [1])) (holds_context c6_rule36 [1, 8, 4] []))
  have l0 := holds_refl [1, 6, 10, 4, 1]
  have l1 := holds_trans l0 (holds_context c6_rule37 [1, 6, 10] [])
  have l2 := holds_trans l1 (holds_context c6_rule36 [1, 6] [10])
  have l3 := holds_trans l2 (holds_context c6_rule39 [1] [4, 10])
  have l4 := holds_trans l3 (holds_context c6_rule169 [] [8, 4, 10])
  have l5 := holds_trans l4 (holds_context c6_rule194 [] [])
  have r0 := holds_refl [1, 8, 4, 1, 4]
  have r1 := holds_trans r0 (holds_context c6_rule37 [1, 8] [4])
  have r2 := holds_trans r1 (holds_context c6_rule38 [1] [10, 4])
  have r3 := holds_trans r2 (holds_context c6_rule169 [] [6, 10, 4])
  have hh : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [6, 10, 4] [6, 10, 4] := holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r6_7111 : (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) = 1 := by
  have h0 := c6_rule2759
  have l0 := holds_refl [3, -9, 3, -9, 6]
  have l1 := holds_trans l0 (holds_context c6_rule2865 [3] [])
  have l2 := holds_trans l1 (holds_context c6_rule2250 [] [-9])
  have l3 := holds_trans l2 (holds_context c6_rule2833 [4] [])
  have r0 := holds_refl [4, 10, 3, 10]
  have r1 := holds_trans r0 (holds_context c6_rule2869 [4] [])
  have hh : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ)) [4, 9, 6, 9] [4, 9, 6, 9] := holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r1)) (by central_nf)
  exact holds_cancel hh

theorem c7_rule4 : Holds ((1 : C)) [3, -3] [] := by
  have h0 := (show Holds 1 [3, -3] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [3, -3]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule6 : Holds ((1 : C)) [4, -4] [] := by
  have h0 := (show Holds 1 [4, -4] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [4, -4]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule8 : Holds ((1 : C)) [5, -5] [] := by
  have h0 := (show Holds 1 [5, -5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [5, -5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule9 : Holds ((1 : C)) [-5, 5] [] := by
  have h0 := (show Holds 1 [-5, 5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-5, 5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule10 : Holds ((1 : C)) [6, -6] [] := by
  have h0 := (show Holds 1 [6, -6] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [6, -6]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule12 : Holds ((1 : C)) [7, -7] [] := by
  have h0 := (show Holds 1 [7, -7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [7, -7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule13 : Holds ((1 : C)) [-7, 7] [] := by
  have h0 := (show Holds 1 [-7, 7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-7, 7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule14 : Holds ((1 : C)) [8, -8] [] := by
  have h0 := (show Holds 1 [8, -8] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [8, -8]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule16 : Holds ((1 : C)) [9, -9] [] := by
  have h0 := (show Holds 1 [9, -9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [9, -9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule17 : Holds ((1 : C)) [-9, 9] [] := by
  have h0 := (show Holds 1 [-9, 9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-9, 9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule18 : Holds ((1 : C)) [10, -10] [] := by
  have h0 := (show Holds 1 [10, -10] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [10, -10]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule20 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule21 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule22 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ)) [-6] [6] := by
  have h0 := (split [6] [6] (rotate [] [6, 6] source4))
  have l0 := holds_refl [6]
  have r0 := holds_refl [-6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule23 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule24 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ)) [-10] [10] := by
  have h0 := (split [10] [10] (rotate [] [10, 10] source6))
  have l0 := holds_refl [10]
  have r0 := holds_refl [-10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule25 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ)) [-5, -5] [5, 5] := by
  have h0 := (split [5, 5] [5, 5] (rotate [] [5, 5, 5, 5] source7))
  have l0 := holds_refl [5, 5]
  have r0 := holds_refl [-5, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule26 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ)) [-7, -7] [7, 7] := by
  have h0 := (split [7, 7] [7, 7] (rotate [] [7, 7, 7, 7] source8))
  have l0 := holds_refl [7, 7]
  have r0 := holds_refl [-7, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule28 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ)) [4, 3] [3, 4] := by
  have h0 := (split [-3, -4] [3, 4] (rotate [] [-3, -4, 3, 4] source10))
  have l0 := holds_refl [-3, -4]
  have l1 := holds_trans l0 (holds_context c7_rule20 [] [-4])
  have l2 := holds_trans l1 (holds_context c7_rule21 [3] [])
  have r0 := holds_refl [-4, -3]
  have r1 := holds_trans r0 (holds_context c7_rule21 [] [-3])
  have r2 := holds_trans r1 (holds_context c7_rule20 [4] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c7_rule29 : Holds (normalizedRelatorError .ii_s1_s3) [3, -5] [-5, 3] := by
  have h0 := (split [-3, -5] [3, 5] (rotate [] [-3, -5, 3, 5] source11))
  have l0 := holds_refl [-3, -5]
  have l1 := holds_trans l0 (holds_context c7_rule20 [] [-5])
  have r0 := holds_refl [-5, -3]
  have r1 := holds_trans r0 (holds_context c7_rule20 [-5] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule30 : Holds (normalizedRelatorError .ii_s1_s3) [3, 5] [5, 3] := by
  have h0 := (split [3, 5] [-3, -5] (rotate [-3, -5] [3, 5] source11))
  have l0 := holds_refl [3, 5]
  have r0 := holds_refl [5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule31 : Holds (normalizedRelatorError .ii_s1_s5) [3, -7] [-7, 3] := by
  have h0 := (split [-3, -7] [3, 7] (rotate [] [-3, -7, 3, 7] source12))
  have l0 := holds_refl [-3, -7]
  have l1 := holds_trans l0 (holds_context c7_rule20 [] [-7])
  have r0 := holds_refl [-7, -3]
  have r1 := holds_trans r0 (holds_context c7_rule20 [-7] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule32 : Holds (normalizedRelatorError .ii_s1_s5) [3, 7] [7, 3] := by
  have h0 := (split [3, 7] [-3, -7] (rotate [-3, -7] [3, 7] source12))
  have l0 := holds_refl [3, 7]
  have r0 := holds_refl [7, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
