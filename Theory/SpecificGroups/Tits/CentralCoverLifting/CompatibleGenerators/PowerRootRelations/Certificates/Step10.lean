module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step09

/-! Kernel-checked central word identities, chunk 10.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c2_rule906 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 2, 9, 3, -7] [-5, 2, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule327 [3] [])) (holds_context c2_rule229 [] [-5, 2, 8]))
  have l0 := holds_refl [3, 2, 9, 3, -7]
  have r0 := holds_refl [-5, 2, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule907 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-5, 2, 8, 7] [3, 2, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule906 [] [7])) (holds_context c2_rule13 [3, 2, 9, 3] []))
  have l0 := holds_refl [-5, 2, 8, 7]
  have r0 := holds_refl [3, 2, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1013 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ)) [5, 5, 6] [6, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule376 [8] [])) (holds_context c2_rule232 [] [6, 5, 5]))
  have l0 := holds_refl [8, 4, 6, 3, 8]
  have l1 := holds_trans l0 (holds_context c2_rule36 [] [6, 3, 8])
  have l2 := holds_trans l1 (holds_context c2_rule569 [4, 8] [8])
  have l3 := holds_trans l2 (holds_context c2_rule308 [4, 8, 3] [])
  have l4 := holds_trans l3 (holds_context c2_rule322 [4] [6])
  have l5 := holds_trans l4 (holds_context c2_rule230 [] [5, 5, 6])
  have r0 := holds_refl [6, 5, 5]
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1043 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 6, 7, 5, 5] [7, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule432 [6] [])) (holds_context c2_rule231 [] [7, 4, 6]))
  have l0 := holds_refl [6, 3, 7, 5, 5]
  have l1 := holds_trans l0 (holds_context c2_rule569 [] [7, 5, 5])
  have r0 := holds_refl [7, 4, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1044 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [7, 4, 6, -5] [3, 6, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1043 [] [-5])) (holds_context c2_rule8 [3, 6, 7, 5] []))
  have l0 := holds_refl [7, 4, 6, -5]
  have r0 := holds_refl [3, 6, 7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1074 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [4, 5, 5, -7, 6] [3, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule452 [-5] [])) (holds_context c2_rule27 [] [4, -7, 6]))
  have l0 := holds_refl [-5, 3, 5, 6, -7]
  have l1 := holds_trans l0 (holds_context c2_rule31 [] [5, 6, -7])
  have l2 := holds_trans l1 (holds_context c2_rule9 [3] [6, -7])
  have r0 := holds_refl [5, 5, 4, -7, 6]
  have r1 := holds_trans r0 (holds_context c2_rule317 [] [-7, 6])
  have r2 := holds_trans r1 (holds_context c2_rule322 [] [-7, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c2_rule1075 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 5, -7, 6] [4, 3, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1074 [4] [])) (holds_context c2_rule230 [] [5, 5, -7, 6]))
  have l0 := holds_refl [4, 3, 6, -7]
  have r0 := holds_refl [5, 5, -7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1093 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 2, 9, 3, -5] [-7, 2, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule481 [] [3])) (holds_context c2_rule229 [-7, 2, 4] []))
  have l0 := holds_refl [3, 2, 9, -5, 3]
  have l1 := holds_trans l0 (holds_context c2_rule31 [3, 2, 9] [])
  have r0 := holds_refl [-7, 2, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1123 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, -7, 8] [8, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule491 [] [2])) (holds_context c2_rule42 [3, -7, 2] []))
  have l0 := holds_refl [2, 9, 3, -5, 2]
  have l1 := holds_trans l0 (holds_context c2_rule624 [2] [])
  have l2 := holds_trans l1 (holds_context c2_rule228 [] [8, 6, 7])
  have r0 := holds_refl [3, -7, 2, 2, 8]
  have r1 := holds_trans r0 (holds_context c2_rule228 [3, -7] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule1128 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 8, 6, 7] [3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1123 [7] [])) (holds_context c2_rule34 [] [-7, 8]))
  have l0 := holds_refl [7, 8, 6, 7]
  have r0 := holds_refl [3, 7, -7, 8]
  have r1 := holds_trans r0 (holds_context c2_rule12 [3] [8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule1129 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 8, 6] [3, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1128 [] [-7])) (holds_context c2_rule12 [7, 8, 6] []))
  have l0 := holds_refl [3, 8, -7]
  have r0 := holds_refl [7, 8, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1131 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [3, 8, 6, 7] [-7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1123 [3] [])) (holds_context c2_rule229 [] [-7, 8]))
  have l0 := holds_refl [3, 8, 6, 7]
  have r0 := holds_refl [-7, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1132 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 8, -7] [3, 8, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1131 [] [-7])) (holds_context c2_rule12 [3, 8, 6] []))
  have l0 := holds_refl [-7, 8, -7]
  have r0 := holds_refl [3, 8, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1135 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 6, -7, 8] [8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1123 [6] [])) (holds_context c2_rule569 [] [-7, 8]))
  have l0 := holds_refl [6, 8, 6, 7]
  have l1 := holds_trans l0 (holds_context c2_rule308 [] [6, 7])
  have l2 := holds_trans l1 (holds_context c2_rule231 [8] [7])
  have r0 := holds_refl [3, 6, -7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1137 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 6, -7] [8, 7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1135 [] [8])) (holds_context c2_rule232 [3, 6, -7] []))
  have l0 := holds_refl [8, 7, 8]
  have r0 := holds_refl [3, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1142 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 8, -7, 6] [7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1129 [] [6])) (holds_context c2_rule231 [7, 8] []))
  have l0 := holds_refl [3, 8, -7, 6]
  have r0 := holds_refl [7, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1143 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [3, 7, 8] [8, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1142 [3] [])) (holds_context c2_rule229 [] [8, -7, 6]))
  have l0 := holds_refl [3, 7, 8]
  have r0 := holds_refl [8, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1144 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 8, -7, 8] [7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1129 [] [8])) (holds_context c2_rule308 [7, 8] []))
  have l0 := holds_refl [3, 8, -7, 8]
  have r0 := holds_refl [7, 8, 8, 6]
  have r1 := holds_trans r0 (holds_context c2_rule232 [7] [6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule1145 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [3, 7, 6] [8, -7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1144 [3] [])) (holds_context c2_rule229 [] [8, -7, 8]))
  have l0 := holds_refl [3, 7, 6]
  have r0 := holds_refl [8, -7, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1150 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 8, 3, -7] [3, 8, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1132 [] [3])) (holds_context c2_rule33 [-7, 8] []))
  have l0 := holds_refl [3, 8, 6, 3]
  have l1 := holds_trans l0 (holds_context c2_rule569 [3, 8] [])
  have r0 := holds_refl [-7, 8, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1164 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [8, 7, 8, 7] [3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1137 [] [7])) (holds_context c2_rule13 [3, 6] []))
  have l0 := holds_refl [8, 7, 8, 7]
  have r0 := holds_refl [3, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1165 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 8, 7] [8, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1164 [8] [])) (holds_context c2_rule232 [] [7, 8, 7]))
  have l0 := holds_refl [8, 3, 6]
  have r0 := holds_refl [7, 8, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1191 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [8, -7, 8, 5] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1145 [] [5])) (holds_context c2_rule537 [3] []))
  have l0 := holds_refl [8, -7, 8, 5]
  have r0 := holds_refl [3, 3, -5, 7]
  have r1 := holds_trans r0 (holds_context c2_rule229 [] [-5, 7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule1192 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 8, 5] [8, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1191 [8] [])) (holds_context c2_rule232 [] [-7, 8, 5]))
  have l0 := holds_refl [8, -5, 7]
  have r0 := holds_refl [-7, 8, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1194 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [8, -7, 8, 3] [7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1145 [] [3])) (holds_context c2_rule569 [3, 7] []))
  have l0 := holds_refl [8, -7, 8, 3]
  have r0 := holds_refl [3, 7, 3, 6]
  have r1 := holds_trans r0 (holds_context c2_rule34 [3] [6])
  have r2 := holds_trans r1 (holds_context c2_rule229 [] [7, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c2_rule1195 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 8, 3] [8, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1194 [8] [])) (holds_context c2_rule232 [] [-7, 8, 3]))
  have l0 := holds_refl [8, 7, 6]
  have r0 := holds_refl [-7, 8, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1196 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [3, 8, 3, 6] [8, -7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1165 [3] [])) (holds_context c2_rule1143 [] [7]))
  have l0 := holds_refl [3, 8, 3, 6]
  have r0 := holds_refl [8, -7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1213 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [8, -7, 6, 7] [8, 7, 6, -7] := by
  have h0 := c2_rule1150
  have l0 := holds_refl [-7, 8, 3, -7]
  have l1 := holds_trans l0 (holds_context c2_rule1195 [] [-7])
  have r0 := holds_refl [3, 8, 3, 6]
  have r1 := holds_trans r0 (holds_context c2_rule1196 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule1216 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ)) [-7, 4, 5, 5] [4, 5, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1195 [] [8])) (holds_context c2_rule322 [-7] []))
  have l0 := holds_refl [8, 7, 6, 8]
  have l1 := holds_trans l0 (holds_context c2_rule308 [8, 7] [])
  have l2 := holds_trans l1 (holds_context c2_rule1129 [8] [])
  have l3 := holds_trans l2 (holds_context c2_rule322 [] [-7])
  have r0 := holds_refl [-7, 4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1270 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ)) [4, 7, 7, 4, 6] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule524 [] [4])) (holds_context c2_rule71 [3] []))
  have l0 := holds_refl [4, 7, 7, 6, 4]
  have l1 := holds_trans l0 (holds_context c2_rule35 [4, 7, 7] [])
  have r0 := holds_refl [3, 6, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c2_rule569 [3] [7, 7])
  have r2 := holds_trans r1 (holds_context c2_rule229 [] [6, 7, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c2_rule1272 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ)) [6, 7, 7, 6] [4, 7, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1270 [] [6])) (holds_context c2_rule231 [4, 7, 7, 4] []))
  have l0 := holds_refl [6, 7, 7, 6]
  have r0 := holds_refl [4, 7, 7, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1299 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [8, -7, 8, 7, 2] [2, 3, -7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule538 [] [7, 2])) (holds_context c2_rule250 [-5, 7] []))
  have l0 := holds_refl [3, 7, 6, 7, 2]
  have l1 := holds_trans l0 (holds_context c2_rule1145 [] [7, 2])
  have r0 := holds_refl [-5, 7, 2, -7, 5]
  have r1 := holds_trans r0 (holds_context c2_rule250 [] [-7, 5])
  have r2 := holds_trans r1 (holds_context c2_rule566 [2, -7] [])
  have r3 := holds_trans r2 (holds_context c2_rule33 [2] [6, -7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

theorem c2_rule1379 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [3, 5, -7, -5, 4] [3, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule564 [] [4, 5, 5])) (holds_context c2_rule381 [3, 5, -7] []))
  have l0 := holds_refl [6, -7, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c2_rule1216 [6] [])
  have l2 := holds_trans l1 (holds_context c2_rule35 [] [5, 5, -7])
  have l3 := holds_trans l2 (holds_context c2_rule444 [4] [])
  have l4 := holds_trans l3 (holds_context c2_rule230 [] [-7, 6, 3])
  have l5 := holds_trans l4 (holds_context c2_rule569 [-7] [])
  have l6 := holds_trans l5 (holds_context c2_rule33 [] [6])
  have r0 := holds_refl [3, 5, -7, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1380 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [5, -7, -5, 4] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1379 [3] [])) (holds_context c2_rule229 [] [5, -7, -5, 4]))
  have l0 := holds_refl [3, 3, -7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule229 [] [-7, 6])
  have r0 := holds_refl [5, -7, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1381 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 6] [-7, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1380 [-5] [])) (holds_context c2_rule9 [] [-7, -5, 4]))
  have l0 := holds_refl [-5, -7, 6]
  have r0 := holds_refl [-7, -5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1382 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [5, -7, -5] [-7, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1380 [] [4])) (holds_context c2_rule230 [5, -7, -5] []))
  have l0 := holds_refl [-7, 6, 4]
  have l1 := holds_trans l0 (holds_context c2_rule35 [-7] [])
  have r0 := holds_refl [5, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1385 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 4, 6] [-7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1381 [] [4])) (holds_context c2_rule35 [-5, -7] []))
  have l0 := holds_refl [-7, -5, 4, 4]
  have l1 := holds_trans l0 (holds_context c2_rule230 [-7, -5] [])
  have r0 := holds_refl [-5, -7, 4, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1386 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 4] [-7, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1385 [] [6])) (holds_context c2_rule231 [-5, -7, 4] []))
  have l0 := holds_refl [-7, -5, 6]
  have r0 := holds_refl [-5, -7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule1388 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [-7, -5, 4, 6] [-5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1381 [] [6])) (holds_context c2_rule231 [-5, -7] []))
  have l0 := holds_refl [-7, -5, 4, 6]
  have r0 := holds_refl [-5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule1389 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [-5, 4, 6] [7, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule1388 [7] [])) (holds_context c2_rule12 [] [-5, 4, 6]))
  have l0 := holds_refl [7, -5, -7]
  have r0 := holds_refl [-5, 4, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
