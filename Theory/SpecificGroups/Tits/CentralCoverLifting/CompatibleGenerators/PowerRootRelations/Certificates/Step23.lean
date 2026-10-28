module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step22

/-! Kernel-checked central word identities, chunk 23.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c7_rule163 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7, 5] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule129 [] [4, -5, -7, 5])) (holds_context c7_rule115 [3] []))
  have l0 := holds_refl [4, -5, -7, 5]
  have r0 := holds_refl [3, -7, 3, 6]
  have r1 := holds_trans r0 (holds_context c7_rule31 [] [3, 6])
  have r2 := holds_trans r1 (holds_context c7_rule129 [-7] [6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule164 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7] [-7, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule163 [] [-5])) (holds_context c7_rule8 [4, -5, -7] []))
  have l0 := holds_refl [-7, 6, -5]
  have r0 := holds_refl [4, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule165 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [4, -7, 6] [-5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule163 [4] [])) (holds_context c7_rule130 [] [-5, -7, 5]))
  have l0 := holds_refl [4, -7, 6]
  have r0 := holds_refl [-5, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule169 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, 7, 6] [8, 3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule137 [] [-5])) (holds_context c7_rule29 [4, -5] []))
  have l0 := holds_refl [3, 4, -5, -5]
  have l1 := holds_trans l0 (holds_context c7_rule25 [3, 4] [])
  have l2 := holds_trans l1 (holds_context c7_rule153 [3] [])
  have l3 := holds_trans l2 (holds_context c7_rule57 [] [])
  have r0 := holds_refl [4, -5, -5, 3]
  have r1 := holds_trans r0 (holds_context c7_rule25 [4] [3])
  have r2 := holds_trans r1 (holds_context c7_rule153 [] [3])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule185 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 8, 3, 4] [8, 5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule156 [] [3])) (holds_context c7_rule28 [3, 8] []))
  have l0 := holds_refl [8, 5, 5, 3]
  have r0 := holds_refl [3, 8, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule187 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, 7, 3] [8, 6, 3, 8] := by
  have h0 := c7_rule60
  have l0 := holds_refl [6, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c7_rule157 [6] [])
  have l2 := holds_trans l1 (holds_context c7_rule145 [] [3, 8])
  have r0 := holds_refl [-7, 6, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule188 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [5, 5, 6, 4] [8, 3, 8, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule157 [] [6])) (holds_context c7_rule33 [5, 5] []))
  have l0 := holds_refl [8, 3, 8, 6]
  have r0 := holds_refl [5, 5, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule192 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6) [5, 5, 3, 8] [8, 5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule161 [3] [])) (holds_context c7_rule30 [] [5, 8]))
  have l0 := holds_refl [3, 8, 3, 4]
  have l1 := holds_trans l0 (holds_context c7_rule185 [] [])
  have r0 := holds_refl [5, 3, 5, 8]
  have r1 := holds_trans r0 (holds_context c7_rule30 [5] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule198 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, -5, 7] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule164 [] [7])) (holds_context c7_rule13 [4, -5] []))
  have l0 := holds_refl [-7, 6, -5, 7]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule199 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, -5, 7] [7, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule198 [7] [])) (holds_context c7_rule12 [] [6, -5, 7]))
  have l0 := holds_refl [7, 4, -5]
  have r0 := holds_refl [6, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule202 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 5, 6] [4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule165 [] [6])) (holds_context c7_rule131 [4, -7] []))
  have l0 := holds_refl [-5, -7, 5, 6]
  have r0 := holds_refl [4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule203 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, 6] [5, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule202 [5] [])) (holds_context c7_rule8 [] [-7, 5, 6]))
  have l0 := holds_refl [5, 4, -7]
  have r0 := holds_refl [-7, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule207 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 4, -5] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule199 [6] [])) (holds_context c7_rule131 [] [-5, 7]))
  have l0 := holds_refl [6, 7, 4, -5]
  have r0 := holds_refl [-5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule208 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 4] [-5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule207 [] [5])) (holds_context c7_rule9 [6, 7, 4] []))
  have l0 := holds_refl [-5, 7, 5]
  have r0 := holds_refl [6, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule212 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, 3, 6] [5, 3, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule203 [3] [])) (holds_context c7_rule31 [] [5, 6]))
  have l0 := holds_refl [3, 5, 4, -7]
  have l1 := holds_trans l0 (holds_context c7_rule30 [] [4, -7])
  have r0 := holds_refl [-7, 3, 5, 6]
  have r1 := holds_trans r0 (holds_context c7_rule30 [-7] [6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule237 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [7, 3, 4, -9, 4] [-7, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule54 [3] [])) (holds_context c7_rule31 [] [3, 6, -9]))
  have l0 := holds_refl [3, 7, 4, -9, 4]
  have l1 := holds_trans l0 (holds_context c7_rule32 [] [4, -9, 4])
  have r0 := holds_refl [-7, 3, 3, 6, -9]
  have r1 := holds_trans r0 (holds_context c7_rule129 [-7] [6, -9])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule238 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [3, 4, -9, 4] [7, 7, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule237 [-7] [])) (holds_context c7_rule13 [] [3, 4, -9, 4]))
  have l0 := holds_refl [-7, -7, 6, -9]
  have l1 := holds_trans l0 (holds_context c7_rule26 [] [6, -9])
  have r0 := holds_refl [3, 4, -9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule246 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [-5, -7, 5, 7, 6] [5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule57 [4] [])) (holds_context c7_rule28 [] [8, 3, 8]))
  have l0 := holds_refl [4, -7, 6, 7, 6]
  have l1 := holds_trans l0 (holds_context c7_rule165 [] [7, 6])
  have r0 := holds_refl [3, 4, 8, 3, 8]
  have r1 := holds_trans r0 (holds_context c7_rule34 [3] [3, 8])
  have r2 := holds_trans r1 (holds_context c7_rule156 [] [3, 8])
  have r3 := holds_trans r2 (holds_context c7_rule192 [8] [])
  have r4 := holds_trans r3 (holds_context c7_rule132 [] [5, 5, 3])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r4)) (by central_nf)

theorem c7_rule247 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7, 6] [-5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule246 [5] [])) (holds_context c7_rule8 [] [-7, 5, 7, 6]))
  have l0 := holds_refl [5, 5, 5, 3]
  have l1 := holds_trans l0 (holds_context c7_rule134 [] [3])
  have r0 := holds_refl [-7, 5, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule248 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 3] [5, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule247 [7] [])) (holds_context c7_rule12 [] [5, 7, 6]))
  have l0 := holds_refl [7, -5, 3]
  have r0 := holds_refl [5, 7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule249 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7] [-5, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule247 [] [6])) (holds_context c7_rule131 [-7, 5, 7] []))
  have l0 := holds_refl [-5, 3, 6]
  have r0 := holds_refl [-7, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule252 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 6, 5] [7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule248 [] [5])) (holds_context c7_rule30 [7, -5] []))
  have l0 := holds_refl [5, 7, 6, 5]
  have r0 := holds_refl [7, -5, 5, 3]
  have r1 := holds_trans r0 (holds_context c7_rule9 [7] [3])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule253 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 6, 5] [-5, 7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule252 [-5] [])) (holds_context c7_rule9 [] [7, 6, 5]))
  have l0 := holds_refl [-5, 7, 3]
  have r0 := holds_refl [7, 6, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule257 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 6, 3] [7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule248 [] [3])) (holds_context c7_rule129 [7, -5] []))
  have l0 := holds_refl [5, 7, 6, 3]
  have r0 := holds_refl [7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule258 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 6, 3] [-5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule257 [-5] [])) (holds_context c7_rule9 [] [7, 6, 3]))
  have l0 := holds_refl [-5, 7, -5]
  have r0 := holds_refl [7, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule259 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 3, 6, -7] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule249 [] [-7])) (holds_context c7_rule12 [-7, 5] []))
  have l0 := holds_refl [-5, 3, 6, -7]
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule260 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 6, -7] [5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule259 [5] [])) (holds_context c7_rule8 [] [3, 6, -7]))
  have l0 := holds_refl [5, -7, 5]
  have r0 := holds_refl [3, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule262 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [-5, 3, 6, 3] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule249 [3] [])) (holds_context c7_rule31 [] [5, 7]))
  have l0 := holds_refl [3, -5, 3, 6]
  have l1 := holds_trans l0 (holds_context c7_rule29 [] [3, 6])
  have l2 := holds_trans l1 (holds_context c7_rule129 [-5] [6])
  have r0 := holds_refl [-7, 3, 5, 7]
  have r1 := holds_trans r0 (holds_context c7_rule30 [-7] [7])
  have r2 := holds_trans r1 (holds_context c7_rule32 [-7, 5] [])
  have r3 := holds_trans r2 (holds_context c7_rule249 [] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r3))) (by central_nf)

theorem c7_rule263 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [3, 6, 3] [6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule262 [5] [])) (holds_context c7_rule8 [] [3, 6, 3]))
  have l0 := holds_refl [5, -5, 6]
  have l1 := holds_trans l0 (holds_context c7_rule8 [] [6])
  have r0 := holds_refl [3, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule264 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ)) [3, 6] [6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule263 [3] [])) (holds_context c7_rule129 [] [6, 3]))
  have l0 := holds_refl [3, 6]
  have r0 := holds_refl [6, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule265 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, -7, 3] [5, -7, 5] := by
  have h0 := c7_rule260
  have l0 := holds_refl [3, 6, -7]
  have l1 := holds_trans l0 (holds_context c7_rule264 [] [-7])
  have l2 := holds_trans l1 (holds_context c7_rule31 [6] [])
  have r0 := holds_refl [5, -7, 5]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule266 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [3, 8, 6] [6, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule264 [] [8])) (holds_context c7_rule145 [3] []))
  have l0 := holds_refl [6, 3, 8]
  have r0 := holds_refl [3, 8, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule267 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, -5, 7, 3] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule253 [-7] [])) (holds_context c7_rule13 [] [6, 5]))
  have l0 := holds_refl [-7, -5, 7, 3]
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule268 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, 3] [-7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule267 [] [3])) (holds_context c7_rule129 [-7, -5, 7] []))
  have l0 := holds_refl [6, 5, 3]
  have r0 := holds_refl [-7, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule271 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ)) [7, 5, -7, 5] [-5, 7, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule258 [] [-7])) (holds_context c7_rule31 [7, 6] []))
  have l0 := holds_refl [-5, 7, -5, -7]
  have r0 := holds_refl [7, 6, -7, 3]
  have r1 := holds_trans r0 (holds_context c7_rule265 [7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule277 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-7, 6, 3, -9] [7, 4, -9, 4] := by
  have h0 := c7_rule54
  have l0 := holds_refl [-7, 3, 6, -9]
  have l1 := holds_trans l0 (holds_context c7_rule264 [-7] [-9])
  have r0 := holds_refl [7, 4, -9, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule289 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 6, 3] [5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule264 [7, -5] [])) (holds_context c7_rule248 [] [6]))
  have l0 := holds_refl [7, -5, 6, 3]
  have r0 := holds_refl [5, 7, 6, 6]
  have r1 := holds_trans r0 (holds_context c7_rule131 [5, 7] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule290 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 6] [5, 7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule289 [] [3])) (holds_context c7_rule129 [7, -5, 6] []))
  have l0 := holds_refl [5, 7, 3]
  have r0 := holds_refl [7, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule295 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, 6, 3] [8, 3, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule265 [] [6])) (holds_context c7_rule264 [6, -7] []))
  have l0 := holds_refl [5, -7, 5, 6]
  have l1 := holds_trans l0 (holds_context c7_rule203 [5] [])
  have l2 := holds_trans l1 (holds_context c7_rule157 [] [-7])
  have r0 := holds_refl [6, -7, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule317 : Holds ((normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [6, 5, 5] [5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule60 [4] [])) (holds_context c7_rule33 [] [5, 5, 4]))
  have l0 := holds_refl [4, -7, 6, 7, 3]
  have l1 := holds_trans l0 (holds_context c7_rule165 [] [7, 3])
  have l2 := holds_trans l1 (holds_context c7_rule249 [-5] [3])
  have l3 := holds_trans l2 (holds_context c7_rule25 [] [3, 6, 3])
  have l4 := holds_trans l3 (holds_context c7_rule264 [5, 5] [3])
  have l5 := holds_trans l4 (holds_context c7_rule129 [5, 5, 6] [])
  have r0 := holds_refl [6, 4, 5, 5, 4]
  have r1 := holds_trans r0 (holds_context c7_rule153 [6] [4])
  have r2 := holds_trans r1 (holds_context c7_rule145 [] [3, 8, 4])
  have r3 := holds_trans r2 (holds_context c7_rule156 [8, 6] [])
  have r4 := holds_trans r3 (holds_context c7_rule145 [8] [5, 5])
  have r5 := holds_trans r4 (holds_context c7_rule132 [] [6, 5, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r5))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
