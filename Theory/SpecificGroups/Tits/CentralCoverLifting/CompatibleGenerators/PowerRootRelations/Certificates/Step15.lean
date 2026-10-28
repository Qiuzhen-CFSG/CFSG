module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step14

/-! Kernel-checked central word identities, chunk 15.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule203 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [3, 8, 5, 5] [8, 4] := by
  have h0 := c6_rule48
  have l0 := holds_refl [8, 3, 3, 4]
  have l1 := holds_trans l0 (holds_context c6_rule170 [8] [4])
  have r0 := holds_refl [3, 8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule204 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 4, -5] [3, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule203 [] [-5])) (holds_context c6_rule8 [3, 8, 5] []))
  have l0 := holds_refl [8, 4, -5]
  have r0 := holds_refl [3, 8, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule206 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 4, 5] [3, 8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule203 [] [5])) (holds_context c6_rule175 [3, 8] []))
  have l0 := holds_refl [8, 4, 5]
  have r0 := holds_refl [3, 8, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule207 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [5, 8, 3, 8] [-5, 4] := by
  have h0 := c6_rule51
  have l0 := holds_refl [-5, 3, 3, 4]
  have l1 := holds_trans l0 (holds_context c6_rule170 [-5] [4])
  have r0 := holds_refl [5, 8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule208 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 8] [5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule207 [-5] [])) (holds_context c6_rule9 [] [8, 3, 8]))
  have l0 := holds_refl [-5, -5, 4]
  have l1 := holds_trans l0 (holds_context c6_rule26 [] [4])
  have r0 := holds_refl [8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule213 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7, 5] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule170 [] [4, -5, -7, 5])) (holds_context c6_rule126 [3] []))
  have l0 := holds_refl [4, -5, -7, 5]
  have r0 := holds_refl [3, 3, -7, 6]
  have r1 := holds_trans r0 (holds_context c6_rule170 [] [-7, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule214 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7] [-7, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule213 [] [-5])) (holds_context c6_rule8 [4, -5, -7] []))
  have l0 := holds_refl [-7, 6, -5]
  have r0 := holds_refl [4, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule215 : Holds ((normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [4, -7, 6] [-5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule213 [4] [])) (holds_context c6_rule171 [] [-5, -7, 5]))
  have l0 := holds_refl [4, -7, 6]
  have r0 := holds_refl [-5, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule219 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 5, 5, 3] [3, -7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule180 [] [-5])) (holds_context c6_rule30 [-7, -5] []))
  have l0 := holds_refl [3, -7, -5, -5]
  have l1 := holds_trans l0 (holds_context c6_rule26 [3, -7] [])
  have r0 := holds_refl [-7, -5, -5, 3]
  have r1 := holds_trans r0 (holds_context c6_rule26 [-7] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule222 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .iv_s2_s6) [1, 6, 10, 6] [1, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule184 [8] [])) (holds_context c6_rule38 [] [10, 6]))
  have l0 := holds_refl [8, 1, 6, 10]
  have l1 := holds_trans l0 (holds_context c6_rule38 [] [6, 10])
  have l2 := holds_trans l1 (holds_context c6_rule172 [1] [10])
  have r0 := holds_refl [1, 6, 10, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule223 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .iv_s2_s6) [6, 10, 6] [10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule222 [1] [])) (holds_context c6_rule169 [] [6, 10, 6]))
  have l0 := holds_refl [1, 1, 10]
  have l1 := holds_trans l0 (holds_context c6_rule169 [] [10])
  have r0 := holds_refl [6, 10, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule224 : Holds (normalizedRelatorError .iv_s2_s6) [10, 6] [6, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule223 [6] [])) (holds_context c6_rule172 [] [10, 6]))
  have l0 := holds_refl [6, 10]
  have r0 := holds_refl [10, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule230 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ)) [5, 5, 4, 5] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule204 [8] [])) (holds_context c6_rule173 [] [4, -5]))
  have l0 := holds_refl [8, 3, 8, 5]
  have l1 := holds_trans l0 (holds_context c6_rule208 [] [5])
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule231 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ)) [4, 5, 5] [5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule230 [] [-5])) (holds_context c6_rule8 [5, 5, 4] []))
  have l0 := holds_refl [4, -5, -5]
  have l1 := holds_trans l0 (holds_context c6_rule26 [4] [])
  have r0 := holds_refl [5, 5, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule235 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ)) [5, 5, 4, -5] [4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule206 [8] [])) (holds_context c6_rule173 [] [4, 5]))
  have l0 := holds_refl [8, 3, 8, -5]
  have l1 := holds_trans l0 (holds_context c6_rule208 [] [-5])
  have r0 := holds_refl [4, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule251 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, -5, 7] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule214 [] [7])) (holds_context c6_rule13 [4, -5] []))
  have l0 := holds_refl [-7, 6, -5, 7]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule252 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 4, -5] [6, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule251 [7] [])) (holds_context c6_rule12 [] [6, -5, 7]))
  have l0 := holds_refl [7, 4, -5]
  have r0 := holds_refl [6, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule258 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 5, 6] [4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule215 [] [6])) (holds_context c6_rule172 [4, -7] []))
  have l0 := holds_refl [-5, -7, 5, 6]
  have r0 := holds_refl [4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule259 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, 6] [5, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule258 [5] [])) (holds_context c6_rule8 [] [-7, 5, 6]))
  have l0 := holds_refl [5, 4, -7]
  have r0 := holds_refl [-7, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule264 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [3, -7, 6, 7] [5, 5, 6, 4] := by
  have h0 := c6_rule69
  have l0 := holds_refl [4, 5, 5, 6]
  have l1 := holds_trans l0 (holds_context c6_rule231 [] [6])
  have l2 := holds_trans l1 (holds_context c6_rule34 [5, 5] [])
  have r0 := holds_refl [3, -7, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule268 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, -5, 7, 5] [7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule252 [] [5])) (holds_context c6_rule9 [7, 4] []))
  have l0 := holds_refl [6, -5, 7, 5]
  have r0 := holds_refl [7, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule269 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 4] [-5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule268 [6] [])) (holds_context c6_rule172 [] [-5, 7, 5]))
  have l0 := holds_refl [6, 7, 4]
  have r0 := holds_refl [-5, 7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule272 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 5, 4, -7] [5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule259 [7] [])) (holds_context c6_rule12 [] [5, 6]))
  have l0 := holds_refl [7, 5, 4, -7]
  have r0 := holds_refl [5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule273 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 5, 4] [5, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule272 [] [7])) (holds_context c6_rule13 [7, 5, 4] []))
  have l0 := holds_refl [5, 6, 7]
  have r0 := holds_refl [7, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule276 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 3, 7, 4] [-5, 3, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule269 [] [3])) (holds_context c6_rule29 [6, 7] []))
  have l0 := holds_refl [-5, 7, 5, 3]
  have l1 := holds_trans l0 (holds_context c6_rule183 [-5] [])
  have r0 := holds_refl [6, 7, 3, 4]
  have r1 := holds_trans r0 (holds_context c6_rule33 [6] [4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule292 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [9, 6, 3, 7, 7] [4, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule54 [9] [])) (holds_context c6_rule16 [] [4, 9, 4]))
  have l0 := holds_refl [9, 6, 3, 7, 7]
  have r0 := holds_refl [4, 9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule293 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s5 * normalizedRelatorError .iv_s7_s2) [4, 9, 4, 7] [9, 6, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule292 [] [7])) (holds_context c6_rule176 [9, 6, 3] []))
  have l0 := holds_refl [4, 9, 4, 7]
  have r0 := holds_refl [9, 6, 3, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule295 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 3, 4] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule54 [] [3])) (holds_context c6_rule29 [-9, 4, 9] []))
  have l0 := holds_refl [6, 3, 7, 7, 3]
  have l1 := holds_trans l0 (holds_context c6_rule33 [6, 3, 7] [])
  have l2 := holds_trans l1 (holds_context c6_rule33 [6, 3] [7])
  have l3 := holds_trans l2 (holds_context c6_rule170 [6] [7, 7])
  have r0 := holds_refl [-9, 4, 9, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule296 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [4, 9, 3, 4] [9, 6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule295 [9] [])) (holds_context c6_rule16 [] [4, 9, 3, 4]))
  have l0 := holds_refl [9, 6, 7, 7]
  have r0 := holds_refl [4, 9, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule297 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 3] [6, 7, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule295 [] [4])) (holds_context c6_rule171 [-9, 4, 9, 3] []))
  have l0 := holds_refl [6, 7, 7, 4]
  have r0 := holds_refl [-9, 4, 9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule324 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 6, 5] [-5, 3, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule64 [] [-5])) (holds_context c6_rule8 [7, 6, 5] []))
  have l0 := holds_refl [6, 3, 7, 4, -5]
  have l1 := holds_trans l0 (holds_context c6_rule276 [] [-5])
  have l2 := holds_trans l1 (holds_context c6_rule8 [-5, 3, 7] [])
  have r0 := holds_refl [7, 6, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule325 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 3, 7, -5] [7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule324 [] [-5])) (holds_context c6_rule8 [7, 6] []))
  have l0 := holds_refl [-5, 3, 7, -5]
  have r0 := holds_refl [7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule326 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 7, -5] [5, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule325 [5] [])) (holds_context c6_rule8 [] [3, 7, -5]))
  have l0 := holds_refl [5, 7, 6]
  have r0 := holds_refl [3, 7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule327 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -7, -5, 7] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule324 [-7] [])) (holds_context c6_rule13 [] [6, 5]))
  have l0 := holds_refl [-7, -5, 3, 7]
  have l1 := holds_trans l0 (holds_context c6_rule180 [] [7])
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule328 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, -7] [3, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule327 [] [-7])) (holds_context c6_rule12 [3, -7, -5] []))
  have l0 := holds_refl [6, 5, -7]
  have r0 := holds_refl [3, -7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule329 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, -5, 7] [3, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule327 [3] [])) (holds_context c6_rule170 [] [-7, -5, 7]))
  have l0 := holds_refl [3, 6, 5]
  have r0 := holds_refl [-7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule332 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7, 6] [-5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule326 [-7] [])) (holds_context c6_rule32 [] [7, -5]))
  have l0 := holds_refl [-7, 5, 7, 6]
  have r0 := holds_refl [3, -7, 7, -5]
  have r1 := holds_trans r0 (holds_context c6_rule13 [3] [-5])
  have r2 := holds_trans r1 (holds_context c6_rule30 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule333 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7] [-5, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule332 [] [6])) (holds_context c6_rule172 [-7, 5, 7] []))
  have l0 := holds_refl [-5, 3, 6]
  have r0 := holds_refl [-7, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule335 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 3, 7, 6] [7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule326 [3] [])) (holds_context c6_rule170 [] [7, -5]))
  have l0 := holds_refl [3, 5, 7, 6]
  have l1 := holds_trans l0 (holds_context c6_rule31 [] [7, 6])
  have r0 := holds_refl [7, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule336 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [3, 7, 6] [-5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule335 [-5] [])) (holds_context c6_rule9 [] [3, 7, 6]))
  have l0 := holds_refl [-5, 7, -5]
  have r0 := holds_refl [3, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
