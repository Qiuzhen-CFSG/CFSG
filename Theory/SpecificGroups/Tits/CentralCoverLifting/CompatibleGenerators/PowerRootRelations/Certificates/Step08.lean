module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step07

/-! Kernel-checked central word identities, chunk 8.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c2_rule231 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c2_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context c2_rule24 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule232 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c2_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context c2_rule25 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule234 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule27 [5] [])) (holds_context c2_rule8 [] [-5]))
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule235 : Holds (normalizedRelatorError .i_s5) [7, 7, 7] [-7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule28 [7] [])) (holds_context c2_rule12 [] [-7]))
  have l0 := holds_refl [7, 7, 7]
  have r0 := holds_refl [-7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule237 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [-5, 4, 3] [3, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule31 [] [4])) (holds_context c2_rule30 [-5] []))
  have l0 := holds_refl [3, -5, 4]
  have r0 := holds_refl [-5, 4, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule240 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, 4, 3] [3, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule34 [] [4])) (holds_context c2_rule30 [7] []))
  have l0 := holds_refl [3, 7, 4]
  have r0 := holds_refl [7, 4, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule250 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [-5, 7, 2] [2, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule52 [-5] [])) (holds_context c2_rule48 [] [5]))
  have l0 := holds_refl [-5, 7, 2]
  have r0 := holds_refl [2, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule251 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, -5, -9] [-7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule53 [] [-9])) (holds_context c2_rule16 [-7, 2] []))
  have l0 := holds_refl [2, -5, -9]
  have r0 := holds_refl [-7, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule252 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ)) [-7, 5, 2] [2, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule53 [] [7])) (holds_context c2_rule47 [-7] []))
  have l0 := holds_refl [2, -5, 7]
  have r0 := holds_refl [-7, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule254 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 7, 2] [9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule228 [] [9, 5])) (holds_context c2_rule52 [2] []))
  have l0 := holds_refl [9, 5]
  have r0 := holds_refl [2, 7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule255 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, -7, 2] [-5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule251 [2] [])) (holds_context c2_rule228 [] [-5, -9]))
  have l0 := holds_refl [2, -7, 2]
  have r0 := holds_refl [-5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule256 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [9, 5, 2] [2, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule254 [] [2])) (holds_context c2_rule228 [2, 7] []))
  have l0 := holds_refl [9, 5, 2]
  have r0 := holds_refl [2, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule263 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s3 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [5, 5, 2, 9] [-5, 2, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule48 [-5] [])) (holds_context c2_rule27 [] [2, 9]))
  have l0 := holds_refl [-5, 2, -7]
  have r0 := holds_refl [5, 5, 2, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule273 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [2, 8, 5, 2] [4, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule51 [4] [])) (holds_context c2_rule42 [] [5, 2]))
  have l0 := holds_refl [4, 9, 7]
  have r0 := holds_refl [2, 8, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule292 : Holds ((normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [2, -9, -7, -9] [9, -5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule54 [9] [])) (holds_context c2_rule45 [] [-7, -9]))
  have l0 := holds_refl [9, -5, 2]
  have r0 := holds_refl [2, -9, -7, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule306 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [4, 8, 6, 8] [4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule60 [8] [])) (holds_context c2_rule36 [] [6, 8]))
  have l0 := holds_refl [8, 4, 8, 6]
  have l1 := holds_trans l0 (holds_context c2_rule36 [] [8, 6])
  have l2 := holds_trans l1 (holds_context c2_rule232 [4] [6])
  have r0 := holds_refl [4, 8, 6, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule307 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [8, 6, 8] [6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule306 [4] [])) (holds_context c2_rule230 [] [8, 6, 8]))
  have l0 := holds_refl [4, 4, 6]
  have l1 := holds_trans l0 (holds_context c2_rule230 [] [6])
  have r0 := holds_refl [8, 6, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule308 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [6, 8] [8, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule307 [8] [])) (holds_context c2_rule232 [] [6, 8]))
  have l0 := holds_refl [8, 6]
  have r0 := holds_refl [6, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule315 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [8, 5, 5, 4] [3, 8] := by
  have h0 := c2_rule66
  have l0 := holds_refl [3, 8, 3, 3]
  have l1 := holds_trans l0 (holds_context c2_rule229 [3, 8] [])
  have r0 := holds_refl [8, 5, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule316 : Holds (normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 5, 5] [4, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule315 [] [4])) (holds_context c2_rule230 [8, 5, 5] []))
  have l0 := holds_refl [3, 8, 4]
  have l1 := holds_trans l0 (holds_context c2_rule36 [3] [])
  have l2 := holds_trans l1 (holds_context c2_rule30 [] [8])
  have r0 := holds_refl [8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule317 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [5, 5, 4] [8, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule315 [8] [])) (holds_context c2_rule232 [] [5, 5, 4]))
  have l0 := holds_refl [8, 3, 8]
  have r0 := holds_refl [5, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule318 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [5, 8, 3, 8] [-5, 4] := by
  have h0 := c2_rule68
  have l0 := holds_refl [-5, 4, 3, 3]
  have l1 := holds_trans l0 (holds_context c2_rule237 [] [3])
  have l2 := holds_trans l1 (holds_context c2_rule237 [3] [])
  have l3 := holds_trans l2 (holds_context c2_rule229 [] [-5, 4])
  have r0 := holds_refl [5, 8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule319 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [-5, 4, 8] [5, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule318 [] [8])) (holds_context c2_rule232 [5, 8, 3] []))
  have l0 := holds_refl [-5, 4, 8]
  have r0 := holds_refl [5, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule320 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [4, 5, 5, 8] [8, 3] := by
  have h0 := c2_rule70
  have l0 := holds_refl [3, 3, 8, 3]
  have l1 := holds_trans l0 (holds_context c2_rule229 [] [8, 3])
  have r0 := holds_refl [4, 5, 5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule322 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6) [8, 3, 8] [4, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule320 [] [8])) (holds_context c2_rule232 [4, 5, 5] []))
  have l0 := holds_refl [8, 3, 8]
  have r0 := holds_refl [4, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule327 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -5, 2, 8] [2, 9, 3, -7] := by
  have h0 := c2_rule105
  have l0 := holds_refl [-5, 4, 3, 2]
  have l1 := holds_trans l0 (holds_context c2_rule237 [] [2])
  have l2 := holds_trans l1 (holds_context c2_rule42 [3, -5] [])
  have r0 := holds_refl [2, 9, 3, -7]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule374 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [4, 3, 8, 5] [8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule316 [] [5])) (holds_context c2_rule234 [8] []))
  have l0 := holds_refl [4, 3, 8, 5]
  have r0 := holds_refl [8, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule375 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [3, 8, 5] [4, 8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule374 [4] [])) (holds_context c2_rule230 [] [3, 8, 5]))
  have l0 := holds_refl [4, 8, -5]
  have r0 := holds_refl [3, 8, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule376 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6, 5, 5] [4, 6, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule316 [6] [])) (holds_context c2_rule308 [] [5, 5]))
  have l0 := holds_refl [6, 4, 3, 8]
  have l1 := holds_trans l0 (holds_context c2_rule35 [] [3, 8])
  have r0 := holds_refl [8, 6, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule381 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ)) [5, 4, 5, 5] [-5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule317 [5] [])) (holds_context c2_rule234 [] [4]))
  have l0 := holds_refl [5, 8, 3, 8]
  have l1 := holds_trans l0 (holds_context c2_rule322 [5] [])
  have r0 := holds_refl [-5, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule388 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6, 3, 8] [4, 6, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule322 [6] [])) (holds_context c2_rule308 [] [3, 8]))
  have l0 := holds_refl [6, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c2_rule35 [] [5, 5])
  have r0 := holds_refl [8, 6, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule431 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [-7, 6, 7, 4, 6] [3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule79 [] [4])) (holds_context c2_rule35 [-7, 6, 7] []))
  have l0 := holds_refl [4, 3, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c2_rule317 [4, 3] [])
  have l2 := holds_trans l1 (holds_context c2_rule322 [4, 3] [])
  have l3 := holds_trans l2 (holds_context c2_rule30 [4] [5, 5])
  have l4 := holds_trans l3 (holds_context c2_rule230 [] [3, 5, 5])
  have r0 := holds_refl [-7, 6, 7, 4, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule432 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [6, 7, 4, 6] [3, 7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule431 [7] [])) (holds_context c2_rule12 [] [6, 7, 4, 6]))
  have l0 := holds_refl [7, 3, 5, 5]
  have l1 := holds_trans l0 (holds_context c2_rule34 [] [5, 5])
  have r0 := holds_refl [6, 7, 4, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule440 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 3, 5, 5] [6, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule81 [] [3])) (holds_context c2_rule32 [7, 6, 5] []))
  have l0 := holds_refl [6, 3, 7, 4, 3]
  have l1 := holds_trans l0 (holds_context c2_rule240 [6, 3] [])
  have l2 := holds_trans l1 (holds_context c2_rule229 [6] [7, 4])
  have r0 := holds_refl [7, 6, 5, 3, 5]
  have r1 := holds_trans r0 (holds_context c2_rule32 [7, 6] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule441 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 3, 5] [6, 7, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule440 [] [-5])) (holds_context c2_rule8 [7, 6, 3, 5] []))
  have l0 := holds_refl [6, 7, 4, -5]
  have r0 := holds_refl [7, 6, 3, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule443 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [4, 6, 5, 5, -7] [-7, 6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule82 [] [-7])) (holds_context c2_rule12 [-7, 6, 3] []))
  have l0 := holds_refl [6, 5, 5, 4, -7]
  have l1 := holds_trans l0 (holds_context c2_rule317 [6] [-7])
  have l2 := holds_trans l1 (holds_context c2_rule308 [] [3, 8, -7])
  have l3 := holds_trans l2 (holds_context c2_rule388 [] [-7])
  have r0 := holds_refl [-7, 6, 3]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule444 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [6, 5, 5, -7] [4, -7, 6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule443 [4] [])) (holds_context c2_rule230 [] [6, 5, 5, -7]))
  have l0 := holds_refl [4, -7, 6, 3]
  have r0 := holds_refl [6, 5, 5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule451 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .v_s5_s4) [3, -5, 4, -7, 6] [5, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule85 [-5] [])) (holds_context c2_rule9 [] [5, 6, -7]))
  have l0 := holds_refl [-5, 4, 3, -7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule237 [] [-7, 6])
  have r0 := holds_refl [5, 6, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule452 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .v_s5_s4) [-5, 4, -7, 6] [3, 5, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule451 [3] [])) (holds_context c2_rule229 [] [-5, 4, -7, 6]))
  have l0 := holds_refl [3, 5, 6, -7]
  have r0 := holds_refl [-5, 4, -7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule461 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 4, 5, 5, 6] [4, -9, 4, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c2_rule86 [-7] [])) (holds_context c2_rule33 [] [-7, 6, 7]))
  have l0 := holds_refl [-7, 4, 5, 5, 6]
  have r0 := holds_refl [3, -7, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c2_rule28 [3] [6, 7])
  have r2 := holds_trans r1 (holds_context c2_rule75 [] [7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
