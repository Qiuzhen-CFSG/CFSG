module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step32

/-! Kernel-checked central word identities, chunk 33.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c10_rule71 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [6, 3, 7, 7] [-9, 4, 9, 4] := by
  have h0 := (split [-9, -4, 9, 4] [-7, -7, -3, -6] (rotate [] [-9, -4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-9, -4, 9, 4]
  have l1 := holds_trans l0 (holds_context c10_rule23 [-9] [9, 4])
  have r0 := holds_refl [6, 3, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule82 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 5, 5, 4] [-7, 6, 3, 7] := by
  have h0 := (split [6, -5, -5, -4] [-3, -7, -6, 7] (rotate [-7, -6, 7] [6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c10_rule27 [6] [-4])
  have l2 := holds_trans l1 (holds_context c10_rule23 [6, 5, 5] [])
  have r0 := holds_refl [-7, 6, 7, 3]
  have r1 := holds_trans r0 (holds_context c10_rule34 [-7, 6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule83 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, 6, 7] [3, 5, 5, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-7, -6, 7, 6] (rotate [-7, -6, 7, 6] [-5, -5, -4, -3] source22))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c10_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c10_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c10_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c10_rule30 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c10_rule32 [5] [4])
  have l6 := holds_trans l5 (holds_context c10_rule32 [] [5, 4])
  have r0 := holds_refl [-6, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c10_rule24 [] [-7, 6, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r1))) (by central_nf)

theorem c10_rule86 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 5, 6] [3, -7, 6, 7] := by
  have h0 := (split [-3, -7, -6, 7] [6, -5, -5, -4] (rotate [-7, -6, 7, 6, -5, -5, -4] [-3] source22))
  have l0 := holds_refl [-3, -7, -6, 7]
  have l1 := holds_trans l0 (holds_context c10_rule22 [] [-7, -6, 7])
  have l2 := holds_trans l1 (holds_context c10_rule24 [3, -7] [7])
  have r0 := holds_refl [4, 5, 5, -6]
  have r1 := holds_trans r0 (holds_context c10_rule24 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c10_rule92 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, 7, 7, 2] [3, 4, 5, 5] := by
  have h0 := (split [3, 4, 5, 5] [2, -7, -7, -3, 2] (rotate [2] [3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [3, 4, 5, 5]
  have r0 := holds_refl [-2, 3, 7, 7, -2]
  have r1 := holds_trans r0 (holds_context c10_rule21 [] [3, 7, 7, -2])
  have r2 := holds_trans r1 (holds_context c10_rule21 [2, 3, 7, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c10_rule98 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 9, -5, 4] [3, -7, 2, 3] := by
  have h0 := (split [-7, -3, 2, 3] [4, 5, 5, 2, -7] (rotate [2, 3, 4, 5, 5, 2, -7] [-7, -3] source36))
  have l0 := holds_refl [-7, -3, 2, 3]
  have l1 := holds_trans l0 (holds_context c10_rule22 [-7] [2, 3])
  have l2 := holds_trans l1 (holds_context c10_rule33 [] [2, 3])
  have r0 := holds_refl [7, -2, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c10_rule21 [7] [-5, -5, -4])
  have r2 := holds_trans r1 (holds_context c10_rule50 [] [-5, -4])
  have r3 := holds_trans r2 (holds_context c10_rule23 [2, 9, -5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r3))) (by central_nf)

theorem c10_rule103 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [3, 4, 5, 5] [3, 5, 5, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-2, 3, 7, 7, -2] (rotate [3, 7, 7, -2] [-5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c10_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c10_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c10_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c10_rule30 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c10_rule32 [5] [4])
  have l6 := holds_trans l5 (holds_context c10_rule32 [] [5, 4])
  have r0 := holds_refl [2, -7, -7, -3, 2]
  have r1 := holds_trans r0 (holds_context c10_rule28 [2] [-3, 2])
  have r2 := holds_trans r1 (holds_context c10_rule22 [2, 7, 7] [2])
  have r3 := holds_trans r2 (holds_context c10_rule34 [2, 7] [2])
  have r4 := holds_trans r3 (holds_context c10_rule34 [2] [7, 2])
  have r5 := holds_trans r4 (holds_context c10_rule92 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r5))) (by central_nf)

theorem c10_rule104 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 9, 3, -7] [3, -5, 2, 8] := by
  have h0 := (split [-5, -4, -3, -2] [3, 7, 7, -2, -5] (rotate [3, 7, 7, -2, -5] [-5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -4, -3, -2]
  have l1 := holds_trans l0 (holds_context c10_rule23 [-5] [-3, -2])
  have l2 := holds_trans l1 (holds_context c10_rule22 [-5, 4] [-2])
  have l3 := holds_trans l2 (holds_context c10_rule30 [-5] [-2])
  have l4 := holds_trans l3 (holds_context c10_rule31 [] [4, -2])
  have l5 := holds_trans l4 (holds_context c10_rule21 [3, -5, 4] [])
  have l6 := holds_trans l5 (holds_context c10_rule42 [3, -5] [])
  have r0 := holds_refl [5, 2, -7, -7, -3]
  have r1 := holds_trans r0 (holds_context c10_rule55 [] [-7, -3])
  have r2 := holds_trans r1 (holds_context c10_rule22 [2, 9, -7] [])
  have r3 := holds_trans r2 (holds_context c10_rule33 [2, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r3))) (by central_nf)

theorem c10_rule131 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, 9, 3, 5, 5, 4] [4, 9, 4] := by
  have h0 := (split [9, 6, -7, -7, -3] [-5, -5, -4, -3, -9, -6] (rotate [-9, -6] [9, 6, -7, -7, -3, -5, -5, -4, -3] source20))
  have l0 := holds_refl [9, 6, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context c10_rule28 [9, 6] [-3])
  have l2 := holds_trans l1 (holds_context c10_rule22 [9, 6, 7, 7] [])
  have l3 := holds_trans l2 (holds_context c10_rule34 [9, 6, 7] [])
  have l4 := holds_trans l3 (holds_context c10_rule34 [9, 6] [7])
  have l5 := holds_trans l4 (holds_context c10_rule71 [9] [])
  have l6 := holds_trans l5 (holds_context c10_rule16 [] [4, 9, 4])
  have r0 := holds_refl [6, 9, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c10_rule103 [6, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r1))) (by central_nf)

theorem c10_rule152 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [3, -5, 7, 5, 4] [6, 3, 7] := by
  have h0 := (split [7, -6, -5, -5, -4] [-3, -4, -5, -7, 5] (rotate [-5, -7, 5] [7, -6, -5, -5, -4, -3, -4] source21))
  have l0 := holds_refl [7, -6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c10_rule24 [7] [-5, -5, -4])
  have l2 := holds_trans l1 (holds_context c10_rule27 [7, 6] [-4])
  have l3 := holds_trans l2 (holds_context c10_rule23 [7, 6, 5, 5] [])
  have l4 := holds_trans l3 (holds_context c10_rule82 [7] [])
  have l5 := holds_trans l4 (holds_context c10_rule12 [] [6, 3, 7])
  have r0 := holds_refl [-5, 7, 5, 4, 3]
  have r1 := holds_trans r0 (holds_context c10_rule30 [-5, 7, 5] [])
  have r2 := holds_trans r1 (holds_context c10_rule32 [-5, 7] [4])
  have r3 := holds_trans r2 (holds_context c10_rule34 [-5] [5, 4])
  have r4 := holds_trans r3 (holds_context c10_rule31 [] [7, 5, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r4))) (by central_nf)

theorem c10_rule157 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 4, -5, -7, 5] [3, -7, 6] := by
  have h0 := (split [-3, -4, -5, -7, 5] [7, -6, -5, -5, -4] (rotate [-5, -7, 5, 7, -6, -5, -5, -4] [-3, -4] source21))
  have l0 := holds_refl [-3, -4, -5, -7, 5]
  have l1 := holds_trans l0 (holds_context c10_rule22 [] [-4, -5, -7, 5])
  have l2 := holds_trans l1 (holds_context c10_rule23 [3] [-5, -7, 5])
  have r0 := holds_refl [4, 5, 5, 6, -7]
  have r1 := holds_trans r0 (holds_context c10_rule86 [] [-7])
  have r2 := holds_trans r1 (holds_context c10_rule12 [3, -7, 6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c10_rule223 : Holds (normalizedRelatorError .i_r1) [1, 1] [] := by
  have h0 := c10_rule0
  have l0 := holds_refl [1, -1]
  have l1 := holds_trans l0 (holds_context c10_rule20 [1] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule224 : Holds (normalizedRelatorError .i_r8) [2, 2] [] := by
  have h0 := c10_rule2
  have l0 := holds_refl [2, -2]
  have l1 := holds_trans l0 (holds_context c10_rule21 [2] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule225 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c10_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c10_rule22 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule226 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c10_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context c10_rule23 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule227 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c10_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context c10_rule24 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule228 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c10_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context c10_rule25 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule229 : Holds (normalizedRelatorError .i_s8) [10, 10] [] := by
  have h0 := c10_rule18
  have l0 := holds_refl [10, -10]
  have l1 := holds_trans l0 (holds_context c10_rule26 [10] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule230 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule27 [5] [])) (holds_context c10_rule8 [] [-5]))
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule235 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [1, 8, 10] [1, 10, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule38 [6] [])) (holds_context c10_rule35 [] [1]))
  have l0 := holds_refl [6, 1, 10]
  have l1 := holds_trans l0 (holds_context c10_rule40 [] [10])
  have r0 := holds_refl [4, 6, 1]
  have r1 := holds_trans r0 (holds_context c10_rule40 [4] [])
  have r2 := holds_trans r1 (holds_context c10_rule38 [] [8])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c10_rule236 : Holds ((normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [1, 6, 10] [1, 10, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule38 [8] [])) (holds_context c10_rule36 [] [1]))
  have l0 := holds_refl [8, 1, 10]
  have l1 := holds_trans l0 (holds_context c10_rule39 [] [10])
  have r0 := holds_refl [4, 8, 1]
  have r1 := holds_trans r0 (holds_context c10_rule39 [4] [])
  have r2 := holds_trans r1 (holds_context c10_rule38 [] [6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c10_rule250 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s3 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [5, 5, 2, 9] [-5, 2, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule48 [-5] [])) (holds_context c10_rule27 [] [2, 9]))
  have l0 := holds_refl [-5, 2, -7]
  have r0 := holds_refl [5, 5, 2, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule283 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s8 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s8) [6, 10, 4, 10] [4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule57 [6] [])) (holds_context c10_rule35 [] [6, 8]))
  have l0 := holds_refl [6, 10, 4, 10]
  have r0 := holds_refl [4, 6, 6, 8]
  have r1 := holds_trans r0 (holds_context c10_rule227 [4] [8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule284 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s8) [6, 10, 4] [4, 8, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule283 [] [10])) (holds_context c10_rule229 [6, 10, 4] []))
  have l0 := holds_refl [4, 8, 10]
  have r0 := holds_refl [6, 10, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule285 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6] [6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule57 [] [4])) (holds_context c10_rule36 [4, 6] []))
  have l0 := holds_refl [10, 4, 10, 4]
  have l1 := holds_trans l0 (holds_context c10_rule59 [10] [])
  have l2 := holds_trans l1 (holds_context c10_rule229 [] [8, 6])
  have r0 := holds_refl [4, 6, 4, 8]
  have r1 := holds_trans r0 (holds_context c10_rule35 [4] [8])
  have r2 := holds_trans r1 (holds_context c10_rule226 [] [6, 8])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c10_rule291 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [6, 10, 6, 8] [8, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule59 [6] [])) (holds_context c10_rule35 [] [10, 4]))
  have l0 := holds_refl [6, 10, 8, 6]
  have l1 := holds_trans l0 (holds_context c10_rule285 [6, 10] [])
  have r0 := holds_refl [4, 6, 10, 4]
  have r1 := holds_trans r0 (holds_context c10_rule284 [4] [])
  have r2 := holds_trans r1 (holds_context c10_rule226 [] [8, 10])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c10_rule292 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 10, 8] [6, 10, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule291 [] [8])) (holds_context c10_rule228 [6, 10, 6] []))
  have l0 := holds_refl [8, 10, 8]
  have r0 := holds_refl [6, 10, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule301 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [3, 8, 5, 5] [4, 8] := by
  have h0 := c10_rule65
  have l0 := holds_refl [8, 3, 3, 4]
  have l1 := holds_trans l0 (holds_context c10_rule225 [8] [4])
  have l2 := holds_trans l1 (holds_context c10_rule36 [] [])
  have r0 := holds_refl [3, 8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule302 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [4, 8, -5] [3, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule301 [] [-5])) (holds_context c10_rule8 [3, 8, 5] []))
  have l0 := holds_refl [4, 8, -5]
  have r0 := holds_refl [3, 8, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule303 : Holds (normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 5, 5] [3, 4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule301 [3] [])) (holds_context c10_rule225 [] [8, 5, 5]))
  have l0 := holds_refl [3, 4, 8]
  have r0 := holds_refl [8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule308 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-5, 7, 5, 4] [3, 6, 3, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule225 [] [-5, 7, 5, 4])) (holds_context c10_rule152 [3] []))
  have l0 := holds_refl [-5, 7, 5, 4]
  have r0 := holds_refl [3, 6, 3, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule309 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7, 5] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule225 [] [4, -5, -7, 5])) (holds_context c10_rule157 [3] []))
  have l0 := holds_refl [4, -5, -7, 5]
  have r0 := holds_refl [3, 3, -7, 6]
  have r1 := holds_trans r0 (holds_context c10_rule225 [] [-7, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule310 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7] [-7, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule309 [] [-5])) (holds_context c10_rule8 [4, -5, -7] []))
  have l0 := holds_refl [-7, 6, -5]
  have r0 := holds_refl [4, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule311 : Holds ((normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [4, -7, 6] [-5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule309 [4] [])) (holds_context c10_rule226 [] [-5, -7, 5]))
  have l0 := holds_refl [4, -7, 6]
  have r0 := holds_refl [-5, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule319 : Holds (normalizedRelatorError .i_s8 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [1, 10, 8, 10] [1, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule235 [4] [])) (holds_context c10_rule38 [] [8, 10]))
  have l0 := holds_refl [4, 1, 10, 8]
  have l1 := holds_trans l0 (holds_context c10_rule38 [] [10, 8])
  have l2 := holds_trans l1 (holds_context c10_rule229 [1] [8])
  have r0 := holds_refl [1, 10, 8, 10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule320 : Holds (normalizedRelatorError .i_s8 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [10, 8, 10] [8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule319 [1] [])) (holds_context c10_rule223 [] [10, 8, 10]))
  have l0 := holds_refl [1, 1, 8]
  have l1 := holds_trans l0 (holds_context c10_rule223 [] [8])
  have r0 := holds_refl [10, 8, 10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule321 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [8, 10] [10, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule320 [10] [])) (holds_context c10_rule229 [] [8, 10]))
  have l0 := holds_refl [10, 8]
  have r0 := holds_refl [8, 10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule324 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6) [6, 10, 6] [10] := by
  have h0 := c10_rule292
  have l0 := holds_refl [8, 10, 8]
  have l1 := holds_trans l0 (holds_context c10_rule321 [] [8])
  have l2 := holds_trans l1 (holds_context c10_rule228 [10] [])
  have r0 := holds_refl [6, 10, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule325 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [6, 10] [10, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule324 [6] [])) (holds_context c10_rule227 [] [10, 6]))
  have l0 := holds_refl [6, 10]
  have r0 := holds_refl [10, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule360 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [6, 3, 8, 5] [10, 4, 10, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule302 [6] [])) (holds_context c10_rule35 [] [8, -5]))
  have l0 := holds_refl [6, 3, 8, 5]
  have r0 := holds_refl [4, 6, 8, -5]
  have r1 := holds_trans r0 (holds_context c10_rule57 [] [-5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
