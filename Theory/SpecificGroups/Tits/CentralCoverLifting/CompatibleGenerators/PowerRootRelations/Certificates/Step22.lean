module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step21

/-! Kernel-checked central word identities, chunk 22.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c7_rule33 : Holds (normalizedRelatorError .iv_s2_s4) [4, 6] [6, 4] := by
  have h0 := (split [-4, -6] [4, 6] (rotate [] [-4, -6, 4, 6] source16))
  have l0 := holds_refl [-4, -6]
  have l1 := holds_trans l0 (holds_context c7_rule21 [] [-6])
  have l2 := holds_trans l1 (holds_context c7_rule22 [4] [])
  have r0 := holds_refl [-6, -4]
  have r1 := holds_trans r0 (holds_context c7_rule22 [] [-4])
  have r2 := holds_trans r1 (holds_context c7_rule21 [6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule34 : Holds (normalizedRelatorError .iv_s2_s6) [4, 8] [8, 4] := by
  have h0 := (split [-4, -8] [4, 8] (rotate [] [-4, -8, 4, 8] source17))
  have l0 := holds_refl [-4, -8]
  have l1 := holds_trans l0 (holds_context c7_rule21 [] [-8])
  have l2 := holds_trans l1 (holds_context c7_rule23 [4] [])
  have r0 := holds_refl [-8, -4]
  have r1 := holds_trans r0 (holds_context c7_rule23 [] [-4])
  have r2 := holds_trans r1 (holds_context c7_rule21 [8] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule35 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .iv_s2_s8) [4, 10, 4] [6, 8, 10] := by
  have h0 := (split [-4, -10, 4] [10, -8, -6] (rotate [] [-4, -10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-4, -10, 4]
  have l1 := holds_trans l0 (holds_context c7_rule21 [] [-10, 4])
  have l2 := holds_trans l1 (holds_context c7_rule24 [4] [4])
  have r0 := holds_refl [6, 8, -10]
  have r1 := holds_trans r0 (holds_context c7_rule24 [6, 8] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule36 : Holds (normalizedRelatorError .i_s8 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * normalizedRelatorError .iv_s2_s8) [10, 4, 10] [6, 8, 4] := by
  have h0 := (split [-10, 4, 10] [-8, -6, -4] (rotate [-4] [-10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-10, 4, 10]
  have l1 := holds_trans l0 (holds_context c7_rule24 [] [4, 10])
  have r0 := holds_refl [4, 6, 8]
  have r1 := holds_trans r0 (holds_context c7_rule33 [] [8])
  have r2 := holds_trans r1 (holds_context c7_rule34 [6] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule39 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [6, 8, 4] [8, 6, 4] := by
  have h0 := (split [-8, -6, -4] [-10, 4, 10] (rotate [-4, -10, 4, 10] [-8, -6] source18))
  have l0 := holds_refl [-8, -6, -4]
  have l1 := holds_trans l0 (holds_context c7_rule23 [] [-6, -4])
  have l2 := holds_trans l1 (holds_context c7_rule22 [8] [-4])
  have l3 := holds_trans l2 (holds_context c7_rule21 [8, 6] [])
  have r0 := holds_refl [-10, -4, 10]
  have r1 := holds_trans r0 (holds_context c7_rule24 [] [-4, 10])
  have r2 := holds_trans r1 (holds_context c7_rule21 [10] [10])
  have r3 := holds_trans r2 (holds_context c7_rule36 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r3))) (by central_nf)

theorem c7_rule41 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 4, 5, 5] [3, 8, 3, 8] := by
  have h0 := (split [-3, -8, 3, 8] [-5, -5, -4, -3] (rotate [] [-3, -8, 3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [-3, -8, 3, 8]
  have l1 := holds_trans l0 (holds_context c7_rule20 [] [-8, 3, 8])
  have l2 := holds_trans l1 (holds_context c7_rule23 [3] [3, 8])
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule42 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 3, 4, 5] [8, 3, 8, -5] := by
  have h0 := (split [-8, 3, 8, -5] [-5, -4, -3, -3] (rotate [-3] [-8, 3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [-8, 3, 8, -5]
  have l1 := holds_trans l0 (holds_context c7_rule23 [] [3, 8, -5])
  have r0 := holds_refl [3, 3, 4, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule44 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 8, 3, 3] [8, 5, 5, 4] := by
  have h0 := (split [8, -5, -5, -4] [-3, -3, -8, 3] (rotate [-3, -8, 3] [8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [8, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c7_rule25 [8] [-4])
  have l2 := holds_trans l1 (holds_context c7_rule21 [8, 5, 5] [])
  have r0 := holds_refl [-3, 8, 3, 3]
  have r1 := holds_trans r0 (holds_context c7_rule20 [] [8, 3, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule46 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [-5, 3, 3, 4] [5, 8, 3, 8] := by
  have h0 := (split [-5, -4, -3, -3] [-8, 3, 8, -5] (rotate [-3, -8, 3, 8, -5] [-5, -4, -3] source13))
  have l0 := holds_refl [-5, -4, -3, -3]
  have l1 := holds_trans l0 (holds_context c7_rule21 [-5] [-3, -3])
  have l2 := holds_trans l1 (holds_context c7_rule20 [-5, 4] [-3])
  have l3 := holds_trans l2 (holds_context c7_rule28 [-5] [-3])
  have l4 := holds_trans l3 (holds_context c7_rule20 [-5, 3, 4] [])
  have l5 := holds_trans l4 (holds_context c7_rule28 [-5, 3] [])
  have r0 := holds_refl [5, -8, -3, 8]
  have r1 := holds_trans r0 (holds_context c7_rule23 [5] [-3, 8])
  have r2 := holds_trans r1 (holds_context c7_rule20 [5, 8] [8])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule47 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [3, 3, 8, 4] [5, 5, 8, 3] := by
  have h0 := (split [-4, -3, -3, -8] [3, 8, -5, -5] (rotate [-3, -8, 3, 8, -5, -5] [-4, -3] source13))
  have l0 := holds_refl [-4, -3, -3, -8]
  have l1 := holds_trans l0 (holds_context c7_rule21 [] [-3, -3, -8])
  have l2 := holds_trans l1 (holds_context c7_rule20 [4] [-3, -8])
  have l3 := holds_trans l2 (holds_context c7_rule28 [] [-3, -8])
  have l4 := holds_trans l3 (holds_context c7_rule20 [3, 4] [-8])
  have l5 := holds_trans l4 (holds_context c7_rule28 [3] [-8])
  have l6 := holds_trans l5 (holds_context c7_rule23 [3, 3, 4] [])
  have l7 := holds_trans l6 (holds_context c7_rule34 [3, 3] [])
  have r0 := holds_refl [5, 5, -8, -3]
  have r1 := holds_trans r0 (holds_context c7_rule23 [5, 5] [-3])
  have r2 := holds_trans r1 (holds_context c7_rule20 [5, 5, 8] [])
  exact holds_factor (holds_trans (holds_symm l7) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule49 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [6, 7, 7, 3] [-9, 4, 9, 4] := by
  have h0 := (split [-9, -4, 9, 4] [-7, -7, -3, -6] (rotate [] [-9, -4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-9, -4, 9, 4]
  have l1 := holds_trans l0 (holds_context c7_rule21 [-9] [9, 4])
  have r0 := holds_refl [6, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c7_rule32 [6] [7])
  have r2 := holds_trans r1 (holds_context c7_rule32 [6, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r2))) (by central_nf)

theorem c7_rule52 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * normalizedRelatorError .iv_s7_s2) [4, 7, 7, 3] [-9, 4, 9, 6] := by
  have h0 := (split [4, -7, -7, -3] [-6, -9, -4, 9] (rotate [-9, -4, 9] [4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [4, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context c7_rule26 [4] [-3])
  have l2 := holds_trans l1 (holds_context c7_rule20 [4, 7, 7] [])
  have r0 := holds_refl [-9, 4, 9, 6]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule53 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, -9, 4, 9] [7, 7, 3, 6] := by
  have h0 := (split [-7, -7, -3, -6] [-9, -4, 9, 4] (rotate [-9, -4, 9, 4] [-7, -7, -3, -6] source19))
  have l0 := holds_refl [-7, -7, -3, -6]
  have l1 := holds_trans l0 (holds_context c7_rule26 [] [-3, -6])
  have l2 := holds_trans l1 (holds_context c7_rule20 [7, 7] [-6])
  have l3 := holds_trans l2 (holds_context c7_rule22 [7, 7, 3] [])
  have r0 := holds_refl [-4, -9, 4, 9]
  have r1 := holds_trans r0 (holds_context c7_rule21 [] [-9, 4, 9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule54 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .iv_s7_s2) [-7, 3, 6, -9] [7, 4, -9, 4] := by
  have h0 := (split [-7, -3, -6, -9] [-4, 9, 4, -7] (rotate [-9, -4, 9, 4, -7] [-7, -3, -6] source19))
  have l0 := holds_refl [-7, -3, -6, -9]
  have l1 := holds_trans l0 (holds_context c7_rule20 [-7] [-6, -9])
  have l2 := holds_trans l1 (holds_context c7_rule22 [-7, 3] [-9])
  have r0 := holds_refl [7, -4, -9, 4]
  have r1 := holds_trans r0 (holds_context c7_rule21 [7] [-9, 4])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule56 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [6, -9, 4, 9] [7, 7, 3, 4] := by
  have h0 := (split [-6, -9, -4, 9] [4, -7, -7, -3] (rotate [-9, -4, 9, 4, -7, -7, -3] [-6] source19))
  have l0 := holds_refl [-6, -9, -4, 9]
  have l1 := holds_trans l0 (holds_context c7_rule22 [] [-9, -4, 9])
  have l2 := holds_trans l1 (holds_context c7_rule21 [6, -9] [9])
  have r0 := holds_refl [3, 7, 7, -4]
  have r1 := holds_trans r0 (holds_context c7_rule32 [] [7, -4])
  have r2 := holds_trans r1 (holds_context c7_rule32 [7] [-4])
  have r3 := holds_trans r2 (holds_context c7_rule21 [7, 7, 3] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r3)) (by central_nf)

theorem c7_rule57 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 8, 3, 8] [-7, 6, 7, 6] := by
  have h0 := (split [-7, -6, 7, 6] [-5, -5, -4, -3] (rotate [] [-7, -6, 7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [-7, -6, 7, 6]
  have l1 := holds_trans l0 (holds_context c7_rule22 [-7] [7, 6])
  have r0 := holds_refl [3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c7_rule41 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule60 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .v_s5_s4) [6, 5, 5, 4] [-7, 6, 7, 3] := by
  have h0 := (split [6, -5, -5, -4] [-3, -7, -6, 7] (rotate [-7, -6, 7] [6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c7_rule25 [6] [-4])
  have l2 := holds_trans l1 (holds_context c7_rule21 [6, 5, 5] [])
  have r0 := holds_refl [-7, 6, 7, 3]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule64 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 5, 6] [-7, 3, 6, 7] := by
  have h0 := (split [-3, -7, -6, 7] [6, -5, -5, -4] (rotate [-7, -6, 7, 6, -5, -5, -4] [-3] source22))
  have l0 := holds_refl [-3, -7, -6, 7]
  have l1 := holds_trans l0 (holds_context c7_rule20 [] [-7, -6, 7])
  have l2 := holds_trans l1 (holds_context c7_rule31 [] [-6, 7])
  have l3 := holds_trans l2 (holds_context c7_rule22 [-7, 3] [7])
  have r0 := holds_refl [4, 5, 5, -6]
  have r1 := holds_trans r0 (holds_context c7_rule22 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule89 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 9, -7, 6, 7, 6] [4, 9, 4] := by
  have h0 := (split [9, 6, -7, -7, -3] [-5, -5, -4, -3, -9, -6] (rotate [-9, -6] [9, 6, -7, -7, -3, -5, -5, -4, -3] source20))
  have l0 := holds_refl [9, 6, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context c7_rule26 [9, 6] [-3])
  have l2 := holds_trans l1 (holds_context c7_rule20 [9, 6, 7, 7] [])
  have l3 := holds_trans l2 (holds_context c7_rule49 [9] [])
  have l4 := holds_trans l3 (holds_context c7_rule16 [] [4, 9, 4])
  have r0 := holds_refl [6, 9, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c7_rule41 [6, 9] [])
  have r2 := holds_trans r1 (holds_context c7_rule57 [6, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem c7_rule106 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 9, 3, 4, 5] [4, 9, 4, -5] := by
  have h0 := (split [6, 9, 3, 4, 5] [5, 3, 7, 7, -6, -9] (rotate [3, 4, 5, 5, 3, 7, 7, -6, -9] [6, 9] (inverted source20)))
  have l0 := holds_refl [6, 9, 3, 4, 5]
  have r0 := holds_refl [9, 6, -7, -7, -3, -5]
  have r1 := holds_trans r0 (holds_context c7_rule26 [9, 6] [-3, -5])
  have r2 := holds_trans r1 (holds_context c7_rule20 [9, 6, 7, 7] [-5])
  have r3 := holds_trans r2 (holds_context c7_rule49 [9] [-5])
  have r4 := holds_trans r3 (holds_context c7_rule16 [] [4, 9, 4, -5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem c7_rule115 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 4, -5, -7, 5] [-7, 3, 6] := by
  have h0 := (split [-3, -4, -5, -7, 5] [7, -6, -5, -5, -4] (rotate [-5, -7, 5, 7, -6, -5, -5, -4] [-3, -4] source21))
  have l0 := holds_refl [-3, -4, -5, -7, 5]
  have l1 := holds_trans l0 (holds_context c7_rule20 [] [-4, -5, -7, 5])
  have l2 := holds_trans l1 (holds_context c7_rule21 [3] [-5, -7, 5])
  have r0 := holds_refl [4, 5, 5, 6, -7]
  have r1 := holds_trans r0 (holds_context c7_rule64 [] [-7])
  have r2 := holds_trans r1 (holds_context c7_rule12 [-7, 3, 6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule129 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c7_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c7_rule20 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule130 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c7_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context c7_rule21 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule131 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c7_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context c7_rule22 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule132 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c7_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context c7_rule23 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule133 : Holds (normalizedRelatorError .i_s8) [10, 10] [] := by
  have h0 := c7_rule18
  have l0 := holds_refl [10, -10]
  have l1 := holds_trans l0 (holds_context c7_rule24 [10] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule134 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule25 [5] [])) (holds_context c7_rule8 [] [-5]))
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule137 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [4, -5, 3] [3, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule29 [4] [])) (holds_context c7_rule28 [] [-5]))
  have l0 := holds_refl [4, -5, 3]
  have r0 := holds_refl [3, 4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule139 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [4, -7, 3] [3, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule31 [4] [])) (holds_context c7_rule28 [] [-7]))
  have l0 := holds_refl [4, -7, 3]
  have r0 := holds_refl [3, 4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule145 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [6, 8] [8, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule36 [4] [])) (holds_context c7_rule35 [] [10]))
  have l0 := holds_refl [4, 6, 8, 4]
  have l1 := holds_trans l0 (holds_context c7_rule33 [] [8, 4])
  have l2 := holds_trans l1 (holds_context c7_rule34 [6] [4])
  have l3 := holds_trans l2 (holds_context c7_rule39 [] [4])
  have l4 := holds_trans l3 (holds_context c7_rule130 [8, 6] [])
  have r0 := holds_refl [6, 8, 10, 10]
  have r1 := holds_trans r0 (holds_context c7_rule133 [6, 8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule152 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6) [8, 3, 8, -5] [4, 5] := by
  have h0 := c7_rule42
  have l0 := holds_refl [3, 3, 4, 5]
  have l1 := holds_trans l0 (holds_context c7_rule129 [] [4, 5])
  have r0 := holds_refl [8, 3, 8, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule153 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [4, 5, 5] [8, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule152 [] [5])) (holds_context c7_rule9 [8, 3, 8] []))
  have l0 := holds_refl [4, 5, 5]
  have r0 := holds_refl [8, 3, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule154 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .iii_s1_s6) [3, 8, -5] [8, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule152 [8] [])) (holds_context c7_rule132 [] [3, 8, -5]))
  have l0 := holds_refl [8, 4, 5]
  have r0 := holds_refl [3, 8, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule155 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [8, 5, 5, 4] [3, 8] := by
  have h0 := c7_rule44
  have l0 := holds_refl [3, 8, 3, 3]
  have l1 := holds_trans l0 (holds_context c7_rule129 [3, 8] [])
  have r0 := holds_refl [8, 5, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule156 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 8, 4] [8, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule155 [] [4])) (holds_context c7_rule130 [8, 5, 5] []))
  have l0 := holds_refl [3, 8, 4]
  have r0 := holds_refl [8, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule157 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [5, 5, 4] [8, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule155 [8] [])) (holds_context c7_rule132 [] [5, 5, 4]))
  have l0 := holds_refl [8, 3, 8]
  have r0 := holds_refl [5, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule158 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [5, 8, 3, 8] [-5, 4] := by
  have h0 := c7_rule46
  have l0 := holds_refl [-5, 3, 3, 4]
  have l1 := holds_trans l0 (holds_context c7_rule129 [-5] [4])
  have r0 := holds_refl [5, 8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule159 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [-5, 8, 4] [5, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule158 [] [8])) (holds_context c7_rule132 [5, 8, 3] []))
  have l0 := holds_refl [-5, 4, 8]
  have l1 := holds_trans l0 (holds_context c7_rule34 [-5] [])
  have r0 := holds_refl [5, 8, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule160 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [5, 5, 8, 3] [8, 4] := by
  have h0 := c7_rule47
  have l0 := holds_refl [3, 3, 8, 4]
  have l1 := holds_trans l0 (holds_context c7_rule129 [] [8, 4])
  have r0 := holds_refl [5, 5, 8, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule161 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [5, 5, 8] [8, 3, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule160 [] [3])) (holds_context c7_rule129 [5, 5, 8] []))
  have l0 := holds_refl [8, 4, 3]
  have l1 := holds_trans l0 (holds_context c7_rule28 [8] [])
  have r0 := holds_refl [5, 5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
