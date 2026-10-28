module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step06

/-! Kernel-checked central word identities, chunk 7.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c2_rule43 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ)) [6, 2] [2, 6] := by
  have h0 := (split [2, 6] [2, -6] (rotate [] [2, 6, 2, -6] source32))
  have l0 := holds_refl [2, 6]
  have r0 := holds_refl [6, -2]
  have r1 := holds_trans r0 (holds_context c2_rule21 [6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule44 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ)) [-9, 2] [2, 9] := by
  have h0 := (split [2, 9] [2, 9] (rotate [] [2, 9, 2, 9] source34))
  have l0 := holds_refl [2, 9]
  have r0 := holds_refl [-9, -2]
  have r1 := holds_trans r0 (holds_context c2_rule21 [-9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule45 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7) [9, 2] [2, -9] := by
  have h0 := (split [9, 2] [9, 2] (rotate [2] [9, 2, 9] source34))
  have l0 := holds_refl [9, 2]
  have r0 := holds_refl [-2, -9]
  have r1 := holds_trans r0 (holds_context c2_rule21 [] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule47 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 9, 7] [5, 2] := by
  have h0 := (split [5, 2] [-7, -9, 2] (rotate [2] [5, 2, -7, -9] source35))
  have l0 := holds_refl [5, 2]
  have r0 := holds_refl [-2, 9, 7]
  have r1 := holds_trans r0 (holds_context c2_rule21 [] [9, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule48 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [-5, 2, 9] [2, -7] := by
  have h0 := (split [2, -7] [-9, 2, 5] (rotate [2, 5] [2, -7, -9] source35))
  have l0 := holds_refl [2, -7]
  have r0 := holds_refl [-5, -2, 9]
  have r1 := holds_trans r0 (holds_context c2_rule21 [-5] [9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule50 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [7, 2, -5] [2, 9] := by
  have h0 := (split [-9, 2] [5, 2, -7] (rotate [2, 5, 2, -7] [-9] source35))
  have l0 := holds_refl [-9, 2]
  have l1 := holds_trans l0 (holds_context c2_rule44 [] [])
  have r0 := holds_refl [7, -2, -5]
  have r1 := holds_trans r0 (holds_context c2_rule21 [7] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule51 : Holds (normalizedRelatorError .viii_s3) [2, 5, 2] [9, 7] := by
  have h0 := (split [9, 7] [-2, -5, -2] (rotate [] [9, 7, -2, -5, -2] (inverted source35)))
  have l0 := holds_refl [9, 7]
  have r0 := holds_refl [2, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule52 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 9, 5] [7, 2] := by
  have h0 := (split [7, -2] [-5, -2, 9] (rotate [9] [7, -2, -5, -2] (inverted source35)))
  have l0 := holds_refl [7, -2]
  have l1 := holds_trans l0 (holds_context c2_rule21 [7] [])
  have r0 := holds_refl [-9, 2, 5]
  have r1 := holds_trans r0 (holds_context c2_rule44 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule53 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [-7, 2, 9] [2, -5] := by
  have h0 := (split [-2, -5] [-2, 9, 7] (rotate [9, 7] [-2, -5, -2] (inverted source35)))
  have l0 := holds_refl [-2, -5]
  have l1 := holds_trans l0 (holds_context c2_rule21 [] [-5])
  have r0 := holds_refl [-7, -9, 2]
  have r1 := holds_trans r0 (holds_context c2_rule44 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule54 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [2, -7, -9] [-5, 2] := by
  have h0 := (split [-5, -2] [9, 7, -2] (rotate [9, 7, -2] [-5, -2] (inverted source35)))
  have l0 := holds_refl [-5, -2]
  have l1 := holds_trans l0 (holds_context c2_rule21 [-5] [])
  have r0 := holds_refl [2, -7, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule55 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [5, 2, -7] [2, 9] := by
  have h0 := (split [-2, 9] [7, -2, -5] (rotate [9, 7, -2, -5] [-2] (inverted source35)))
  have l0 := holds_refl [-2, 9]
  have l1 := holds_trans l0 (holds_context c2_rule21 [] [9])
  have r0 := holds_refl [5, 2, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule57 : Holds (normalizedRelatorError .i_s8 * normalizedRelatorError .iv_s2_s8) [10, 4, 10] [4, 6, 8] := by
  have h0 := (split [-10, 4, 10] [-8, -6, -4] (rotate [-4] [-10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-10, 4, 10]
  have l1 := holds_trans l0 (holds_context c2_rule26 [] [4, 10])
  have r0 := holds_refl [4, 6, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule60 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [4, 6, 8] [4, 8, 6] := by
  have h0 := (split [-8, -6, -4] [-10, 4, 10] (rotate [-4, -10, 4, 10] [-8, -6] source18))
  have l0 := holds_refl [-8, -6, -4]
  have l1 := holds_trans l0 (holds_context c2_rule25 [] [-6, -4])
  have l2 := holds_trans l1 (holds_context c2_rule24 [8] [-4])
  have l3 := holds_trans l2 (holds_context c2_rule23 [8, 6] [])
  have l4 := holds_trans l3 (holds_context c2_rule35 [8] [])
  have l5 := holds_trans l4 (holds_context c2_rule36 [] [6])
  have r0 := holds_refl [-10, -4, 10]
  have r1 := holds_trans r0 (holds_context c2_rule26 [] [-4, 10])
  have r2 := holds_trans r1 (holds_context c2_rule23 [10] [10])
  have r3 := holds_trans r2 (holds_context c2_rule57 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r3))) (by central_nf)

theorem c2_rule66 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 8, 3, 3] [8, 5, 5, 4] := by
  have h0 := (split [8, -5, -5, -4] [-3, -3, -8, 3] (rotate [-3, -8, 3] [8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [8, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c2_rule27 [8] [-4])
  have l2 := holds_trans l1 (holds_context c2_rule23 [8, 5, 5] [])
  have r0 := holds_refl [-3, 8, 3, 3]
  have r1 := holds_trans r0 (holds_context c2_rule22 [] [8, 3, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule67 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [5, 5, 4, 3] [8, 3, 8, 3] := by
  have h0 := (split [-5, -5, -4, -3] [-3, -8, 3, 8] (rotate [-3, -8, 3, 8] [-5, -5, -4, -3] source13))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c2_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c2_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c2_rule22 [5, 5, 4] [])
  have r0 := holds_refl [-8, -3, 8, 3]
  have r1 := holds_trans r0 (holds_context c2_rule25 [] [-3, 8, 3])
  have r2 := holds_trans r1 (holds_context c2_rule22 [8] [8, 3])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r2)) (by central_nf)

theorem c2_rule68 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6) [-5, 4, 3, 3] [5, 8, 3, 8] := by
  have h0 := (split [-5, -4, -3, -3] [-8, 3, 8, -5] (rotate [-3, -8, 3, 8, -5] [-5, -4, -3] source13))
  have l0 := holds_refl [-5, -4, -3, -3]
  have l1 := holds_trans l0 (holds_context c2_rule23 [-5] [-3, -3])
  have l2 := holds_trans l1 (holds_context c2_rule22 [-5, 4] [-3])
  have l3 := holds_trans l2 (holds_context c2_rule22 [-5, 4, 3] [])
  have r0 := holds_refl [5, -8, -3, 8]
  have r1 := holds_trans r0 (holds_context c2_rule25 [5] [-3, 8])
  have r2 := holds_trans r1 (holds_context c2_rule22 [5, 8] [8])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r2)) (by central_nf)

theorem c2_rule70 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [3, 3, 8, 3] [4, 5, 5, 8] := by
  have h0 := (split [-3, -3, -8, 3] [8, -5, -5, -4] (rotate [-3, -8, 3, 8, -5, -5, -4] [-3] source13))
  have l0 := holds_refl [-3, -3, -8, 3]
  have l1 := holds_trans l0 (holds_context c2_rule22 [] [-3, -8, 3])
  have l2 := holds_trans l1 (holds_context c2_rule22 [3] [-8, 3])
  have l3 := holds_trans l2 (holds_context c2_rule25 [3, 3] [3])
  have r0 := holds_refl [4, 5, 5, -8]
  have r1 := holds_trans r0 (holds_context c2_rule25 [4, 5, 5] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule71 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 4] [6, 3, 7, 7] := by
  have h0 := (split [-9, -4, 9, 4] [-7, -7, -3, -6] (rotate [] [-9, -4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-9, -4, 9, 4]
  have l1 := holds_trans l0 (holds_context c2_rule23 [-9] [9, 4])
  have r0 := holds_refl [6, 3, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule72 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [9, 6, 3, 7] [4, 9, 4, -7] := by
  have h0 := (split [-4, 9, 4, -7] [-7, -3, -6, -9] (rotate [-9] [-4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-4, 9, 4, -7]
  have l1 := holds_trans l0 (holds_context c2_rule23 [] [9, 4, -7])
  have r0 := holds_refl [9, 6, 3, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c2_rule75 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [3, 7, 7, 6] [4, -9, 4, 9] := by
  have h0 := (split [-7, -7, -3, -6] [-9, -4, 9, 4] (rotate [-9, -4, 9, 4] [-7, -7, -3, -6] source19))
  have l0 := holds_refl [-7, -7, -3, -6]
  have l1 := holds_trans l0 (holds_context c2_rule28 [] [-3, -6])
  have l2 := holds_trans l1 (holds_context c2_rule22 [7, 7] [-6])
  have l3 := holds_trans l2 (holds_context c2_rule34 [7] [-6])
  have l4 := holds_trans l3 (holds_context c2_rule34 [] [7, -6])
  have l5 := holds_trans l4 (holds_context c2_rule24 [3, 7, 7] [])
  have r0 := holds_refl [-4, -9, 4, 9]
  have r1 := holds_trans r0 (holds_context c2_rule23 [] [-9, 4, 9])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule79 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s5_s4) [-7, 6, 7, 6] [4, 3, 5, 5] := by
  have h0 := (split [-7, -6, 7, 6] [-5, -5, -4, -3] (rotate [] [-7, -6, 7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [-7, -6, 7, 6]
  have l1 := holds_trans l0 (holds_context c2_rule24 [-7] [7, 6])
  have r0 := holds_refl [3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c2_rule30 [] [5, 5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule81 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 5, 5] [6, 3, 7, 4] := by
  have h0 := (split [7, 6, -5, -5] [-4, -3, -7, -6] (rotate [-7, -6] [7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [7, 6, -5, -5]
  have l1 := holds_trans l0 (holds_context c2_rule27 [7, 6] [])
  have r0 := holds_refl [6, 7, 3, 4]
  have r1 := holds_trans r0 (holds_context c2_rule34 [6] [4])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule82 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, 3, 7] [6, 5, 5, 4] := by
  have h0 := (split [6, -5, -5, -4] [-3, -7, -6, 7] (rotate [-7, -6, 7] [6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c2_rule27 [6] [-4])
  have l2 := holds_trans l1 (holds_context c2_rule23 [6, 5, 5] [])
  have r0 := holds_refl [-7, 6, 7, 3]
  have r1 := holds_trans r0 (holds_context c2_rule34 [-7, 6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule83 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, 6, 7] [8, 3, 8, 3] := by
  have h0 := (split [-5, -5, -4, -3] [-7, -6, 7, 6] (rotate [-7, -6, 7, 6] [-5, -5, -4, -3] source22))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c2_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c2_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c2_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c2_rule67 [] [])
  have r0 := holds_refl [-6, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c2_rule24 [] [-7, 6, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule85 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 6, -7] [4, 3, -7, 6] := by
  have h0 := (split [-4, -3, -7, -6] [7, 6, -5, -5] (rotate [-7, -6, 7, 6, -5, -5] [-4, -3] source22))
  have l0 := holds_refl [-4, -3, -7, -6]
  have l1 := holds_trans l0 (holds_context c2_rule23 [] [-3, -7, -6])
  have l2 := holds_trans l1 (holds_context c2_rule22 [4] [-7, -6])
  have l3 := holds_trans l2 (holds_context c2_rule24 [4, 3, -7] [])
  have r0 := holds_refl [5, 5, -6, -7]
  have r1 := holds_trans r0 (holds_context c2_rule24 [5, 5] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule86 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .v_s5_s4) [3, -7, 6, 7] [4, 5, 5, 6] := by
  have h0 := (split [-3, -7, -6, 7] [6, -5, -5, -4] (rotate [-7, -6, 7, 6, -5, -5, -4] [-3] source22))
  have l0 := holds_refl [-3, -7, -6, 7]
  have l1 := holds_trans l0 (holds_context c2_rule22 [] [-7, -6, 7])
  have l2 := holds_trans l1 (holds_context c2_rule24 [3, -7] [7])
  have r0 := holds_refl [4, 5, 5, -6]
  have r1 := holds_trans r0 (holds_context c2_rule24 [4, 5, 5] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c2_rule91 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 7, 2, 9] [2, 4, 3, 5] := by
  have h0 := (split [2, 3, 4, 5] [5, 2, -7, -7, -3] (rotate [] [2, 3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [2, 3, 4, 5]
  have l1 := holds_trans l0 (holds_context c2_rule30 [2] [5])
  have r0 := holds_refl [3, 7, 7, -2, -5]
  have r1 := holds_trans r0 (holds_context c2_rule21 [3, 7, 7] [-5])
  have r2 := holds_trans r1 (holds_context c2_rule50 [3, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r2))) (by central_nf)

theorem c2_rule92 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, 7, 7, 2] [4, 3, 5, 5] := by
  have h0 := (split [3, 4, 5, 5] [2, -7, -7, -3, 2] (rotate [2] [3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c2_rule30 [] [5, 5])
  have r0 := holds_refl [-2, 3, 7, 7, -2]
  have r1 := holds_trans r0 (holds_context c2_rule21 [] [3, 7, 7, -2])
  have r2 := holds_trans r1 (holds_context c2_rule21 [2, 3, 7, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r2))) (by central_nf)

theorem c2_rule98 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, -7, 2, 3] [2, 9, -5, 4] := by
  have h0 := (split [-7, -3, 2, 3] [4, 5, 5, 2, -7] (rotate [2, 3, 4, 5, 5, 2, -7] [-7, -3] source36))
  have l0 := holds_refl [-7, -3, 2, 3]
  have l1 := holds_trans l0 (holds_context c2_rule22 [-7] [2, 3])
  have l2 := holds_trans l1 (holds_context c2_rule33 [] [2, 3])
  have r0 := holds_refl [7, -2, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c2_rule21 [7] [-5, -5, -4])
  have r2 := holds_trans r1 (holds_context c2_rule50 [] [-5, -4])
  have r3 := holds_trans r2 (holds_context c2_rule23 [2, 9, -5] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r3)) (by central_nf)

theorem c2_rule99 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 2, 9, -5] [3, 2, 4, 3] := by
  have h0 := (split [-3, 2, 3, 4] [5, 5, 2, -7, -7] (rotate [2, 3, 4, 5, 5, 2, -7, -7] [-3] source36))
  have l0 := holds_refl [-3, 2, 3, 4]
  have l1 := holds_trans l0 (holds_context c2_rule22 [] [2, 3, 4])
  have l2 := holds_trans l1 (holds_context c2_rule30 [3, 2] [])
  have r0 := holds_refl [7, 7, -2, -5, -5]
  have r1 := holds_trans r0 (holds_context c2_rule21 [7, 7] [-5, -5])
  have r2 := holds_trans r1 (holds_context c2_rule50 [7] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c2_rule104 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [8, 3, 8, 3] [4, 3, 5, 5] := by
  have h0 := (split [-5, -5, -4, -3] [-2, 3, 7, 7, -2] (rotate [3, 7, 7, -2] [-5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c2_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c2_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c2_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c2_rule67 [] [])
  have r0 := holds_refl [2, -7, -7, -3, 2]
  have r1 := holds_trans r0 (holds_context c2_rule28 [2] [-3, 2])
  have r2 := holds_trans r1 (holds_context c2_rule22 [2, 7, 7] [2])
  have r3 := holds_trans r2 (holds_context c2_rule34 [2, 7] [2])
  have r4 := holds_trans r3 (holds_context c2_rule34 [2] [7, 2])
  have r5 := holds_trans r4 (holds_context c2_rule92 [] [])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r5)) (by central_nf)

theorem c2_rule105 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-5, 4, 3, 2] [2, 9, 3, -7] := by
  have h0 := (split [-5, -4, -3, -2] [3, 7, 7, -2, -5] (rotate [3, 7, 7, -2, -5] [-5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -4, -3, -2]
  have l1 := holds_trans l0 (holds_context c2_rule23 [-5] [-3, -2])
  have l2 := holds_trans l1 (holds_context c2_rule22 [-5, 4] [-2])
  have l3 := holds_trans l2 (holds_context c2_rule21 [-5, 4, 3] [])
  have r0 := holds_refl [5, 2, -7, -7, -3]
  have r1 := holds_trans r0 (holds_context c2_rule55 [] [-7, -3])
  have r2 := holds_trans r1 (holds_context c2_rule22 [2, 9, -7] [])
  have r3 := holds_trans r2 (holds_context c2_rule33 [2, 9] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r3)) (by central_nf)

theorem c2_rule138 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [4, 3, 5, 5, -9] [4, -9, 4, 6] := by
  have h0 := (split [-5, -5, -4, -3, -9] [-6, 9, 6, -7, -7, -3] (rotate [-9, -6, 9, 6, -7, -7, -3] [-5, -5, -4, -3] source20))
  have l0 := holds_refl [-5, -5, -4, -3, -9]
  have l1 := holds_trans l0 (holds_context c2_rule27 [] [-4, -3, -9])
  have l2 := holds_trans l1 (holds_context c2_rule23 [5, 5] [-3, -9])
  have l3 := holds_trans l2 (holds_context c2_rule22 [5, 5, 4] [-9])
  have l4 := holds_trans l3 (holds_context c2_rule67 [] [-9])
  have l5 := holds_trans l4 (holds_context c2_rule104 [] [-9])
  have r0 := holds_refl [3, 7, 7, -6, -9, 6]
  have r1 := holds_trans r0 (holds_context c2_rule24 [3, 7, 7] [-9, 6])
  have r2 := holds_trans r1 (holds_context c2_rule75 [] [-9, 6])
  have r3 := holds_trans r2 (holds_context c2_rule16 [4, -9, 4] [6])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r3)) (by central_nf)

theorem c2_rule152 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [9, 4, 3, 5, 5] [4, 6, 9, 4] := by
  have h0 := (split [9, 3, 4, 5, 5] [3, 7, 7, -6, -9, 6] (rotate [3, 4, 5, 5, 3, 7, 7, -6, -9, 6] [9] (inverted source20)))
  have l0 := holds_refl [9, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c2_rule30 [9] [5, 5])
  have r0 := holds_refl [-6, 9, 6, -7, -7, -3]
  have r1 := holds_trans r0 (holds_context c2_rule24 [] [9, 6, -7, -7, -3])
  have r2 := holds_trans r1 (holds_context c2_rule28 [6, 9, 6] [-3])
  have r3 := holds_trans r2 (holds_context c2_rule22 [6, 9, 6, 7, 7] [])
  have r4 := holds_trans r3 (holds_context c2_rule34 [6, 9, 6, 7] [])
  have r5 := holds_trans r4 (holds_context c2_rule34 [6, 9, 6] [7])
  have r6 := holds_trans r5 (holds_context c2_rule72 [6] [7])
  have r7 := holds_trans r6 (holds_context c2_rule35 [] [9, 4, -7, 7])
  have r8 := holds_trans r7 (holds_context c2_rule13 [4, 6, 9, 4] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r8)) (by central_nf)

theorem c2_rule154 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [5, 4, 4, 3, 5] [-7, 5, 7, 6, -5] := by
  have h0 := (split [-7, 5, 7, -6, -5] [-5, -4, -3, -4, -5] (rotate [-5] [-7, 5, 7, -6, -5, -5, -4, -3, -4] source21))
  have l0 := holds_refl [-7, 5, 7, -6, -5]
  have l1 := holds_trans l0 (holds_context c2_rule24 [-7, 5, 7] [-5])
  have r0 := holds_refl [5, 4, 3, 4, 5]
  have r1 := holds_trans r0 (holds_context c2_rule30 [5, 4] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c2_rule164 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ)) [4, 6, 9, 4, 5] [2, 3, 2, -9, -7] := by
  have h0 := (split [2, 3, 2, -9, -7] [-5, -5, -5, -4, -3, -9] (rotate [] [2, 3, 2, -9, -7, -5, -5, -5, -4, -3, -9] source33))
  have l0 := holds_refl [2, 3, 2, -9, -7]
  have r0 := holds_refl [9, 3, 4, 5, 5, 5]
  have r1 := holds_trans r0 (holds_context c2_rule30 [9] [5, 5, 5])
  have r2 := holds_trans r1 (holds_context c2_rule152 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c2_rule183 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ)) [2, 3, 2, 9, 3] [-9, -7, 5, 4] := by
  have h0 := (split [-2, -3, -2, 9, 3] [4, 5, 5, 5, 7, 9] (rotate [9, 3, 4, 5, 5, 5, 7, 9] [-2, -3, -2] (inverted source33)))
  have l0 := holds_refl [-2, -3, -2, 9, 3]
  have l1 := holds_trans l0 (holds_context c2_rule21 [] [-3, -2, 9, 3])
  have l2 := holds_trans l1 (holds_context c2_rule22 [2] [-2, 9, 3])
  have l3 := holds_trans l2 (holds_context c2_rule21 [2, 3] [9, 3])
  have r0 := holds_refl [-9, -7, -5, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c2_rule27 [-9, -7] [-5, -4])
  have r2 := holds_trans r1 (holds_context c2_rule8 [-9, -7, 5] [-4])
  have r3 := holds_trans r2 (holds_context c2_rule23 [-9, -7, 5] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r3)) (by central_nf)

theorem c2_rule228 : Holds (normalizedRelatorError .i_r8) [2, 2] [] := by
  have h0 := c2_rule2
  have l0 := holds_refl [2, -2]
  have l1 := holds_trans l0 (holds_context c2_rule21 [2] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule229 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c2_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c2_rule22 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c2_rule230 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c2_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context c2_rule23 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
