module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step00

/-! Kernel-checked central word identities, chunk 1.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c1_rule45 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7) [9, 2] [2, -9] := by
  have h0 := (split [9, 2] [9, 2] (rotate [2] [9, 2, 9] source34))
  have l0 := holds_refl [9, 2]
  have r0 := holds_refl [-2, -9]
  have r1 := holds_trans r0 (holds_context c1_rule21 [] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule46 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [9, 7, 2] [2, 5] := by
  have h0 := (split [2, 5] [2, -7, -9] (rotate [] [2, 5, 2, -7, -9] source35))
  have l0 := holds_refl [2, 5]
  have r0 := holds_refl [9, 7, -2]
  have r1 := holds_trans r0 (holds_context c1_rule21 [9, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule47 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 9, 7] [5, 2] := by
  have h0 := (split [5, 2] [-7, -9, 2] (rotate [2] [5, 2, -7, -9] source35))
  have l0 := holds_refl [5, 2]
  have r0 := holds_refl [-2, 9, 7]
  have r1 := holds_trans r0 (holds_context c1_rule21 [] [9, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule48 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [-5, 2, 9] [2, -7] := by
  have h0 := (split [2, -7] [-9, 2, 5] (rotate [2, 5] [2, -7, -9] source35))
  have l0 := holds_refl [2, -7]
  have r0 := holds_refl [-5, -2, 9]
  have r1 := holds_trans r0 (holds_context c1_rule21 [-5] [9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule49 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, -5, 2] [-7, -9] := by
  have h0 := (split [-7, -9] [2, 5, 2] (rotate [2, 5, 2] [-7, -9] source35))
  have l0 := holds_refl [-7, -9]
  have r0 := holds_refl [-2, -5, -2]
  have r1 := holds_trans r0 (holds_context c1_rule21 [] [-5, -2])
  have r2 := holds_trans r1 (holds_context c1_rule21 [2, -5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule50 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [7, 2, -5] [2, 9] := by
  have h0 := (split [-9, 2] [5, 2, -7] (rotate [2, 5, 2, -7] [-9] source35))
  have l0 := holds_refl [-9, 2]
  have l1 := holds_trans l0 (holds_context c1_rule44 [] [])
  have r0 := holds_refl [7, -2, -5]
  have r1 := holds_trans r0 (holds_context c1_rule21 [7] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule51 : Holds (normalizedRelatorError .viii_s3) [2, 5, 2] [9, 7] := by
  have h0 := (split [9, 7] [-2, -5, -2] (rotate [] [9, 7, -2, -5, -2] (inverted source35)))
  have l0 := holds_refl [9, 7]
  have r0 := holds_refl [2, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule52 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 9, 5] [7, 2] := by
  have h0 := (split [7, -2] [-5, -2, 9] (rotate [9] [7, -2, -5, -2] (inverted source35)))
  have l0 := holds_refl [7, -2]
  have l1 := holds_trans l0 (holds_context c1_rule21 [7] [])
  have r0 := holds_refl [-9, 2, 5]
  have r1 := holds_trans r0 (holds_context c1_rule44 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule53 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [-7, 2, 9] [2, -5] := by
  have h0 := (split [-2, -5] [-2, 9, 7] (rotate [9, 7] [-2, -5, -2] (inverted source35)))
  have l0 := holds_refl [-2, -5]
  have l1 := holds_trans l0 (holds_context c1_rule21 [] [-5])
  have r0 := holds_refl [-7, -9, 2]
  have r1 := holds_trans r0 (holds_context c1_rule44 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule54 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [2, -7, -9] [-5, 2] := by
  have h0 := (split [-5, -2] [9, 7, -2] (rotate [9, 7, -2] [-5, -2] (inverted source35)))
  have l0 := holds_refl [-5, -2]
  have l1 := holds_trans l0 (holds_context c1_rule21 [-5] [])
  have r0 := holds_refl [2, -7, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule55 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [5, 2, -7] [2, 9] := by
  have h0 := (split [-2, 9] [7, -2, -5] (rotate [9, 7, -2, -5] [-2] (inverted source35)))
  have l0 := holds_refl [-2, 9]
  have l1 := holds_trans l0 (holds_context c1_rule21 [] [9])
  have r0 := holds_refl [5, 2, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule57 : Holds (normalizedRelatorError .i_s8 * normalizedRelatorError .iv_s2_s8) [10, 4, 10] [4, 6, 8] := by
  have h0 := (split [-10, 4, 10] [-8, -6, -4] (rotate [-4] [-10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-10, 4, 10]
  have l1 := holds_trans l0 (holds_context c1_rule26 [] [4, 10])
  have r0 := holds_refl [4, 6, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule60 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [4, 8, 6] [4, 6, 8] := by
  have h0 := (split [-8, -6, -4] [-10, 4, 10] (rotate [-4, -10, 4, 10] [-8, -6] source18))
  have l0 := holds_refl [-8, -6, -4]
  have l1 := holds_trans l0 (holds_context c1_rule25 [] [-6, -4])
  have l2 := holds_trans l1 (holds_context c1_rule24 [8] [-4])
  have l3 := holds_trans l2 (holds_context c1_rule23 [8, 6] [])
  have l4 := holds_trans l3 (holds_context c1_rule35 [8] [])
  have l5 := holds_trans l4 (holds_context c1_rule36 [] [6])
  have r0 := holds_refl [-10, -4, 10]
  have r1 := holds_trans r0 (holds_context c1_rule26 [] [-4, 10])
  have r2 := holds_trans r1 (holds_context c1_rule23 [10] [10])
  have r3 := holds_trans r2 (holds_context c1_rule57 [] [])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r3)) (by central_nf)

theorem c1_rule61 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [8, 10, 4] [4, 6, 10] := by
  have h0 := (split [-6, -4, -10] [4, 10, -8] (rotate [-4, -10, 4, 10, -8] [-6] source18))
  have l0 := holds_refl [-6, -4, -10]
  have l1 := holds_trans l0 (holds_context c1_rule24 [] [-4, -10])
  have l2 := holds_trans l1 (holds_context c1_rule23 [6] [-10])
  have l3 := holds_trans l2 (holds_context c1_rule35 [] [-10])
  have l4 := holds_trans l3 (holds_context c1_rule26 [4, 6] [])
  have r0 := holds_refl [8, -10, -4]
  have r1 := holds_trans r0 (holds_context c1_rule26 [8] [-4])
  have r2 := holds_trans r1 (holds_context c1_rule23 [8, 10] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule63 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6) [3, 8, 3, 8] [3, 4, 5, 5] := by
  have h0 := (split [-3, -8, 3, 8] [-5, -5, -4, -3] (rotate [] [-3, -8, 3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [-3, -8, 3, 8]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-8, 3, 8])
  have l2 := holds_trans l1 (holds_context c1_rule25 [3] [3, 8])
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule64 : Holds (normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6) [8, 3, 8, -5] [3, 3, 4, 5] := by
  have h0 := (split [-8, 3, 8, -5] [-5, -4, -3, -3] (rotate [-3] [-8, 3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [-8, 3, 8, -5]
  have l1 := holds_trans l0 (holds_context c1_rule25 [] [3, 8, -5])
  have r0 := holds_refl [3, 3, 4, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule67 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 8, 3] [3, 5, 5, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-3, -8, 3, 8] (rotate [-3, -8, 3, 8] [-5, -5, -4, -3] source13))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c1_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c1_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c1_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c1_rule30 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c1_rule32 [5] [4])
  have l6 := holds_trans l5 (holds_context c1_rule32 [] [5, 4])
  have r0 := holds_refl [-8, -3, 8, 3]
  have r1 := holds_trans r0 (holds_context c1_rule25 [] [-3, 8, 3])
  have r2 := holds_trans r1 (holds_context c1_rule22 [8] [8, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule68 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [5, 8, 3, 8] [3, 3, -5, 4] := by
  have h0 := (split [-5, -4, -3, -3] [-8, 3, 8, -5] (rotate [-3, -8, 3, 8, -5] [-5, -4, -3] source13))
  have l0 := holds_refl [-5, -4, -3, -3]
  have l1 := holds_trans l0 (holds_context c1_rule23 [-5] [-3, -3])
  have l2 := holds_trans l1 (holds_context c1_rule22 [-5, 4] [-3])
  have l3 := holds_trans l2 (holds_context c1_rule30 [-5] [-3])
  have l4 := holds_trans l3 (holds_context c1_rule31 [] [4, -3])
  have l5 := holds_trans l4 (holds_context c1_rule22 [3, -5, 4] [])
  have l6 := holds_trans l5 (holds_context c1_rule30 [3, -5] [])
  have l7 := holds_trans l6 (holds_context c1_rule31 [3] [4])
  have r0 := holds_refl [5, -8, -3, 8]
  have r1 := holds_trans r0 (holds_context c1_rule25 [5] [-3, 8])
  have r2 := holds_trans r1 (holds_context c1_rule22 [5, 8] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l7) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule70 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [4, 5, 5, 8] [3, 3, 8, 3] := by
  have h0 := (split [-3, -3, -8, 3] [8, -5, -5, -4] (rotate [-3, -8, 3, 8, -5, -5, -4] [-3] source13))
  have l0 := holds_refl [-3, -3, -8, 3]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-3, -8, 3])
  have l2 := holds_trans l1 (holds_context c1_rule22 [3] [-8, 3])
  have l3 := holds_trans l2 (holds_context c1_rule25 [3, 3] [3])
  have r0 := holds_refl [4, 5, 5, -8]
  have r1 := holds_trans r0 (holds_context c1_rule25 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule71 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 4] [6, 3, 7, 7] := by
  have h0 := (split [-9, -4, 9, 4] [-7, -7, -3, -6] (rotate [] [-9, -4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-9, -4, 9, 4]
  have l1 := holds_trans l0 (holds_context c1_rule23 [-9] [9, 4])
  have r0 := holds_refl [6, 3, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule72 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [9, 6, 3, 7] [4, 9, 4, -7] := by
  have h0 := (split [-4, 9, 4, -7] [-7, -3, -6, -9] (rotate [-9] [-4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-4, 9, 4, -7]
  have l1 := holds_trans l0 (holds_context c1_rule23 [] [9, 4, -7])
  have r0 := holds_refl [9, 6, 3, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule74 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [-9, 4, 9, 6] [3, 4, 7, 7] := by
  have h0 := (split [4, -7, -7, -3] [-6, -9, -4, 9] (rotate [-9, -4, 9] [4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [4, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context c1_rule28 [4] [-3])
  have l2 := holds_trans l1 (holds_context c1_rule22 [4, 7, 7] [])
  have l3 := holds_trans l2 (holds_context c1_rule34 [4, 7] [])
  have l4 := holds_trans l3 (holds_context c1_rule34 [4] [7])
  have l5 := holds_trans l4 (holds_context c1_rule30 [] [7, 7])
  have r0 := holds_refl [-9, 4, 9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule75 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, -9, 4, 9] [3, 7, 7, 6] := by
  have h0 := (split [-7, -7, -3, -6] [-9, -4, 9, 4] (rotate [-9, -4, 9, 4] [-7, -7, -3, -6] source19))
  have l0 := holds_refl [-7, -7, -3, -6]
  have l1 := holds_trans l0 (holds_context c1_rule28 [] [-3, -6])
  have l2 := holds_trans l1 (holds_context c1_rule22 [7, 7] [-6])
  have l3 := holds_trans l2 (holds_context c1_rule34 [7] [-6])
  have l4 := holds_trans l3 (holds_context c1_rule34 [] [7, -6])
  have l5 := holds_trans l4 (holds_context c1_rule24 [3, 7, 7] [])
  have r0 := holds_refl [-4, -9, 4, 9]
  have r1 := holds_trans r0 (holds_context c1_rule23 [] [-9, 4, 9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule76 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [7, 4, -9, 4] [3, -7, 6, -9] := by
  have h0 := (split [-7, -3, -6, -9] [-4, 9, 4, -7] (rotate [-9, -4, 9, 4, -7] [-7, -3, -6] source19))
  have l0 := holds_refl [-7, -3, -6, -9]
  have l1 := holds_trans l0 (holds_context c1_rule22 [-7] [-6, -9])
  have l2 := holds_trans l1 (holds_context c1_rule33 [] [-6, -9])
  have l3 := holds_trans l2 (holds_context c1_rule24 [3, -7] [-9])
  have r0 := holds_refl [7, -4, -9, 4]
  have r1 := holds_trans r0 (holds_context c1_rule23 [7] [-9, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule77 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [7, 7, 4, -9] [3, 6, -9, 4] := by
  have h0 := (split [-3, -6, -9, -4] [9, 4, -7, -7] (rotate [-9, -4, 9, 4, -7, -7] [-3, -6] source19))
  have l0 := holds_refl [-3, -6, -9, -4]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-6, -9, -4])
  have l2 := holds_trans l1 (holds_context c1_rule24 [3] [-9, -4])
  have l3 := holds_trans l2 (holds_context c1_rule23 [3, 6, -9] [])
  have r0 := holds_refl [7, 7, -4, -9]
  have r1 := holds_trans r0 (holds_context c1_rule23 [7, 7] [-9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule79 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s5_s4) [-7, 6, 7, 6] [3, 4, 5, 5] := by
  have h0 := (split [-7, -6, 7, 6] [-5, -5, -4, -3] (rotate [] [-7, -6, 7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [-7, -6, 7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule24 [-7] [7, 6])
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule81 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 5, 5] [6, 3, 7, 4] := by
  have h0 := (split [7, 6, -5, -5] [-4, -3, -7, -6] (rotate [-7, -6] [7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [7, 6, -5, -5]
  have l1 := holds_trans l0 (holds_context c1_rule27 [7, 6] [])
  have r0 := holds_refl [6, 7, 3, 4]
  have r1 := holds_trans r0 (holds_context c1_rule34 [6] [4])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule82 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, 3, 7] [6, 5, 5, 4] := by
  have h0 := (split [6, -5, -5, -4] [-3, -7, -6, 7] (rotate [-7, -6, 7] [6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c1_rule27 [6] [-4])
  have l2 := holds_trans l1 (holds_context c1_rule23 [6, 5, 5] [])
  have r0 := holds_refl [-7, 6, 7, 3]
  have r1 := holds_trans r0 (holds_context c1_rule34 [-7, 6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule83 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, 6, 7] [3, 5, 5, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-7, -6, 7, 6] (rotate [-7, -6, 7, 6] [-5, -5, -4, -3] source22))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c1_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c1_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c1_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c1_rule30 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c1_rule32 [5] [4])
  have l6 := holds_trans l5 (holds_context c1_rule32 [] [5, 4])
  have r0 := holds_refl [-6, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c1_rule24 [] [-7, 6, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule84 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 6, -7, 6] [3, -5, 4, -7] := by
  have h0 := (split [-5, -4, -3, -7] [-6, 7, 6, -5] (rotate [-7, -6, 7, 6, -5] [-5, -4, -3] source22))
  have l0 := holds_refl [-5, -4, -3, -7]
  have l1 := holds_trans l0 (holds_context c1_rule23 [-5] [-3, -7])
  have l2 := holds_trans l1 (holds_context c1_rule22 [-5, 4] [-7])
  have l3 := holds_trans l2 (holds_context c1_rule30 [-5] [-7])
  have l4 := holds_trans l3 (holds_context c1_rule31 [] [4, -7])
  have r0 := holds_refl [5, -6, -7, 6]
  have r1 := holds_trans r0 (holds_context c1_rule24 [5] [-7, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule85 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 6, -7] [3, 4, -7, 6] := by
  have h0 := (split [-4, -3, -7, -6] [7, 6, -5, -5] (rotate [-7, -6, 7, 6, -5, -5] [-4, -3] source22))
  have l0 := holds_refl [-4, -3, -7, -6]
  have l1 := holds_trans l0 (holds_context c1_rule23 [] [-3, -7, -6])
  have l2 := holds_trans l1 (holds_context c1_rule22 [4] [-7, -6])
  have l3 := holds_trans l2 (holds_context c1_rule30 [] [-7, -6])
  have l4 := holds_trans l3 (holds_context c1_rule24 [3, 4, -7] [])
  have r0 := holds_refl [5, 5, -6, -7]
  have r1 := holds_trans r0 (holds_context c1_rule24 [5, 5] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule86 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 5, 6] [3, -7, 6, 7] := by
  have h0 := (split [-3, -7, -6, 7] [6, -5, -5, -4] (rotate [-7, -6, 7, 6, -5, -5, -4] [-3] source22))
  have l0 := holds_refl [-3, -7, -6, 7]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-7, -6, 7])
  have l2 := holds_trans l1 (holds_context c1_rule24 [3, -7] [7])
  have r0 := holds_refl [4, 5, 5, -6]
  have r1 := holds_trans r0 (holds_context c1_rule24 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule91 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 7, 2, 9] [2, 3, 4, 5] := by
  have h0 := (split [2, 3, 4, 5] [5, 2, -7, -7, -3] (rotate [] [2, 3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [2, 3, 4, 5]
  have r0 := holds_refl [3, 7, 7, -2, -5]
  have r1 := holds_trans r0 (holds_context c1_rule21 [3, 7, 7] [-5])
  have r2 := holds_trans r1 (holds_context c1_rule50 [3, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule92 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, 7, 7, 2] [3, 4, 5, 5] := by
  have h0 := (split [3, 4, 5, 5] [2, -7, -7, -3, 2] (rotate [2] [3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [3, 4, 5, 5]
  have r0 := holds_refl [-2, 3, 7, 7, -2]
  have r1 := holds_trans r0 (holds_context c1_rule21 [] [3, 7, 7, -2])
  have r2 := holds_trans r1 (holds_context c1_rule21 [2, 3, 7, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule94 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 2, 8, 3, 7] [5, 2, 9] := by
  have h0 := (split [5, 5, 2, -7] [-7, -3, 2, 3, 4] (rotate [2, 3, 4] [5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [5, 5, 2, -7]
  have l1 := holds_trans l0 (holds_context c1_rule55 [5] [])
  have r0 := holds_refl [-4, -3, -2, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule23 [] [-3, -2, 3, 7])
  have r2 := holds_trans r1 (holds_context c1_rule22 [4] [-2, 3, 7])
  have r3 := holds_trans r2 (holds_context c1_rule30 [] [-2, 3, 7])
  have r4 := holds_trans r3 (holds_context c1_rule21 [3, 4] [3, 7])
  have r5 := holds_trans r4 (holds_context c1_rule42 [3] [3, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule95 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -5, 2, 8, 3] [2, 9, -7] := by
  have h0 := (split [5, 2, -7, -7] [-3, 2, 3, 4, 5] (rotate [2, 3, 4, 5] [5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [5, 2, -7, -7]
  have l1 := holds_trans l0 (holds_context c1_rule55 [] [-7])
  have r0 := holds_refl [-5, -4, -3, -2, 3]
  have r1 := holds_trans r0 (holds_context c1_rule23 [-5] [-3, -2, 3])
  have r2 := holds_trans r1 (holds_context c1_rule22 [-5, 4] [-2, 3])
  have r3 := holds_trans r2 (holds_context c1_rule30 [-5] [-2, 3])
  have r4 := holds_trans r3 (holds_context c1_rule31 [] [4, -2, 3])
  have r5 := holds_trans r4 (holds_context c1_rule21 [3, -5, 4] [3])
  have r6 := holds_trans r5 (holds_context c1_rule42 [3, -5] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r6))) (by central_nf)

theorem c1_rule100 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 3, 4, 5, 5] [3, 7, 7, 2] := by
  have h0 := (split [3, 7, 7, -2] [-5, -5, -4, -3, -2] (rotate [] [3, 7, 7, -2, -5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [3, 7, 7, -2]
  have l1 := holds_trans l0 (holds_context c1_rule21 [3, 7, 7] [])
  have r0 := holds_refl [2, 3, 4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule101 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 2, 3, 4, 5] [7, 2, 9] := by
  have h0 := (split [7, 7, -2, -5] [-5, -4, -3, -2, 3] (rotate [3] [7, 7, -2, -5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [7, 7, -2, -5]
  have l1 := holds_trans l0 (holds_context c1_rule21 [7, 7] [-5])
  have l2 := holds_trans l1 (holds_context c1_rule50 [7] [])
  have r0 := holds_refl [-3, 2, 3, 4, 5]
  have r1 := holds_trans r0 (holds_context c1_rule22 [] [2, 3, 4, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule103 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .viii_r3) [3, 7, 7, 2, 3] [2, 5, 5, 4] := by
  have h0 := (split [-2, -5, -5, -4] [-3, -2, 3, 7, 7] (rotate [3, 7, 7] [-2, -5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-2, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c1_rule21 [] [-5, -5, -4])
  have l2 := holds_trans l1 (holds_context c1_rule27 [2] [-4])
  have l3 := holds_trans l2 (holds_context c1_rule23 [2, 5, 5] [])
  have r0 := holds_refl [-7, -7, -3, 2, 3]
  have r1 := holds_trans r0 (holds_context c1_rule28 [] [-3, 2, 3])
  have r2 := holds_trans r1 (holds_context c1_rule22 [7, 7] [2, 3])
  have r3 := holds_trans r2 (holds_context c1_rule34 [7] [2, 3])
  have r4 := holds_trans r3 (holds_context c1_rule34 [] [7, 2, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule104 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 5, 5, 4] [3, 4, 5, 5] := by
  have h0 := (split [-5, -5, -4, -3] [-2, 3, 7, 7, -2] (rotate [3, 7, 7, -2] [-5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c1_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c1_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c1_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c1_rule30 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c1_rule32 [5] [4])
  have l6 := holds_trans l5 (holds_context c1_rule32 [] [5, 4])
  have r0 := holds_refl [2, -7, -7, -3, 2]
  have r1 := holds_trans r0 (holds_context c1_rule28 [2] [-3, 2])
  have r2 := holds_trans r1 (holds_context c1_rule22 [2, 7, 7] [2])
  have r3 := holds_trans r2 (holds_context c1_rule34 [2, 7] [2])
  have r4 := holds_trans r3 (holds_context c1_rule34 [2] [7, 2])
  have r5 := holds_trans r4 (holds_context c1_rule92 [] [])
  exact holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r5)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
