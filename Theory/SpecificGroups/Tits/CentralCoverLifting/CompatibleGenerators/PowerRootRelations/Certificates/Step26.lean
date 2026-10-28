module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step25

/-! Kernel-checked central word identities, chunk 26.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c9_rule57 : Holds (normalizedRelatorError .i_s8 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * normalizedRelatorError .iv_s2_s8) [10, 4, 10] [6, 8, 4] := by
  have h0 := (split [-10, 4, 10] [-8, -6, -4] (rotate [-4] [-10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-10, 4, 10]
  have l1 := holds_trans l0 (holds_context c9_rule26 [] [4, 10])
  have r0 := holds_refl [4, 6, 8]
  have r1 := holds_trans r0 (holds_context c9_rule35 [] [8])
  have r2 := holds_trans r1 (holds_context c9_rule36 [6] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c9_rule60 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6, 4] [6, 8, 4] := by
  have h0 := (split [-8, -6, -4] [-10, 4, 10] (rotate [-4, -10, 4, 10] [-8, -6] source18))
  have l0 := holds_refl [-8, -6, -4]
  have l1 := holds_trans l0 (holds_context c9_rule25 [] [-6, -4])
  have l2 := holds_trans l1 (holds_context c9_rule24 [8] [-4])
  have l3 := holds_trans l2 (holds_context c9_rule23 [8, 6] [])
  have r0 := holds_refl [-10, -4, 10]
  have r1 := holds_trans r0 (holds_context c9_rule26 [] [-4, 10])
  have r2 := holds_trans r1 (holds_context c9_rule23 [10] [10])
  have r3 := holds_trans r2 (holds_context c9_rule57 [] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r3)) (by central_nf)

theorem c9_rule63 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 4, 5, 5] [3, 8, 3, 8] := by
  have h0 := (split [-3, -8, 3, 8] [-5, -5, -4, -3] (rotate [] [-3, -8, 3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [-3, -8, 3, 8]
  have l1 := holds_trans l0 (holds_context c9_rule22 [] [-8, 3, 8])
  have l2 := holds_trans l1 (holds_context c9_rule25 [3] [3, 8])
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule65 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 3, 4] [3, 8, 5, 5] := by
  have h0 := (split [3, 8, -5, -5] [-4, -3, -3, -8] (rotate [-3, -8] [3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [3, 8, -5, -5]
  have l1 := holds_trans l0 (holds_context c9_rule27 [3, 8] [])
  have r0 := holds_refl [8, 3, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule68 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [5, 8, 3, 8] [3, 3, -5, 4] := by
  have h0 := (split [-5, -4, -3, -3] [-8, 3, 8, -5] (rotate [-3, -8, 3, 8, -5] [-5, -4, -3] source13))
  have l0 := holds_refl [-5, -4, -3, -3]
  have l1 := holds_trans l0 (holds_context c9_rule23 [-5] [-3, -3])
  have l2 := holds_trans l1 (holds_context c9_rule22 [-5, 4] [-3])
  have l3 := holds_trans l2 (holds_context c9_rule30 [-5] [-3])
  have l4 := holds_trans l3 (holds_context c9_rule31 [] [4, -3])
  have l5 := holds_trans l4 (holds_context c9_rule22 [3, -5, 4] [])
  have l6 := holds_trans l5 (holds_context c9_rule30 [3, -5] [])
  have l7 := holds_trans l6 (holds_context c9_rule31 [3] [4])
  have r0 := holds_refl [5, -8, -3, 8]
  have r1 := holds_trans r0 (holds_context c9_rule25 [5] [-3, 8])
  have r2 := holds_trans r1 (holds_context c9_rule22 [5, 8] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l7) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule71 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [6, 3, 7, 7] [-9, 4, 9, 4] := by
  have h0 := (split [-9, -4, 9, 4] [-7, -7, -3, -6] (rotate [] [-9, -4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-9, -4, 9, 4]
  have l1 := holds_trans l0 (holds_context c9_rule23 [-9] [9, 4])
  have r0 := holds_refl [6, 3, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule75 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, -9, 4, 9] [3, 7, 7, 6] := by
  have h0 := (split [-7, -7, -3, -6] [-9, -4, 9, 4] (rotate [-9, -4, 9, 4] [-7, -7, -3, -6] source19))
  have l0 := holds_refl [-7, -7, -3, -6]
  have l1 := holds_trans l0 (holds_context c9_rule28 [] [-3, -6])
  have l2 := holds_trans l1 (holds_context c9_rule22 [7, 7] [-6])
  have l3 := holds_trans l2 (holds_context c9_rule34 [7] [-6])
  have l4 := holds_trans l3 (holds_context c9_rule34 [] [7, -6])
  have l5 := holds_trans l4 (holds_context c9_rule24 [3, 7, 7] [])
  have r0 := holds_refl [-4, -9, 4, 9]
  have r1 := holds_trans r0 (holds_context c9_rule23 [] [-9, 4, 9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule80 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 7, 4, 5] [6, 7, 6, -5] := by
  have h0 := (split [-6, 7, 6, -5] [-5, -4, -3, -7] (rotate [-7] [-6, 7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [-6, 7, 6, -5]
  have l1 := holds_trans l0 (holds_context c9_rule24 [] [7, 6, -5])
  have r0 := holds_refl [7, 3, 4, 5]
  have r1 := holds_trans r0 (holds_context c9_rule34 [] [4, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule83 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 5, 5, 4] [6, -7, 6, 7] := by
  have h0 := (split [-5, -5, -4, -3] [-7, -6, 7, 6] (rotate [-7, -6, 7, 6] [-5, -5, -4, -3] source22))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c9_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c9_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c9_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c9_rule30 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c9_rule32 [5] [4])
  have l6 := holds_trans l5 (holds_context c9_rule32 [] [5, 4])
  have r0 := holds_refl [-6, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c9_rule24 [] [-7, 6, 7])
  exact holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule84 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 6, -7, 6] [3, -5, 4, -7] := by
  have h0 := (split [-5, -4, -3, -7] [-6, 7, 6, -5] (rotate [-7, -6, 7, 6, -5] [-5, -4, -3] source22))
  have l0 := holds_refl [-5, -4, -3, -7]
  have l1 := holds_trans l0 (holds_context c9_rule23 [-5] [-3, -7])
  have l2 := holds_trans l1 (holds_context c9_rule22 [-5, 4] [-7])
  have l3 := holds_trans l2 (holds_context c9_rule30 [-5] [-7])
  have l4 := holds_trans l3 (holds_context c9_rule31 [] [4, -7])
  have r0 := holds_refl [5, -6, -7, 6]
  have r1 := holds_trans r0 (holds_context c9_rule24 [5] [-7, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule85 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 6, -7] [3, 4, -7, 6] := by
  have h0 := (split [-4, -3, -7, -6] [7, 6, -5, -5] (rotate [-7, -6, 7, 6, -5, -5] [-4, -3] source22))
  have l0 := holds_refl [-4, -3, -7, -6]
  have l1 := holds_trans l0 (holds_context c9_rule23 [] [-3, -7, -6])
  have l2 := holds_trans l1 (holds_context c9_rule22 [4] [-7, -6])
  have l3 := holds_trans l2 (holds_context c9_rule30 [] [-7, -6])
  have l4 := holds_trans l3 (holds_context c9_rule24 [3, 4, -7] [])
  have r0 := holds_refl [5, 5, -6, -7]
  have r1 := holds_trans r0 (holds_context c9_rule24 [5, 5] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule86 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 5, 6] [3, -7, 6, 7] := by
  have h0 := (split [-3, -7, -6, 7] [6, -5, -5, -4] (rotate [-7, -6, 7, 6, -5, -5, -4] [-3] source22))
  have l0 := holds_refl [-3, -7, -6, 7]
  have l1 := holds_trans l0 (holds_context c9_rule22 [] [-7, -6, 7])
  have l2 := holds_trans l1 (holds_context c9_rule24 [3, -7] [7])
  have r0 := holds_refl [4, 5, 5, -6]
  have r1 := holds_trans r0 (holds_context c9_rule24 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule91 : Holds (normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 7, -9, 2] [2, 3, 4, 5] := by
  have h0 := (split [2, 3, 4, 5] [5, 2, -7, -7, -3] (rotate [] [2, 3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [2, 3, 4, 5]
  have r0 := holds_refl [3, 7, 7, -2, -5]
  have r1 := holds_trans r0 (holds_context c9_rule21 [3, 7, 7] [-5])
  have r2 := holds_trans r1 (holds_context c9_rule50 [3, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule92 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, 7, 7, 2] [3, 8, 3, 8] := by
  have h0 := (split [3, 4, 5, 5] [2, -7, -7, -3, 2] (rotate [2] [3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c9_rule63 [] [])
  have r0 := holds_refl [-2, 3, 7, 7, -2]
  have r1 := holds_trans r0 (holds_context c9_rule21 [] [3, 7, 7, -2])
  have r2 := holds_trans r1 (holds_context c9_rule21 [2, 3, 7, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule97 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 2, -7, 6, 7] [3, 7, 7, 2] := by
  have h0 := (split [-7, -7, -3, 2] [3, 4, 5, 5, 2] (rotate [2, 3, 4, 5, 5, 2] [-7, -7, -3] source36))
  have l0 := holds_refl [-7, -7, -3, 2]
  have l1 := holds_trans l0 (holds_context c9_rule28 [] [-3, 2])
  have l2 := holds_trans l1 (holds_context c9_rule22 [7, 7] [2])
  have l3 := holds_trans l2 (holds_context c9_rule34 [7] [2])
  have l4 := holds_trans l3 (holds_context c9_rule34 [] [7, 2])
  have r0 := holds_refl [-2, -5, -5, -4, -3]
  have r1 := holds_trans r0 (holds_context c9_rule21 [] [-5, -5, -4, -3])
  have r2 := holds_trans r1 (holds_context c9_rule27 [2] [-4, -3])
  have r3 := holds_trans r2 (holds_context c9_rule23 [2, 5, 5] [-3])
  have r4 := holds_trans r3 (holds_context c9_rule22 [2, 5, 5, 4] [])
  have r5 := holds_trans r4 (holds_context c9_rule30 [2, 5, 5] [])
  have r6 := holds_trans r5 (holds_context c9_rule32 [2, 5] [4])
  have r7 := holds_trans r6 (holds_context c9_rule32 [2] [5, 4])
  have r8 := holds_trans r7 (holds_context c9_rule83 [2] [])
  have r9 := holds_trans r8 (holds_context c9_rule43 [] [-7, 6, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r9))) (by central_nf)

theorem c9_rule98 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, -7, 2, 3] [-9, 2, -5, 4] := by
  have h0 := (split [-7, -3, 2, 3] [4, 5, 5, 2, -7] (rotate [2, 3, 4, 5, 5, 2, -7] [-7, -3] source36))
  have l0 := holds_refl [-7, -3, 2, 3]
  have l1 := holds_trans l0 (holds_context c9_rule22 [-7] [2, 3])
  have l2 := holds_trans l1 (holds_context c9_rule33 [] [2, 3])
  have r0 := holds_refl [7, -2, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c9_rule21 [7] [-5, -5, -4])
  have r2 := holds_trans r1 (holds_context c9_rule50 [] [-5, -4])
  have r3 := holds_trans r2 (holds_context c9_rule23 [-9, 2, -5] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r3)) (by central_nf)

theorem c9_rule104 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [3, 8, 3, 8] [6, -7, 6, 7] := by
  have h0 := (split [-5, -5, -4, -3] [-2, 3, 7, 7, -2] (rotate [3, 7, 7, -2] [-5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c9_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c9_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c9_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c9_rule30 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c9_rule32 [5] [4])
  have l6 := holds_trans l5 (holds_context c9_rule32 [] [5, 4])
  have l7 := holds_trans l6 (holds_context c9_rule83 [] [])
  have r0 := holds_refl [2, -7, -7, -3, 2]
  have r1 := holds_trans r0 (holds_context c9_rule28 [2] [-3, 2])
  have r2 := holds_trans r1 (holds_context c9_rule22 [2, 7, 7] [2])
  have r3 := holds_trans r2 (holds_context c9_rule34 [2, 7] [2])
  have r4 := holds_trans r3 (holds_context c9_rule34 [2] [7, 2])
  have r5 := holds_trans r4 (holds_context c9_rule92 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l7) (holds_trans h0 r5))) (by central_nf)

theorem c9_rule105 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -5, 2, 8] [-9, 2, 3, -7] := by
  have h0 := (split [-5, -4, -3, -2] [3, 7, 7, -2, -5] (rotate [3, 7, 7, -2, -5] [-5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -4, -3, -2]
  have l1 := holds_trans l0 (holds_context c9_rule23 [-5] [-3, -2])
  have l2 := holds_trans l1 (holds_context c9_rule22 [-5, 4] [-2])
  have l3 := holds_trans l2 (holds_context c9_rule30 [-5] [-2])
  have l4 := holds_trans l3 (holds_context c9_rule31 [] [4, -2])
  have l5 := holds_trans l4 (holds_context c9_rule21 [3, -5, 4] [])
  have l6 := holds_trans l5 (holds_context c9_rule42 [3, -5] [])
  have r0 := holds_refl [5, 2, -7, -7, -3]
  have r1 := holds_trans r0 (holds_context c9_rule55 [] [-7, -3])
  have r2 := holds_trans r1 (holds_context c9_rule22 [-9, 2, -7] [])
  have r3 := holds_trans r2 (holds_context c9_rule33 [-9, 2] [])
  exact holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r3)) (by central_nf)

theorem c9_rule132 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, 9, 6, -7, 6, 7] [4, 9, 4] := by
  have h0 := (split [9, 6, -7, -7, -3] [-5, -5, -4, -3, -9, -6] (rotate [-9, -6] [9, 6, -7, -7, -3, -5, -5, -4, -3] source20))
  have l0 := holds_refl [9, 6, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context c9_rule28 [9, 6] [-3])
  have l2 := holds_trans l1 (holds_context c9_rule22 [9, 6, 7, 7] [])
  have l3 := holds_trans l2 (holds_context c9_rule34 [9, 6, 7] [])
  have l4 := holds_trans l3 (holds_context c9_rule34 [9, 6] [7])
  have l5 := holds_trans l4 (holds_context c9_rule71 [9] [])
  have l6 := holds_trans l5 (holds_context c9_rule16 [] [4, 9, 4])
  have r0 := holds_refl [6, 9, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c9_rule63 [6, 9] [])
  have r2 := holds_trans r1 (holds_context c9_rule104 [6, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule158 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 4, -5, -7, 5] [3, -7, 6] := by
  have h0 := (split [-3, -4, -5, -7, 5] [7, -6, -5, -5, -4] (rotate [-5, -7, 5, 7, -6, -5, -5, -4] [-3, -4] source21))
  have l0 := holds_refl [-3, -4, -5, -7, 5]
  have l1 := holds_trans l0 (holds_context c9_rule22 [] [-4, -5, -7, 5])
  have l2 := holds_trans l1 (holds_context c9_rule23 [3] [-5, -7, 5])
  have r0 := holds_refl [4, 5, 5, 6, -7]
  have r1 := holds_trans r0 (holds_context c9_rule86 [] [-7])
  have r2 := holds_trans r1 (holds_context c9_rule12 [3, -7, 6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c9_rule179 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ)) [2, 3, -9, 2, 3] [-9, -7, 5, 4] := by
  have h0 := (split [-2, -3, -2, 9, 3] [4, 5, 5, 5, 7, 9] (rotate [9, 3, 4, 5, 5, 5, 7, 9] [-2, -3, -2] (inverted source33)))
  have l0 := holds_refl [-2, -3, -2, 9, 3]
  have l1 := holds_trans l0 (holds_context c9_rule21 [] [-3, -2, 9, 3])
  have l2 := holds_trans l1 (holds_context c9_rule22 [2] [-2, 9, 3])
  have l3 := holds_trans l2 (holds_context c9_rule21 [2, 3] [9, 3])
  have l4 := holds_trans l3 (holds_context c9_rule44 [2, 3] [3])
  have r0 := holds_refl [-9, -7, -5, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c9_rule27 [-9, -7] [-5, -4])
  have r2 := holds_trans r1 (holds_context c9_rule8 [-9, -7, 5] [-4])
  have r3 := holds_trans r2 (holds_context c9_rule23 [-9, -7, 5] [])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r3)) (by central_nf)

theorem c9_rule223 : Holds (normalizedRelatorError .i_r8) [2, 2] [] := by
  have h0 := c9_rule2
  have l0 := holds_refl [2, -2]
  have l1 := holds_trans l0 (holds_context c9_rule21 [2] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule224 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c9_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c9_rule22 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule225 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c9_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context c9_rule23 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule226 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c9_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context c9_rule24 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule227 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c9_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context c9_rule25 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule229 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule27 [5] [])) (holds_context c9_rule8 [] [-5]))
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule230 : Holds (normalizedRelatorError .i_s5) [7, 7, 7] [-7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule28 [7] [])) (holds_context c9_rule12 [] [-7]))
  have l0 := holds_refl [7, 7, 7]
  have r0 := holds_refl [-7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule242 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s7) [4, 9, 2] [2, 8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule45 [4] [])) (holds_context c9_rule42 [] [-9]))
  have l0 := holds_refl [4, 9, 2]
  have r0 := holds_refl [2, 8, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule243 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [9, 5, 2] [2, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule47 [9] [])) (holds_context c9_rule16 [] [2, 7]))
  have l0 := holds_refl [9, 5, 2]
  have r0 := holds_refl [2, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule245 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ)) [-7, 5, 2] [2, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule53 [] [7])) (holds_context c9_rule47 [-7] []))
  have l0 := holds_refl [2, -5, 7]
  have r0 := holds_refl [-7, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule247 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, -7, 2] [-5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule223 [-5, -9] [])) (holds_context c9_rule48 [] [2]))
  have l0 := holds_refl [-5, -9]
  have r0 := holds_refl [2, -7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule250 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [9, 7, 6, 2] [2, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule46 [] [6])) (holds_context c9_rule43 [9, 7] []))
  have l0 := holds_refl [2, 5, 6]
  have r0 := holds_refl [9, 7, 6, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule254 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [-9, 2, 3, 7] [5, 2, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule47 [] [3])) (holds_context c9_rule34 [-9, 2] []))
  have l0 := holds_refl [5, 2, 3]
  have r0 := holds_refl [-9, 2, 3, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule284 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [-5, -9, -5, 2] [2, 7, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule54 [-5, -9] [])) (holds_context c9_rule48 [] [-7, -9]))
  have l0 := holds_refl [-5, -9, -5, 2]
  have r0 := holds_refl [2, -7, -7, -9]
  have r1 := holds_trans r0 (holds_context c9_rule28 [2] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule302 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6, 8, 4] [6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule60 [] [8])) (holds_context c9_rule36 [8, 6] []))
  have l0 := holds_refl [6, 8, 4, 8]
  have l1 := holds_trans l0 (holds_context c9_rule36 [6, 8] [])
  have l2 := holds_trans l1 (holds_context c9_rule227 [6] [4])
  have r0 := holds_refl [8, 6, 8, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule303 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6, 8] [6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule302 [] [4])) (holds_context c9_rule225 [8, 6, 8] []))
  have l0 := holds_refl [6, 4, 4]
  have l1 := holds_trans l0 (holds_context c9_rule225 [6] [])
  have r0 := holds_refl [8, 6, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule304 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [8, 6] [6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule303 [8] [])) (holds_context c9_rule227 [] [6, 8]))
  have l0 := holds_refl [8, 6]
  have r0 := holds_refl [6, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule313 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [3, 8, 5, 5] [8, 4] := by
  have h0 := c9_rule65
  have l0 := holds_refl [8, 3, 3, 4]
  have l1 := holds_trans l0 (holds_context c9_rule224 [8] [4])
  have r0 := holds_refl [3, 8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule314 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 4, -5] [3, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule313 [] [-5])) (holds_context c9_rule8 [3, 8, 5] []))
  have l0 := holds_refl [8, 4, -5]
  have r0 := holds_refl [3, 8, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
