module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step01

/-! Kernel-checked central word identities, chunk 2.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c1_rule105 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -5, 2, 8] [2, 9, 3, -7] := by
  have h0 := (split [-5, -4, -3, -2] [3, 7, 7, -2, -5] (rotate [3, 7, 7, -2, -5] [-5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -4, -3, -2]
  have l1 := holds_trans l0 (holds_context c1_rule23 [-5] [-3, -2])
  have l2 := holds_trans l1 (holds_context c1_rule22 [-5, 4] [-2])
  have l3 := holds_trans l2 (holds_context c1_rule30 [-5] [-2])
  have l4 := holds_trans l3 (holds_context c1_rule31 [] [4, -2])
  have l5 := holds_trans l4 (holds_context c1_rule21 [3, -5, 4] [])
  have l6 := holds_trans l5 (holds_context c1_rule42 [3, -5] [])
  have r0 := holds_refl [5, 2, -7, -7, -3]
  have r1 := holds_trans r0 (holds_context c1_rule55 [] [-7, -3])
  have r2 := holds_trans r1 (holds_context c1_rule22 [2, 9, -7] [])
  have r3 := holds_trans r2 (holds_context c1_rule33 [2, 9] [])
  exact holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r3)) (by central_nf)

theorem c1_rule106 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [5, 2, 9, -7] [3, 2, 8, 3] := by
  have h0 := (split [-4, -3, -2, 3] [7, 7, -2, -5, -5] (rotate [3, 7, 7, -2, -5, -5] [-4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-4, -3, -2, 3]
  have l1 := holds_trans l0 (holds_context c1_rule23 [] [-3, -2, 3])
  have l2 := holds_trans l1 (holds_context c1_rule22 [4] [-2, 3])
  have l3 := holds_trans l2 (holds_context c1_rule30 [] [-2, 3])
  have l4 := holds_trans l3 (holds_context c1_rule21 [3, 4] [3])
  have l5 := holds_trans l4 (holds_context c1_rule42 [3] [3])
  have r0 := holds_refl [5, 5, 2, -7, -7]
  have r1 := holds_trans r0 (holds_context c1_rule55 [5] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule107 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [4, 5, 2, 9] [3, 2, 3, 7] := by
  have h0 := (split [-3, -2, 3, 7] [7, -2, -5, -5, -4] (rotate [3, 7, 7, -2, -5, -5, -4] [-3, -2] (inverted source36)))
  have l0 := holds_refl [-3, -2, 3, 7]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-2, 3, 7])
  have l2 := holds_trans l1 (holds_context c1_rule21 [3] [3, 7])
  have r0 := holds_refl [4, 5, 5, 2, -7]
  have r1 := holds_trans r0 (holds_context c1_rule55 [4, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule108 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 4, 5, 5, 2] [2, 3, 7, 7] := by
  have h0 := (split [-2, 3, 7, 7] [-2, -5, -5, -4, -3] (rotate [3, 7, 7, -2, -5, -5, -4, -3] [-2] (inverted source36)))
  have l0 := holds_refl [-2, 3, 7, 7]
  have l1 := holds_trans l0 (holds_context c1_rule21 [] [3, 7, 7])
  have r0 := holds_refl [3, 4, 5, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule112 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 10, 3, 9, 9, 3] [10, 3, 4, 5, 5] := by
  have h0 := (split [10, -3, -5, -5, -4] [-3, -9, -9, -3, -10, 3] (rotate [-3, -10, 3] [10, -3, -5, -5, -4, -3, -9, -9] source15))
  have l0 := holds_refl [10, -3, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c1_rule22 [10] [-5, -5, -4])
  have l2 := holds_trans l1 (holds_context c1_rule27 [10, 3] [-4])
  have l3 := holds_trans l2 (holds_context c1_rule23 [10, 3, 5, 5] [])
  have l4 := holds_trans l3 (holds_context c1_rule104 [10] [])
  have r0 := holds_refl [-3, 10, 3, 9, 9, 3]
  have r1 := holds_trans r0 (holds_context c1_rule22 [] [10, 3, 9, 9, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule115 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [3, 5, 10, 3, 10, 3] [3, -5, 4, 9, 9] := by
  have h0 := (split [-5, -4, -3, -9, -9] [-3, -10, 3, 10, -3, -5] (rotate [-3, -10, 3, 10, -3, -5] [-5, -4, -3, -9, -9] source15))
  have l0 := holds_refl [-5, -4, -3, -9, -9]
  have l1 := holds_trans l0 (holds_context c1_rule23 [-5] [-3, -9, -9])
  have l2 := holds_trans l1 (holds_context c1_rule22 [-5, 4] [-9, -9])
  have l3 := holds_trans l2 (holds_context c1_rule30 [-5] [-9, -9])
  have l4 := holds_trans l3 (holds_context c1_rule31 [] [4, -9, -9])
  have l5 := holds_trans l4 (holds_context c1_rule29 [3, -5, 4] [])
  have r0 := holds_refl [5, 3, -10, -3, 10, 3]
  have r1 := holds_trans r0 (holds_context c1_rule32 [] [-10, -3, 10, 3])
  have r2 := holds_trans r1 (holds_context c1_rule26 [3, 5] [-3, 10, 3])
  have r3 := holds_trans r2 (holds_context c1_rule22 [3, 5, 10] [10, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r3))) (by central_nf)

theorem c1_rule117 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [3, 4, 5, 5, 10, 3] [3, 9, 9, 3, 10] := by
  have h0 := (split [-3, -9, -9, -3, -10] [3, 10, -3, -5, -5, -4] (rotate [-3, -10, 3, 10, -3, -5, -5, -4] [-3, -9, -9] source15))
  have l0 := holds_refl [-3, -9, -9, -3, -10]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-9, -9, -3, -10])
  have l2 := holds_trans l1 (holds_context c1_rule29 [3] [-3, -10])
  have l3 := holds_trans l2 (holds_context c1_rule22 [3, 9, 9] [-10])
  have l4 := holds_trans l3 (holds_context c1_rule26 [3, 9, 9, 3] [])
  have r0 := holds_refl [4, 5, 5, 3, -10, -3]
  have r1 := holds_trans r0 (holds_context c1_rule32 [4, 5] [-10, -3])
  have r2 := holds_trans r1 (holds_context c1_rule32 [4] [5, -10, -3])
  have r3 := holds_trans r2 (holds_context c1_rule30 [] [5, 5, -10, -3])
  have r4 := holds_trans r3 (holds_context c1_rule26 [3, 4, 5, 5] [-3])
  have r5 := holds_trans r4 (holds_context c1_rule22 [3, 4, 5, 5, 10] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule123 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [3, 9, 9, 3, 10, 3] [3, 4, 5, 5, 10] := by
  have h0 := (split [4, 5, 5, 3, -10] [-3, 10, 3, 9, 9, 3] (rotate [9, 9, 3] [4, 5, 5, 3, -10, -3, 10, 3] (inverted source15)))
  have l0 := holds_refl [4, 5, 5, 3, -10]
  have l1 := holds_trans l0 (holds_context c1_rule32 [4, 5] [-10])
  have l2 := holds_trans l1 (holds_context c1_rule32 [4] [5, -10])
  have l3 := holds_trans l2 (holds_context c1_rule30 [] [5, 5, -10])
  have l4 := holds_trans l3 (holds_context c1_rule26 [3, 4, 5, 5] [])
  have r0 := holds_refl [-3, -9, -9, -3, -10, 3]
  have r1 := holds_trans r0 (holds_context c1_rule22 [] [-9, -9, -3, -10, 3])
  have r2 := holds_trans r1 (holds_context c1_rule29 [3] [-3, -10, 3])
  have r3 := holds_trans r2 (holds_context c1_rule22 [3, 9, 9] [-10, 3])
  have r4 := holds_trans r3 (holds_context c1_rule26 [3, 9, 9, 3] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule129 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [3, 10, 3, 4, 5, 5] [10, 3, 9, 9, 3] := by
  have h0 := (split [10, 3, 9, 9, 3] [4, 5, 5, 3, -10, -3] (rotate [9, 9, 3, 4, 5, 5, 3, -10, -3] [10, 3] (inverted source15)))
  have l0 := holds_refl [10, 3, 9, 9, 3]
  have r0 := holds_refl [3, 10, -3, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c1_rule22 [3, 10] [-5, -5, -4])
  have r2 := holds_trans r1 (holds_context c1_rule27 [3, 10, 3] [-4])
  have r3 := holds_trans r2 (holds_context c1_rule23 [3, 10, 3, 5, 5] [])
  have r4 := holds_trans r3 (holds_context c1_rule104 [3, 10] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r4))) (by central_nf)

theorem c1_rule137 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 7, 6, -9, 6, 9] [3, 3, 4, 5, 5] := by
  have h0 := (split [-3, -5, -5, -4, -3] [-9, -6, 9, 6, -7, -7] (rotate [-9, -6, 9, 6, -7, -7] [-3, -5, -5, -4, -3] source20))
  have l0 := holds_refl [-3, -5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-5, -5, -4, -3])
  have l2 := holds_trans l1 (holds_context c1_rule27 [3] [-4, -3])
  have l3 := holds_trans l2 (holds_context c1_rule23 [3, 5, 5] [-3])
  have l4 := holds_trans l3 (holds_context c1_rule104 [] [-3])
  have l5 := holds_trans l4 (holds_context c1_rule22 [3, 4, 5, 5] [])
  have l6 := holds_trans l5 (holds_context c1_rule32 [3, 4, 5] [])
  have l7 := holds_trans l6 (holds_context c1_rule32 [3, 4] [5])
  have l8 := holds_trans l7 (holds_context c1_rule30 [3] [5, 5])
  have r0 := holds_refl [7, 7, -6, -9, 6, 9]
  have r1 := holds_trans r0 (holds_context c1_rule24 [7, 7] [-9, 6, 9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l8) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule141 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [3, 4, 5, 5, 7, 7] [3, -9, 6, 9, 6] := by
  have h0 := (split [-3, -9, -6, 9, 6] [-7, -7, -3, -5, -5, -4] (rotate [-9, -6, 9, 6, -7, -7, -3, -5, -5, -4] [-3] source20))
  have l0 := holds_refl [-3, -9, -6, 9, 6]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-9, -6, 9, 6])
  have l2 := holds_trans l1 (holds_context c1_rule24 [3, -9] [9, 6])
  have r0 := holds_refl [4, 5, 5, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c1_rule32 [4, 5] [7, 7])
  have r2 := holds_trans r1 (holds_context c1_rule32 [4] [5, 7, 7])
  have r3 := holds_trans r2 (holds_context c1_rule30 [] [5, 5, 7, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r3))) (by central_nf)

theorem c1_rule146 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [3, 4, 5, 5, -9, 6] [3, 7, 7, 6, -9] := by
  have h0 := (split [3, 7, 7, -6, -9] [6, 9, 3, 4, 5, 5] (rotate [3, 4, 5, 5] [3, 7, 7, -6, -9, 6, 9] (inverted source20)))
  have l0 := holds_refl [3, 7, 7, -6, -9]
  have l1 := holds_trans l0 (holds_context c1_rule24 [3, 7, 7] [-9])
  have r0 := holds_refl [-5, -5, -4, -3, -9, -6]
  have r1 := holds_trans r0 (holds_context c1_rule27 [] [-4, -3, -9, -6])
  have r2 := holds_trans r1 (holds_context c1_rule23 [5, 5] [-3, -9, -6])
  have r3 := holds_trans r2 (holds_context c1_rule22 [5, 5, 4] [-9, -6])
  have r4 := holds_trans r3 (holds_context c1_rule30 [5, 5] [-9, -6])
  have r5 := holds_trans r4 (holds_context c1_rule32 [5] [4, -9, -6])
  have r6 := holds_trans r5 (holds_context c1_rule32 [] [5, 4, -9, -6])
  have r7 := holds_trans r6 (holds_context c1_rule104 [] [-9, -6])
  have r8 := holds_trans r7 (holds_context c1_rule24 [3, 4, 5, 5, -9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r8))) (by central_nf)

theorem c1_rule149 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4) [3, 7, 7, 5, 5, 4] [6, -9, 6, 9, 3] := by
  have h0 := (split [-6, -9, 6, 9, 3] [4, 5, 5, 3, 7, 7] (rotate [3, 4, 5, 5, 3, 7, 7] [-6, -9, 6, 9] (inverted source20)))
  have l0 := holds_refl [-6, -9, 6, 9, 3]
  have l1 := holds_trans l0 (holds_context c1_rule24 [] [-9, 6, 9, 3])
  have r0 := holds_refl [-7, -7, -3, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c1_rule28 [] [-3, -5, -5, -4])
  have r2 := holds_trans r1 (holds_context c1_rule22 [7, 7] [-5, -5, -4])
  have r3 := holds_trans r2 (holds_context c1_rule34 [7] [-5, -5, -4])
  have r4 := holds_trans r3 (holds_context c1_rule34 [] [7, -5, -5, -4])
  have r5 := holds_trans r4 (holds_context c1_rule27 [3, 7, 7] [-4])
  have r6 := holds_trans r5 (holds_context c1_rule23 [3, 7, 7, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r6))) (by central_nf)

theorem c1_rule150 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4) [6, 3, 7, 7, 5, 5] [-9, 6, 9, 3, 4] := by
  have h0 := (split [-9, 6, 9, 3, 4] [5, 5, 3, 7, 7, -6] (rotate [3, 4, 5, 5, 3, 7, 7, -6] [-9, 6, 9] (inverted source20)))
  have l0 := holds_refl [-9, 6, 9, 3, 4]
  have r0 := holds_refl [6, -7, -7, -3, -5, -5]
  have r1 := holds_trans r0 (holds_context c1_rule28 [6] [-3, -5, -5])
  have r2 := holds_trans r1 (holds_context c1_rule22 [6, 7, 7] [-5, -5])
  have r3 := holds_trans r2 (holds_context c1_rule34 [6, 7] [-5, -5])
  have r4 := holds_trans r3 (holds_context c1_rule34 [6] [7, -5, -5])
  have r5 := holds_trans r4 (holds_context c1_rule27 [6, 3, 7, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r5))) (by central_nf)

theorem c1_rule152 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [9, 3, 4, 5, 5] [4, 6, 9, 4] := by
  have h0 := (split [9, 3, 4, 5, 5] [3, 7, 7, -6, -9, 6] (rotate [3, 4, 5, 5, 3, 7, 7, -6, -9, 6] [9] (inverted source20)))
  have l0 := holds_refl [9, 3, 4, 5, 5]
  have r0 := holds_refl [-6, 9, 6, -7, -7, -3]
  have r1 := holds_trans r0 (holds_context c1_rule24 [] [9, 6, -7, -7, -3])
  have r2 := holds_trans r1 (holds_context c1_rule28 [6, 9, 6] [-3])
  have r3 := holds_trans r2 (holds_context c1_rule22 [6, 9, 6, 7, 7] [])
  have r4 := holds_trans r3 (holds_context c1_rule34 [6, 9, 6, 7] [])
  have r5 := holds_trans r4 (holds_context c1_rule34 [6, 9, 6] [7])
  have r6 := holds_trans r5 (holds_context c1_rule72 [6] [7])
  have r7 := holds_trans r6 (holds_context c1_rule35 [] [9, 4, -7, 7])
  have r8 := holds_trans r7 (holds_context c1_rule13 [4, 6, 9, 4] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r8)) (by central_nf)

theorem c1_rule155 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 6, 3, 7, 4] [3, 7, 5, 4, 4] := by
  have h0 := (split [5, 7, -6, -5, -5] [-4, -3, -4, -5, -7] (rotate [-5, -7] [5, 7, -6, -5, -5, -4, -3, -4] source21))
  have l0 := holds_refl [5, 7, -6, -5, -5]
  have l1 := holds_trans l0 (holds_context c1_rule24 [5, 7] [-5, -5])
  have l2 := holds_trans l1 (holds_context c1_rule27 [5, 7, 6] [])
  have l3 := holds_trans l2 (holds_context c1_rule81 [5] [])
  have r0 := holds_refl [7, 5, 4, 3, 4]
  have r1 := holds_trans r0 (holds_context c1_rule30 [7, 5] [4])
  have r2 := holds_trans r1 (holds_context c1_rule32 [7] [4, 4])
  have r3 := holds_trans r2 (holds_context c1_rule34 [] [5, 4, 4])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r3)) (by central_nf)

theorem c1_rule156 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 3, 7, 4, 4] [3, -5, 7, 5, 4] := by
  have h0 := (split [7, -6, -5, -5, -4] [-3, -4, -5, -7, 5] (rotate [-5, -7, 5] [7, -6, -5, -5, -4, -3, -4] source21))
  have l0 := holds_refl [7, -6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c1_rule24 [7] [-5, -5, -4])
  have l2 := holds_trans l1 (holds_context c1_rule27 [7, 6] [-4])
  have l3 := holds_trans l2 (holds_context c1_rule81 [] [-4])
  have l4 := holds_trans l3 (holds_context c1_rule23 [6, 3, 7, 4] [])
  have r0 := holds_refl [-5, 7, 5, 4, 3]
  have r1 := holds_trans r0 (holds_context c1_rule30 [-5, 7, 5] [])
  have r2 := holds_trans r1 (holds_context c1_rule32 [-5, 7] [4])
  have r3 := holds_trans r2 (holds_context c1_rule34 [-5] [5, 4])
  have r4 := holds_trans r3 (holds_context c1_rule31 [] [7, 5, 4])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r4)) (by central_nf)

theorem c1_rule157 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-7, -5, 7, 5, 4] [6, 3, 4, 5, 5] := by
  have h0 := (split [-6, -5, -5, -4, -3] [-4, -5, -7, 5, 7] (rotate [-5, -7, 5, 7] [-6, -5, -5, -4, -3, -4] source21))
  have l0 := holds_refl [-6, -5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c1_rule24 [] [-5, -5, -4, -3])
  have l2 := holds_trans l1 (holds_context c1_rule27 [6] [-4, -3])
  have l3 := holds_trans l2 (holds_context c1_rule23 [6, 5, 5] [-3])
  have l4 := holds_trans l3 (holds_context c1_rule22 [6, 5, 5, 4] [])
  have l5 := holds_trans l4 (holds_context c1_rule30 [6, 5, 5] [])
  have l6 := holds_trans l5 (holds_context c1_rule32 [6, 5] [4])
  have l7 := holds_trans l6 (holds_context c1_rule32 [6] [5, 4])
  have l8 := holds_trans l7 (holds_context c1_rule104 [6] [])
  have r0 := holds_refl [-7, -5, 7, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l8) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule158 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, -7, -5, 7, 5] [3, 4, 5, 5, 4] := by
  have h0 := (split [-5, -5, -4, -3, -4] [-5, -7, 5, 7, -6] (rotate [-5, -7, 5, 7, -6] [-5, -5, -4, -3, -4] source21))
  have l0 := holds_refl [-5, -5, -4, -3, -4]
  have l1 := holds_trans l0 (holds_context c1_rule27 [] [-4, -3, -4])
  have l2 := holds_trans l1 (holds_context c1_rule23 [5, 5] [-3, -4])
  have l3 := holds_trans l2 (holds_context c1_rule22 [5, 5, 4] [-4])
  have l4 := holds_trans l3 (holds_context c1_rule30 [5, 5] [-4])
  have l5 := holds_trans l4 (holds_context c1_rule32 [5] [4, -4])
  have l6 := holds_trans l5 (holds_context c1_rule32 [] [5, 4, -4])
  have l7 := holds_trans l6 (holds_context c1_rule104 [] [-4])
  have l8 := holds_trans l7 (holds_context c1_rule23 [3, 4, 5, 5] [])
  have r0 := holds_refl [6, -7, -5, 7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l8) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule159 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [5, 6, -7, -5, 7] [3, -5, 4, 4, -5] := by
  have h0 := (split [-5, -4, -3, -4, -5] [-7, 5, 7, -6, -5] (rotate [-5, -7, 5, 7, -6, -5] [-5, -4, -3, -4] source21))
  have l0 := holds_refl [-5, -4, -3, -4, -5]
  have l1 := holds_trans l0 (holds_context c1_rule23 [-5] [-3, -4, -5])
  have l2 := holds_trans l1 (holds_context c1_rule22 [-5, 4] [-4, -5])
  have l3 := holds_trans l2 (holds_context c1_rule30 [-5] [-4, -5])
  have l4 := holds_trans l3 (holds_context c1_rule31 [] [4, -4, -5])
  have l5 := holds_trans l4 (holds_context c1_rule23 [3, -5, 4] [-5])
  have r0 := holds_refl [5, 6, -7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule160 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 4, -7, 6, -5] [3, 4, 4, -5, -7] := by
  have h0 := (split [-4, -3, -4, -5, -7] [5, 7, -6, -5, -5] (rotate [-5, -7, 5, 7, -6, -5, -5] [-4, -3, -4] source21))
  have l0 := holds_refl [-4, -3, -4, -5, -7]
  have l1 := holds_trans l0 (holds_context c1_rule23 [] [-3, -4, -5, -7])
  have l2 := holds_trans l1 (holds_context c1_rule22 [4] [-4, -5, -7])
  have l3 := holds_trans l2 (holds_context c1_rule30 [] [-4, -5, -7])
  have l4 := holds_trans l3 (holds_context c1_rule23 [3, 4] [-5, -7])
  have r0 := holds_refl [5, 5, 6, -7, -5]
  have r1 := holds_trans r0 (holds_context c1_rule85 [] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule161 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 4, -5, -7, 5] [3, -7, 6] := by
  have h0 := (split [-3, -4, -5, -7, 5] [7, -6, -5, -5, -4] (rotate [-5, -7, 5, 7, -6, -5, -5, -4] [-3, -4] source21))
  have l0 := holds_refl [-3, -4, -5, -7, 5]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-4, -5, -7, 5])
  have l2 := holds_trans l1 (holds_context c1_rule23 [3] [-5, -7, 5])
  have r0 := holds_refl [4, 5, 5, 6, -7]
  have r1 := holds_trans r0 (holds_context c1_rule86 [] [-7])
  have r2 := holds_trans r1 (holds_context c1_rule12 [3, -7, 6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c1_rule165 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1) [3, 2, -9, -7, -5] [2, 4, 6, 9, 4] := by
  have h0 := (split [3, 2, -9, -7, -5] [-5, -5, -4, -3, -9, 2] (rotate [2] [3, 2, -9, -7, -5, -5, -5, -4, -3, -9] source33))
  have l0 := holds_refl [3, 2, -9, -7, -5]
  have r0 := holds_refl [-2, 9, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule21 [] [9, 3, 4, 5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule152 [2] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c1_rule176 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7) [2, 9, 3, 2, -9, -7] [3, 4, 5, 5, 5] := by
  have h0 := (split [3, 4, 5, 5, 5] [7, 9, -2, -3, -2, 9] (rotate [9] [3, 4, 5, 5, 5, 7, 9, -2, -3, -2] (inverted source33)))
  have l0 := holds_refl [3, 4, 5, 5, 5]
  have r0 := holds_refl [-9, 2, 3, 2, -9, -7]
  have r1 := holds_trans r0 (holds_context c1_rule44 [] [3, 2, -9, -7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule177 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .viii_s1 * normalizedRelatorError .viii_s7) [3, 2, 9, 3, 2, -9] [4, 5, 5, 5, 7] := by
  have h0 := (split [4, 5, 5, 5, 7] [9, -2, -3, -2, 9, 3] (rotate [9, 3] [4, 5, 5, 5, 7, 9, -2, -3, -2] (inverted source33)))
  have l0 := holds_refl [4, 5, 5, 5, 7]
  have r0 := holds_refl [-3, -9, 2, 3, 2, -9]
  have r1 := holds_trans r0 (holds_context c1_rule22 [] [-9, 2, 3, 2, -9])
  have r2 := holds_trans r1 (holds_context c1_rule44 [3] [3, 2, -9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule180 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 7, 2, -9, 3] [2, 3, 7, 7, 9] := by
  have h0 := (split [5, 7, 9, -2, -3] [-2, 9, 3, 4, 5, 5] (rotate [9, 3, 4, 5, 5] [5, 7, 9, -2, -3, -2] (inverted source33)))
  have l0 := holds_refl [5, 7, 9, -2, -3]
  have l1 := holds_trans l0 (holds_context c1_rule21 [5, 7, 9] [-3])
  have l2 := holds_trans l1 (holds_context c1_rule45 [5, 7] [-3])
  have l3 := holds_trans l2 (holds_context c1_rule22 [5, 7, 2, -9] [])
  have r0 := holds_refl [-5, -5, -4, -3, -9, 2]
  have r1 := holds_trans r0 (holds_context c1_rule27 [] [-4, -3, -9, 2])
  have r2 := holds_trans r1 (holds_context c1_rule23 [5, 5] [-3, -9, 2])
  have r3 := holds_trans r2 (holds_context c1_rule22 [5, 5, 4] [-9, 2])
  have r4 := holds_trans r3 (holds_context c1_rule30 [5, 5] [-9, 2])
  have r5 := holds_trans r4 (holds_context c1_rule32 [5] [4, -9, 2])
  have r6 := holds_trans r5 (holds_context c1_rule32 [] [5, 4, -9, 2])
  have r7 := holds_trans r6 (holds_context c1_rule104 [] [-9, 2])
  have r8 := holds_trans r7 (holds_context c1_rule44 [3, 4, 5, 5] [])
  have r9 := holds_trans r8 (holds_context c1_rule108 [] [9])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r9)) (by central_nf)

theorem c1_rule182 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ)) [2, -9, 3, 2, 9] [3, -7, 5, 4] := by
  have h0 := (split [9, -2, -3, -2, 9] [3, 4, 5, 5, 5, 7] (rotate [9, 3, 4, 5, 5, 5, 7] [9, -2, -3, -2] (inverted source33)))
  have l0 := holds_refl [9, -2, -3, -2, 9]
  have l1 := holds_trans l0 (holds_context c1_rule21 [9] [-3, -2, 9])
  have l2 := holds_trans l1 (holds_context c1_rule45 [] [-3, -2, 9])
  have l3 := holds_trans l2 (holds_context c1_rule22 [2, -9] [-2, 9])
  have l4 := holds_trans l3 (holds_context c1_rule21 [2, -9, 3] [9])
  have r0 := holds_refl [-7, -5, -5, -5, -4, -3]
  have r1 := holds_trans r0 (holds_context c1_rule27 [-7] [-5, -4, -3])
  have r2 := holds_trans r1 (holds_context c1_rule8 [-7, 5] [-4, -3])
  have r3 := holds_trans r2 (holds_context c1_rule23 [-7, 5] [-3])
  have r4 := holds_trans r3 (holds_context c1_rule22 [-7, 5, 4] [])
  have r5 := holds_trans r4 (holds_context c1_rule30 [-7, 5] [])
  have r6 := holds_trans r5 (holds_context c1_rule32 [-7] [4])
  have r7 := holds_trans r6 (holds_context c1_rule33 [] [5, 4])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r7)) (by central_nf)

theorem c1_rule187 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s7) [-9, 3, 9, 3, 7, 7] [3, 3, 4, 4, 5, 5] := by
  have h0 := (split [-9, 3, 9, -7, -7, -3] [-5, -5, -4, -3, -4, -3] (rotate [-3] [-9, 3, 9, -7, -7, -3, -5, -5, -4, -3, -4] source14))
  have l0 := holds_refl [-9, 3, 9, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context c1_rule28 [-9, 3, 9] [-3])
  have l2 := holds_trans l1 (holds_context c1_rule22 [-9, 3, 9, 7, 7] [])
  have l3 := holds_trans l2 (holds_context c1_rule34 [-9, 3, 9, 7] [])
  have l4 := holds_trans l3 (holds_context c1_rule34 [-9, 3, 9] [7])
  have r0 := holds_refl [3, 4, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule30 [3] [4, 5, 5])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule192 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 7, -9, 3, 9, 3] [3, 3, 4, 5, 5, 4] := by
  have h0 := (split [-3, -5, -5, -4, -3, -4] [-3, -9, 3, 9, -7, -7] (rotate [-3, -9, 3, 9, -7, -7] [-3, -5, -5, -4, -3, -4] source14))
  have l0 := holds_refl [-3, -5, -5, -4, -3, -4]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-5, -5, -4, -3, -4])
  have l2 := holds_trans l1 (holds_context c1_rule27 [3] [-4, -3, -4])
  have l3 := holds_trans l2 (holds_context c1_rule23 [3, 5, 5] [-3, -4])
  have l4 := holds_trans l3 (holds_context c1_rule104 [] [-3, -4])
  have l5 := holds_trans l4 (holds_context c1_rule22 [3, 4, 5, 5] [-4])
  have l6 := holds_trans l5 (holds_context c1_rule32 [3, 4, 5] [-4])
  have l7 := holds_trans l6 (holds_context c1_rule32 [3, 4] [5, -4])
  have l8 := holds_trans l7 (holds_context c1_rule30 [3] [5, 5, -4])
  have l9 := holds_trans l8 (holds_context c1_rule23 [3, 3, 4, 5, 5] [])
  have r0 := holds_refl [7, 7, -9, -3, 9, 3]
  have r1 := holds_trans r0 (holds_context c1_rule22 [7, 7, -9] [9, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l9) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule195 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ)) [3, 5, 5, 7, 7, -9] [3, 3, 4, 4, -9, 3] := by
  have h0 := (split [-4, -3, -4, -3, -9, 3] [9, -7, -7, -3, -5, -5] (rotate [-3, -9, 3, 9, -7, -7, -3, -5, -5] [-4, -3, -4] source14))
  have l0 := holds_refl [-4, -3, -4, -3, -9, 3]
  have l1 := holds_trans l0 (holds_context c1_rule23 [] [-3, -4, -3, -9, 3])
  have l2 := holds_trans l1 (holds_context c1_rule22 [4] [-4, -3, -9, 3])
  have l3 := holds_trans l2 (holds_context c1_rule30 [] [-4, -3, -9, 3])
  have l4 := holds_trans l3 (holds_context c1_rule23 [3, 4] [-3, -9, 3])
  have l5 := holds_trans l4 (holds_context c1_rule22 [3, 4, 4] [-9, 3])
  have l6 := holds_trans l5 (holds_context c1_rule30 [3, 4] [-9, 3])
  have l7 := holds_trans l6 (holds_context c1_rule30 [3] [4, -9, 3])
  have r0 := holds_refl [5, 5, 3, 7, 7, -9]
  have r1 := holds_trans r0 (holds_context c1_rule32 [5] [7, 7, -9])
  have r2 := holds_trans r1 (holds_context c1_rule32 [] [5, 7, 7, -9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l7) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule196 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [3, 3, 4, -9, 3, 9] [3, -9, 6, 9, 6] := by
  have h0 := (split [-3, -4, -3, -9, 3, 9] [-7, -7, -3, -5, -5, -4] (rotate [-3, -9, 3, 9, -7, -7, -3, -5, -5, -4] [-3, -4] source14))
  have l0 := holds_refl [-3, -4, -3, -9, 3, 9]
  have l1 := holds_trans l0 (holds_context c1_rule22 [] [-4, -3, -9, 3, 9])
  have l2 := holds_trans l1 (holds_context c1_rule23 [3] [-3, -9, 3, 9])
  have l3 := holds_trans l2 (holds_context c1_rule22 [3, 4] [-9, 3, 9])
  have l4 := holds_trans l3 (holds_context c1_rule30 [3] [-9, 3, 9])
  have r0 := holds_refl [4, 5, 5, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c1_rule32 [4, 5] [7, 7])
  have r2 := holds_trans r1 (holds_context c1_rule32 [4] [5, 7, 7])
  have r3 := holds_trans r2 (holds_context c1_rule30 [] [5, 5, 7, 7])
  have r4 := holds_trans r3 (holds_context c1_rule141 [] [])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r4)) (by central_nf)

theorem c1_rule199 : Holds (normalizedRelatorError .i_r8) [2, 2] [] := by
  have h0 := c1_rule2
  have l0 := holds_refl [2, -2]
  have l1 := holds_trans l0 (holds_context c1_rule21 [2] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule200 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c1_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c1_rule22 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule201 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c1_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context c1_rule23 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule202 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c1_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context c1_rule24 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule203 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c1_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context c1_rule25 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule204 : Holds (normalizedRelatorError .i_s8) [10, 10] [] := by
  have h0 := c1_rule18
  have l0 := holds_refl [10, -10]
  have l1 := holds_trans l0 (holds_context c1_rule26 [10] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule205 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule27 [5] [])) (holds_context c1_rule8 [] [-5]))
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule206 : Holds (normalizedRelatorError .i_s5) [7, 7, 7] [-7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule28 [7] [])) (holds_context c1_rule12 [] [-7]))
  have l0 := holds_refl [7, 7, 7]
  have r0 := holds_refl [-7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule207 : Holds (normalizedRelatorError .i_s7) [9, 9, 9] [-9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule29 [9] [])) (holds_context c1_rule16 [] [-9]))
  have l0 := holds_refl [9, 9, 9]
  have r0 := holds_refl [-9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
