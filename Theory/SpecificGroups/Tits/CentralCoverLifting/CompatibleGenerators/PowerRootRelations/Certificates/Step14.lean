module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step13

/-! Kernel-checked central word identities, chunk 14.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule54 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 4] [6, 3, 7, 7] := by
  have h0 := (split [-9, -4, 9, 4] [-7, -7, -3, -6] (rotate [] [-9, -4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-9, -4, 9, 4]
  have l1 := holds_trans l0 (holds_context c6_rule22 [-9] [9, 4])
  have r0 := holds_refl [6, 3, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule55 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .iv_s7_s2) [4, 9, 4, -7] [9, 6, 3, 7] := by
  have h0 := (split [-4, 9, 4, -7] [-7, -3, -6, -9] (rotate [-9] [-4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-4, 9, 4, -7]
  have l1 := holds_trans l0 (holds_context c6_rule22 [] [9, 4, -7])
  have r0 := holds_refl [9, 6, 3, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule56 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, 9, 6, 3] [9, 4, 7, 7] := by
  have h0 := (split [9, 4, -7, -7] [-3, -6, -9, -4] (rotate [-9, -4] [9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [9, 4, -7, -7]
  have l1 := holds_trans l0 (holds_context c6_rule27 [9, 4] [])
  have r0 := holds_refl [4, 9, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule58 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, -9, 4, 9] [3, 7, 7, 6] := by
  have h0 := (split [-7, -7, -3, -6] [-9, -4, 9, 4] (rotate [-9, -4, 9, 4] [-7, -7, -3, -6] source19))
  have l0 := holds_refl [-7, -7, -3, -6]
  have l1 := holds_trans l0 (holds_context c6_rule27 [] [-3, -6])
  have l2 := holds_trans l1 (holds_context c6_rule21 [7, 7] [-6])
  have l3 := holds_trans l2 (holds_context c6_rule33 [7] [-6])
  have l4 := holds_trans l3 (holds_context c6_rule33 [] [7, -6])
  have l5 := holds_trans l4 (holds_context c6_rule23 [3, 7, 7] [])
  have r0 := holds_refl [-4, -9, 4, 9]
  have r1 := holds_trans r0 (holds_context c6_rule22 [] [-9, 4, 9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule60 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [7, 7, 4, -9] [3, 6, -9, 4] := by
  have h0 := (split [-3, -6, -9, -4] [9, 4, -7, -7] (rotate [-9, -4, 9, 4, -7, -7] [-3, -6] source19))
  have l0 := holds_refl [-3, -6, -9, -4]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-6, -9, -4])
  have l2 := holds_trans l1 (holds_context c6_rule23 [3] [-9, -4])
  have l3 := holds_trans l2 (holds_context c6_rule22 [3, 6, -9] [])
  have r0 := holds_refl [7, 7, -4, -9]
  have r1 := holds_trans r0 (holds_context c6_rule22 [7, 7] [-9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule64 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 5, 5] [6, 3, 7, 4] := by
  have h0 := (split [7, 6, -5, -5] [-4, -3, -7, -6] (rotate [-7, -6] [7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [7, 6, -5, -5]
  have l1 := holds_trans l0 (holds_context c6_rule26 [7, 6] [])
  have r0 := holds_refl [6, 7, 3, 4]
  have r1 := holds_trans r0 (holds_context c6_rule33 [6] [4])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule65 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, 3, 7] [6, 5, 5, 4] := by
  have h0 := (split [6, -5, -5, -4] [-3, -7, -6, 7] (rotate [-7, -6, 7] [6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c6_rule26 [6] [-4])
  have l2 := holds_trans l1 (holds_context c6_rule22 [6, 5, 5] [])
  have r0 := holds_refl [-7, 6, 7, 3]
  have r1 := holds_trans r0 (holds_context c6_rule33 [-7, 6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule66 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, 6, 7] [5, 5, 3, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-7, -6, 7, 6] (rotate [-7, -6, 7, 6] [-5, -5, -4, -3] source22))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c6_rule26 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c6_rule22 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c6_rule21 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c6_rule29 [5, 5] [])
  have r0 := holds_refl [-6, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c6_rule23 [] [-7, 6, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule69 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 5, 6] [3, -7, 6, 7] := by
  have h0 := (split [-3, -7, -6, 7] [6, -5, -5, -4] (rotate [-7, -6, 7, 6, -5, -5, -4] [-3] source22))
  have l0 := holds_refl [-3, -7, -6, 7]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-7, -6, 7])
  have l2 := holds_trans l1 (holds_context c6_rule23 [3, -7] [7])
  have r0 := holds_refl [4, 5, 5, -6]
  have r1 := holds_trans r0 (holds_context c6_rule23 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule70 : Holds ((normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [3, 1, 3, 1] [1, 7, 1, -7] := by
  have h0 := (split [1, 7, 1, -7] [-1, -3, -1, -3] (rotate [] [1, 7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, 7, 1, -7]
  have r0 := holds_refl [3, 1, 3, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule71 : Holds (normalizedRelatorError .vii_s5) [7, 1, -7, 1] [1, 3, 1, 3] := by
  have h0 := (split [7, 1, -7, -1] [-3, -1, -3, 1] (rotate [1] [7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [7, 1, -7, -1]
  have l1 := holds_trans l0 (holds_context c6_rule20 [7, 1, -7] [])
  have r0 := holds_refl [-1, 3, 1, 3]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [3, 1, 3])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule72 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [-7, 1, 3, 1] [1, -7, 1, 3] := by
  have h0 := (split [1, -7, -1, -3] [-1, -3, 1, 7] (rotate [1, 7] [1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, -7, -1, -3]
  have l1 := holds_trans l0 (holds_context c6_rule20 [1, -7] [-3])
  have l2 := holds_trans l1 (holds_context c6_rule21 [1, -7, 1] [])
  have r0 := holds_refl [-7, -1, 3, 1]
  have r1 := holds_trans r0 (holds_context c6_rule20 [-7] [3, 1])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule74 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [9, 9, 3, 8, 3, 8] [3, 10, 3, 10, 3] := by
  have h0 := (split [-3, -10, 3, 10, -3] [-5, -5, -4, -3, -9, -9] (rotate [] [-3, -10, 3, 10, -3, -5, -5, -4, -3, -9, -9] source15))
  have l0 := holds_refl [-3, -10, 3, 10, -3]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-10, 3, 10, -3])
  have l2 := holds_trans l1 (holds_context c6_rule25 [3] [3, 10, -3])
  have l3 := holds_trans l2 (holds_context c6_rule21 [3, 10, 3, 10] [])
  have r0 := holds_refl [9, 9, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c6_rule46 [9, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule83 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [5, 5, 3, 3, 4, 10] [9, 9, 3, 10, 3] := by
  have h0 := (split [-9, -9, -3, -10, 3] [10, -3, -5, -5, -4, -3] (rotate [-3, -10, 3, 10, -3, -5, -5, -4, -3] [-9, -9] source15))
  have l0 := holds_refl [-9, -9, -3, -10, 3]
  have l1 := holds_trans l0 (holds_context c6_rule28 [] [-3, -10, 3])
  have l2 := holds_trans l1 (holds_context c6_rule21 [9, 9] [-10, 3])
  have l3 := holds_trans l2 (holds_context c6_rule25 [9, 9, 3] [3])
  have r0 := holds_refl [3, 4, 5, 5, 3, -10]
  have r1 := holds_trans r0 (holds_context c6_rule46 [] [3, -10])
  have r2 := holds_trans r1 (holds_context c6_rule50 [3] [-10])
  have r3 := holds_trans r2 (holds_context c6_rule31 [] [5, 3, 4, -10])
  have r4 := holds_trans r3 (holds_context c6_rule31 [5] [3, 4, -10])
  have r5 := holds_trans r4 (holds_context c6_rule25 [5, 5, 3, 3, 4] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r5))) (by central_nf)

theorem c6_rule84 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ)) [9, 5, 5, 3, 3, 4] [-9, 3, 10, 3, 10] := by
  have h0 := (split [-9, -3, -10, 3, 10] [-3, -5, -5, -4, -3, -9] (rotate [-3, -10, 3, 10, -3, -5, -5, -4, -3, -9] [-9] source15))
  have l0 := holds_refl [-9, -3, -10, 3, 10]
  have l1 := holds_trans l0 (holds_context c6_rule21 [-9] [-10, 3, 10])
  have l2 := holds_trans l1 (holds_context c6_rule25 [-9, 3] [3, 10])
  have r0 := holds_refl [9, 3, 4, 5, 5, 3]
  have r1 := holds_trans r0 (holds_context c6_rule46 [9] [3])
  have r2 := holds_trans r1 (holds_context c6_rule50 [9, 3] [])
  have r3 := holds_trans r2 (holds_context c6_rule31 [9] [5, 3, 4])
  have r4 := holds_trans r3 (holds_context c6_rule31 [9, 5] [3, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r4))) (by central_nf)

theorem c6_rule97 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [-9, 3, 10, 3, 10] [6, 9, 6, 7, 7] := by
  have h0 := (split [-6, 9, 6, -7, -7] [-3, -5, -5, -4, -3, -9] (rotate [-9] [-6, 9, 6, -7, -7, -3, -5, -5, -4, -3] source20))
  have l0 := holds_refl [-6, 9, 6, -7, -7]
  have l1 := holds_trans l0 (holds_context c6_rule23 [] [9, 6, -7, -7])
  have l2 := holds_trans l1 (holds_context c6_rule27 [6, 9, 6] [])
  have r0 := holds_refl [9, 3, 4, 5, 5, 3]
  have r1 := holds_trans r0 (holds_context c6_rule46 [9] [3])
  have r2 := holds_trans r1 (holds_context c6_rule50 [9, 3] [])
  have r3 := holds_trans r2 (holds_context c6_rule31 [9] [5, 3, 4])
  have r4 := holds_trans r3 (holds_context c6_rule31 [9, 5] [3, 4])
  have r5 := holds_trans r4 (holds_context c6_rule84 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r5))) (by central_nf)

theorem c6_rule114 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4) [3, 7, 7, 5, 5, 4] [6, -9, 6, 9, 3] := by
  have h0 := (split [-6, -9, 6, 9, 3] [4, 5, 5, 3, 7, 7] (rotate [3, 4, 5, 5, 3, 7, 7] [-6, -9, 6, 9] (inverted source20)))
  have l0 := holds_refl [-6, -9, 6, 9, 3]
  have l1 := holds_trans l0 (holds_context c6_rule23 [] [-9, 6, 9, 3])
  have r0 := holds_refl [-7, -7, -3, -5, -5, -4]
  have r1 := holds_trans r0 (holds_context c6_rule27 [] [-3, -5, -5, -4])
  have r2 := holds_trans r1 (holds_context c6_rule21 [7, 7] [-5, -5, -4])
  have r3 := holds_trans r2 (holds_context c6_rule33 [7] [-5, -5, -4])
  have r4 := holds_trans r3 (holds_context c6_rule33 [] [7, -5, -5, -4])
  have r5 := holds_trans r4 (holds_context c6_rule26 [3, 7, 7] [-4])
  have r6 := holds_trans r5 (holds_context c6_rule22 [3, 7, 7, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r6))) (by central_nf)

theorem c6_rule126 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 4, -5, -7, 5] [3, -7, 6] := by
  have h0 := (split [-3, -4, -5, -7, 5] [7, -6, -5, -5, -4] (rotate [-5, -7, 5, 7, -6, -5, -5, -4] [-3, -4] source21))
  have l0 := holds_refl [-3, -4, -5, -7, 5]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-4, -5, -7, 5])
  have l2 := holds_trans l1 (holds_context c6_rule22 [3] [-5, -7, 5])
  have r0 := holds_refl [4, 5, 5, 6, -7]
  have r1 := holds_trans r0 (holds_context c6_rule69 [] [-7])
  have r2 := holds_trans r1 (holds_context c6_rule12 [3, -7, 6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule128 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1) [1, 7, 1, 3, -7] [1, 1, 7, 1, -7] := by
  have h0 := (split [3, 1, 3, 1, 3] [1, 3, 1, 3, 1] (rotate [] [3, 1, 3, 1, 3, 1, 3, 1, 3, 1] source24))
  have l0 := holds_refl [3, 1, 3, 1, 3]
  have l1 := holds_trans l0 (holds_context c6_rule70 [] [3])
  have l2 := holds_trans l1 (holds_context c6_rule32 [1, 7, 1] [])
  have r0 := holds_refl [-1, -3, -1, -3, -1]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [-3, -1, -3, -1])
  have r2 := holds_trans r1 (holds_context c6_rule21 [1] [-1, -3, -1])
  have r3 := holds_trans r2 (holds_context c6_rule20 [1, 3] [-3, -1])
  have r4 := holds_trans r3 (holds_context c6_rule21 [1, 3, 1] [-1])
  have r5 := holds_trans r4 (holds_context c6_rule20 [1, 3, 1, 3] [])
  have r6 := holds_trans r5 (holds_context c6_rule70 [1] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r6)) (by central_nf)

theorem c6_rule133 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4) [-9, 3, 9, 3, 3, 4] [6, -9, 6, 9, 3] := by
  have h0 := (split [-7, -7, -3, -5, -5, -4] [-3, -4, -3, -9, 3, 9] (rotate [-3, -9, 3, 9] [-7, -7, -3, -5, -5, -4, -3, -4] source14))
  have l0 := holds_refl [-7, -7, -3, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context c6_rule27 [] [-3, -5, -5, -4])
  have l2 := holds_trans l1 (holds_context c6_rule21 [7, 7] [-5, -5, -4])
  have l3 := holds_trans l2 (holds_context c6_rule33 [7] [-5, -5, -4])
  have l4 := holds_trans l3 (holds_context c6_rule33 [] [7, -5, -5, -4])
  have l5 := holds_trans l4 (holds_context c6_rule26 [3, 7, 7] [-4])
  have l6 := holds_trans l5 (holds_context c6_rule22 [3, 7, 7, 5, 5] [])
  have l7 := holds_trans l6 (holds_context c6_rule114 [] [])
  have r0 := holds_refl [-9, -3, 9, 3, 4, 3]
  have r1 := holds_trans r0 (holds_context c6_rule21 [-9] [9, 3, 4, 3])
  have r2 := holds_trans r1 (holds_context c6_rule29 [-9, 3, 9, 3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l7) (holds_trans h0 r2))) (by central_nf)

theorem c6_rule144 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ)) [1, -5, 1, 1, 7, 1, -7] [-9, -7, 5, 3, 4] := by
  have h0 := (split [-9, -7, -5, -5, -5, -4, -3] [-1, -3, -1, -3, 1, 5, 1] (rotate [1, 5, 1] [-9, -7, -5, -5, -5, -4, -3, -1, -3, -1, -3] source29))
  have l0 := holds_refl [-9, -7, -5, -5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c6_rule26 [-9, -7] [-5, -4, -3])
  have l2 := holds_trans l1 (holds_context c6_rule8 [-9, -7, 5] [-4, -3])
  have l3 := holds_trans l2 (holds_context c6_rule22 [-9, -7, 5] [-3])
  have l4 := holds_trans l3 (holds_context c6_rule21 [-9, -7, 5, 4] [])
  have l5 := holds_trans l4 (holds_context c6_rule29 [-9, -7, 5] [])
  have r0 := holds_refl [-1, -5, -1, 3, 1, 3, 1]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [-5, -1, 3, 1, 3, 1])
  have r2 := holds_trans r1 (holds_context c6_rule20 [1, -5] [3, 1, 3, 1])
  have r3 := holds_trans r2 (holds_context c6_rule70 [1, -5, 1] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r3))) (by central_nf)

theorem c6_rule161 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [1, 5, 5, 3, 1, 10, 9] [-9, -7, 5, 3, 4] := by
  have h0 := (split [-9, -7, -5, -5, -5, -4, -3] [-9, 1, 3, 4, 5, 5, 1] (rotate [1, 3, 4, 5, 5, 1] [-9, -7, -5, -5, -5, -4, -3, -9] source30))
  have l0 := holds_refl [-9, -7, -5, -5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c6_rule26 [-9, -7] [-5, -4, -3])
  have l2 := holds_trans l1 (holds_context c6_rule8 [-9, -7, 5] [-4, -3])
  have l3 := holds_trans l2 (holds_context c6_rule22 [-9, -7, 5] [-3])
  have l4 := holds_trans l3 (holds_context c6_rule21 [-9, -7, 5, 4] [])
  have l5 := holds_trans l4 (holds_context c6_rule29 [-9, -7, 5] [])
  have r0 := holds_refl [-1, -5, -5, -4, -3, -1, 9]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [-5, -5, -4, -3, -1, 9])
  have r2 := holds_trans r1 (holds_context c6_rule26 [1] [-4, -3, -1, 9])
  have r3 := holds_trans r2 (holds_context c6_rule22 [1, 5, 5] [-3, -1, 9])
  have r4 := holds_trans r3 (holds_context c6_rule21 [1, 5, 5, 4] [-1, 9])
  have r5 := holds_trans r4 (holds_context c6_rule29 [1, 5, 5] [-1, 9])
  have r6 := holds_trans r5 (holds_context c6_rule20 [1, 5, 5, 3, 4] [9])
  have r7 := holds_trans r6 (holds_context c6_rule37 [1, 5, 5, 3] [9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r7))) (by central_nf)

theorem c6_rule169 : Holds (normalizedRelatorError .i_r1) [1, 1] [] := by
  have h0 := c6_rule0
  have l0 := holds_refl [1, -1]
  have l1 := holds_trans l0 (holds_context c6_rule20 [1] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule170 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c6_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c6_rule21 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule171 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c6_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context c6_rule22 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule172 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c6_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context c6_rule23 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule173 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c6_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context c6_rule24 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule174 : Holds (normalizedRelatorError .i_s8) [10, 10] [] := by
  have h0 := c6_rule18
  have l0 := holds_refl [10, -10]
  have l1 := holds_trans l0 (holds_context c6_rule25 [10] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule175 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule26 [5] [])) (holds_context c6_rule8 [] [-5]))
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule176 : Holds (normalizedRelatorError .i_s5) [7, 7, 7] [-7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule27 [7] [])) (holds_context c6_rule12 [] [-7]))
  have l0 := holds_refl [7, 7, 7]
  have r0 := holds_refl [-7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule177 : Holds (normalizedRelatorError .i_s7) [9, 9, 9] [-9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule28 [9] [])) (holds_context c6_rule16 [] [-9]))
  have l0 := holds_refl [9, 9, 9]
  have r0 := holds_refl [-9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule179 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [4, 5, 3] [3, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule31 [4] [])) (holds_context c6_rule29 [] [5]))
  have l0 := holds_refl [4, 5, 3]
  have r0 := holds_refl [3, 4, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule180 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, -5, 3] [3, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule32 [] [-5])) (holds_context c6_rule30 [-7] []))
  have l0 := holds_refl [3, -7, -5]
  have r0 := holds_refl [-7, -5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule181 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 5, 3] [3, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule32 [] [5])) (holds_context c6_rule31 [-7] []))
  have l0 := holds_refl [3, -7, 5]
  have r0 := holds_refl [-7, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule182 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, -5, 3] [3, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule33 [] [-5])) (holds_context c6_rule30 [7] []))
  have l0 := holds_refl [3, 7, -5]
  have r0 := holds_refl [7, -5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule183 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, 5, 3] [3, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule33 [] [5])) (holds_context c6_rule31 [7] []))
  have l0 := holds_refl [3, 7, 5]
  have r0 := holds_refl [7, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule184 : Holds (normalizedRelatorError .iv_s2_s6) [1, 10, 6] [1, 6, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule38 [4] [])) (holds_context c6_rule35 [] [1]))
  have l0 := holds_refl [4, 1, 6]
  have l1 := holds_trans l0 (holds_context c6_rule37 [] [6])
  have r0 := holds_refl [8, 4, 1]
  have r1 := holds_trans r0 (holds_context c6_rule37 [8] [])
  have r2 := holds_trans r1 (holds_context c6_rule38 [] [10])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule192 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s4) ^ (-2 : ℤ)) [1, 8, 4, 10] [1, 6, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule42 [] [1])) (holds_context c6_rule38 [4, 10] []))
  have l0 := holds_refl [10, 6, 4, 1]
  have l1 := holds_trans l0 (holds_context c6_rule37 [10, 6] [])
  have l2 := holds_trans l1 (holds_context c6_rule39 [10] [10])
  have l3 := holds_trans l2 (holds_context c6_rule36 [] [8, 10])
  have l4 := holds_trans l3 (holds_context c6_rule35 [1] [10])
  have r0 := holds_refl [4, 10, 1, 6]
  have r1 := holds_trans r0 (holds_context c6_rule36 [4] [6])
  have r2 := holds_trans r1 (holds_context c6_rule37 [] [4, 6])
  have r3 := holds_trans r2 (holds_context c6_rule34 [1, 10] [])
  have r4 := holds_trans r3 (holds_context c6_rule184 [] [4])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r4)) (by central_nf)

theorem c6_rule193 : Holds (normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [6, 8, 4, 10] [10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule43 [4] [])) (holds_context c6_rule42 [] [6]))
  have l0 := holds_refl [4, 6, 8, 10]
  have l1 := holds_trans l0 (holds_context c6_rule34 [] [8, 10])
  have l2 := holds_trans l1 (holds_context c6_rule35 [6] [10])
  have r0 := holds_refl [10, 6, 4, 6]
  have r1 := holds_trans r0 (holds_context c6_rule34 [10, 6] [])
  have r2 := holds_trans r1 (holds_context c6_rule172 [10] [4])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule194 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [8, 4, 10] [6, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule193 [6] [])) (holds_context c6_rule172 [] [8, 4, 10]))
  have l0 := holds_refl [6, 10, 4]
  have r0 := holds_refl [8, 4, 10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
