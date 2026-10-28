module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step12

/-! Kernel-checked central word identities, chunk 13.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem equation_r5_158 : (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c5_rule46 [7, 1] [])) (holds_context c5_rule26 [] [-7, 1]))
  have l0 := holds_refl [7, 1, 3, -7, 1, -7]
  have l1 := holds_trans l0 (holds_context c5_rule49 [] [-7, 1, -7])
  have l2 := holds_trans l1 (holds_context c5_rule26 [1] [-7])
  have l3 := holds_trans l2 (holds_context c5_rule30 [] [3, 1, 3, -7])
  have l4 := holds_trans l3 (holds_context c5_rule47 [] [])
  have r0 := holds_refl [1, 3, 1, 3, -7, 1]
  have r1 := holds_trans r0 (holds_context c5_rule47 [1] [1])
  have r2 := holds_trans r1 (holds_context c5_rule30 [] [-7, 1, 3, 1])
  have r3 := holds_trans r2 (holds_context c5_rule27 [] [])
  have hh : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [1, -7, 1, 3] [1, -7, 1, 3] := holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem c6_rule0 : Holds ((1 : C)) [1, -1] [] := by
  have h0 := (show Holds 1 [1, -1] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [1, -1]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4 : Holds ((1 : C)) [3, -3] [] := by
  have h0 := (show Holds 1 [3, -3] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [3, -3]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule6 : Holds ((1 : C)) [4, -4] [] := by
  have h0 := (show Holds 1 [4, -4] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [4, -4]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule8 : Holds ((1 : C)) [5, -5] [] := by
  have h0 := (show Holds 1 [5, -5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [5, -5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule9 : Holds ((1 : C)) [-5, 5] [] := by
  have h0 := (show Holds 1 [-5, 5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-5, 5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule10 : Holds ((1 : C)) [6, -6] [] := by
  have h0 := (show Holds 1 [6, -6] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [6, -6]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule12 : Holds ((1 : C)) [7, -7] [] := by
  have h0 := (show Holds 1 [7, -7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [7, -7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule13 : Holds ((1 : C)) [-7, 7] [] := by
  have h0 := (show Holds 1 [-7, 7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-7, 7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule14 : Holds ((1 : C)) [8, -8] [] := by
  have h0 := (show Holds 1 [8, -8] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [8, -8]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule16 : Holds ((1 : C)) [9, -9] [] := by
  have h0 := (show Holds 1 [9, -9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [9, -9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule17 : Holds ((1 : C)) [-9, 9] [] := by
  have h0 := (show Holds 1 [-9, 9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-9, 9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule18 : Holds ((1 : C)) [10, -10] [] := by
  have h0 := (show Holds 1 [10, -10] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [10, -10]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule20 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ)) [-1] [1] := by
  have h0 := (split [1] [1] (rotate [] [1, 1] source0))
  have l0 := holds_refl [1]
  have r0 := holds_refl [-1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule21 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule22 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule23 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ)) [-6] [6] := by
  have h0 := (split [6] [6] (rotate [] [6, 6] source4))
  have l0 := holds_refl [6]
  have r0 := holds_refl [-6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule24 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule25 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ)) [-10] [10] := by
  have h0 := (split [10] [10] (rotate [] [10, 10] source6))
  have l0 := holds_refl [10]
  have r0 := holds_refl [-10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule26 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ)) [-5, -5] [5, 5] := by
  have h0 := (split [5, 5] [5, 5] (rotate [] [5, 5, 5, 5] source7))
  have l0 := holds_refl [5, 5]
  have r0 := holds_refl [-5, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule27 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ)) [-7, -7] [7, 7] := by
  have h0 := (split [7, 7] [7, 7] (rotate [] [7, 7, 7, 7] source8))
  have l0 := holds_refl [7, 7]
  have r0 := holds_refl [-7, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule28 : Holds ((normalizedRelatorError .i_s7) ^ (-1 : ℤ)) [-9, -9] [9, 9] := by
  have h0 := (split [9, 9] [9, 9] (rotate [] [9, 9, 9, 9] source9))
  have l0 := holds_refl [9, 9]
  have r0 := holds_refl [-9, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule29 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ)) [4, 3] [3, 4] := by
  have h0 := (split [-3, -4] [3, 4] (rotate [] [-3, -4, 3, 4] source10))
  have l0 := holds_refl [-3, -4]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-4])
  have l2 := holds_trans l1 (holds_context c6_rule22 [3] [])
  have r0 := holds_refl [-4, -3]
  have r1 := holds_trans r0 (holds_context c6_rule22 [] [-3])
  have r2 := holds_trans r1 (holds_context c6_rule21 [4] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c6_rule30 : Holds (normalizedRelatorError .ii_s1_s3) [3, -5] [-5, 3] := by
  have h0 := (split [-3, -5] [3, 5] (rotate [] [-3, -5, 3, 5] source11))
  have l0 := holds_refl [-3, -5]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-5])
  have r0 := holds_refl [-5, -3]
  have r1 := holds_trans r0 (holds_context c6_rule21 [-5] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule31 : Holds (normalizedRelatorError .ii_s1_s3) [3, 5] [5, 3] := by
  have h0 := (split [3, 5] [-3, -5] (rotate [-3, -5] [3, 5] source11))
  have l0 := holds_refl [3, 5]
  have r0 := holds_refl [5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule32 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 3] [3, -7] := by
  have h0 := (split [-3, -7] [3, 7] (rotate [] [-3, -7, 3, 7] source12))
  have l0 := holds_refl [-3, -7]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-7])
  have r0 := holds_refl [-7, -3]
  have r1 := holds_trans r0 (holds_context c6_rule21 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule33 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, 3] [3, 7] := by
  have h0 := (split [3, 7] [-3, -7] (rotate [-3, -7] [3, 7] source12))
  have l0 := holds_refl [3, 7]
  have r0 := holds_refl [7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule34 : Holds (normalizedRelatorError .iv_s2_s4) [4, 6] [6, 4] := by
  have h0 := (split [-4, -6] [4, 6] (rotate [] [-4, -6, 4, 6] source16))
  have l0 := holds_refl [-4, -6]
  have l1 := holds_trans l0 (holds_context c6_rule22 [] [-6])
  have l2 := holds_trans l1 (holds_context c6_rule23 [4] [])
  have r0 := holds_refl [-6, -4]
  have r1 := holds_trans r0 (holds_context c6_rule23 [] [-4])
  have r2 := holds_trans r1 (holds_context c6_rule22 [6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule35 : Holds (normalizedRelatorError .iv_s2_s6) [4, 8] [8, 4] := by
  have h0 := (split [-4, -8] [4, 8] (rotate [] [-4, -8, 4, 8] source17))
  have l0 := holds_refl [-4, -8]
  have l1 := holds_trans l0 (holds_context c6_rule22 [] [-8])
  have l2 := holds_trans l1 (holds_context c6_rule24 [4] [])
  have r0 := holds_refl [-8, -4]
  have r1 := holds_trans r0 (holds_context c6_rule24 [] [-4])
  have r2 := holds_trans r1 (holds_context c6_rule22 [8] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule36 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ)) [10, 1] [1, 4] := by
  have h0 := (split [1, 4] [1, -10] (rotate [] [1, 4, 1, -10] source26))
  have l0 := holds_refl [1, 4]
  have r0 := holds_refl [10, -1]
  have r1 := holds_trans r0 (holds_context c6_rule20 [10] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule37 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2) [4, 1] [1, 10] := by
  have h0 := (split [4, 1] [-10, 1] (rotate [1] [4, 1, -10] source26))
  have l0 := holds_refl [4, 1]
  have r0 := holds_refl [-1, 10]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [10])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule38 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [8, 1] [1, 6] := by
  have h0 := (split [1, 6] [1, -8] (rotate [] [1, 6, 1, -8] source27))
  have l0 := holds_refl [1, 6]
  have r0 := holds_refl [8, -1]
  have r1 := holds_trans r0 (holds_context c6_rule20 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule39 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s4) [6, 1] [1, 8] := by
  have h0 := (split [6, 1] [-8, 1] (rotate [1] [6, 1, -8] source27))
  have l0 := holds_refl [6, 1]
  have r0 := holds_refl [-1, 8]
  have r1 := holds_trans r0 (holds_context c6_rule20 [] [8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule40 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .iv_s2_s8) [4, 10, 4] [6, 8, 10] := by
  have h0 := (split [-4, -10, 4] [10, -8, -6] (rotate [] [-4, -10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-4, -10, 4]
  have l1 := holds_trans l0 (holds_context c6_rule22 [] [-10, 4])
  have l2 := holds_trans l1 (holds_context c6_rule25 [4] [4])
  have r0 := holds_refl [6, 8, -10]
  have r1 := holds_trans r0 (holds_context c6_rule25 [6, 8] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule42 : Holds (normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s8) [4, 10, 8] [10, 6, 4] := by
  have h0 := (split [4, 10, -8] [-6, -4, -10] (rotate [-4, -10] [4, 10, -8, -6] source18))
  have l0 := holds_refl [4, 10, -8]
  have l1 := holds_trans l0 (holds_context c6_rule24 [4, 10] [])
  have r0 := holds_refl [10, 4, 6]
  have r1 := holds_trans r0 (holds_context c6_rule34 [10] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule43 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [10, 8, 6] [6, 8, 10] := by
  have h0 := (split [10, -8, -6] [-4, -10, 4] (rotate [-4, -10, 4] [10, -8, -6] source18))
  have l0 := holds_refl [10, -8, -6]
  have l1 := holds_trans l0 (holds_context c6_rule24 [10] [-6])
  have l2 := holds_trans l1 (holds_context c6_rule23 [10, 8] [])
  have r0 := holds_refl [-4, 10, 4]
  have r1 := holds_trans r0 (holds_context c6_rule22 [] [10, 4])
  have r2 := holds_trans r1 (holds_context c6_rule40 [] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule46 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 4, 5, 5] [3, 8, 3, 8] := by
  have h0 := (split [-3, -8, 3, 8] [-5, -5, -4, -3] (rotate [] [-3, -8, 3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [-3, -8, 3, 8]
  have l1 := holds_trans l0 (holds_context c6_rule21 [] [-8, 3, 8])
  have l2 := holds_trans l1 (holds_context c6_rule24 [3] [3, 8])
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule48 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 3, 4] [3, 8, 5, 5] := by
  have h0 := (split [3, 8, -5, -5] [-4, -3, -3, -8] (rotate [-3, -8] [3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [3, 8, -5, -5]
  have l1 := holds_trans l0 (holds_context c6_rule26 [3, 8] [])
  have r0 := holds_refl [8, 3, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule50 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 8, 3] [5, 5, 3, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-3, -8, 3, 8] (rotate [-3, -8, 3, 8] [-5, -5, -4, -3] source13))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c6_rule26 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c6_rule22 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c6_rule21 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c6_rule29 [5, 5] [])
  have r0 := holds_refl [-8, -3, 8, 3]
  have r1 := holds_trans r0 (holds_context c6_rule24 [] [-3, 8, 3])
  have r2 := holds_trans r1 (holds_context c6_rule21 [8] [8, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem c6_rule51 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [-5, 3, 3, 4] [5, 8, 3, 8] := by
  have h0 := (split [-5, -4, -3, -3] [-8, 3, 8, -5] (rotate [-3, -8, 3, 8, -5] [-5, -4, -3] source13))
  have l0 := holds_refl [-5, -4, -3, -3]
  have l1 := holds_trans l0 (holds_context c6_rule22 [-5] [-3, -3])
  have l2 := holds_trans l1 (holds_context c6_rule21 [-5, 4] [-3])
  have l3 := holds_trans l2 (holds_context c6_rule29 [-5] [-3])
  have l4 := holds_trans l3 (holds_context c6_rule21 [-5, 3, 4] [])
  have l5 := holds_trans l4 (holds_context c6_rule29 [-5, 3] [])
  have r0 := holds_refl [5, -8, -3, 8]
  have r1 := holds_trans r0 (holds_context c6_rule24 [5] [-3, 8])
  have r2 := holds_trans r1 (holds_context c6_rule21 [5, 8] [8])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r2)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
