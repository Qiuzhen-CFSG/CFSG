module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.SourceWords

/-! Central word identities for the remaining normalized commutators, chunk 0.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule0 : Holds ((1 : C)) [1, -1] [] := by
  have h0 := (show Holds 1 [1, -1] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [1, -1]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2 : Holds ((1 : C)) [2, -2] [] := by
  have h0 := (show Holds 1 [2, -2] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [2, -2]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule4 : Holds ((1 : C)) [3, -3] [] := by
  have h0 := (show Holds 1 [3, -3] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [3, -3]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule6 : Holds ((1 : C)) [4, -4] [] := by
  have h0 := (show Holds 1 [4, -4] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [4, -4]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule8 : Holds ((1 : C)) [5, -5] [] := by
  have h0 := (show Holds 1 [5, -5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [5, -5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule9 : Holds ((1 : C)) [-5, 5] [] := by
  have h0 := (show Holds 1 [-5, 5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-5, 5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule10 : Holds ((1 : C)) [6, -6] [] := by
  have h0 := (show Holds 1 [6, -6] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [6, -6]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule12 : Holds ((1 : C)) [7, -7] [] := by
  have h0 := (show Holds 1 [7, -7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [7, -7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule13 : Holds ((1 : C)) [-7, 7] [] := by
  have h0 := (show Holds 1 [-7, 7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-7, 7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule14 : Holds ((1 : C)) [8, -8] [] := by
  have h0 := (show Holds 1 [8, -8] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [8, -8]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule16 : Holds ((1 : C)) [9, -9] [] := by
  have h0 := (show Holds 1 [9, -9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [9, -9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule17 : Holds ((1 : C)) [-9, 9] [] := by
  have h0 := (show Holds 1 [-9, 9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-9, 9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule18 : Holds ((1 : C)) [10, -10] [] := by
  have h0 := (show Holds 1 [10, -10] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [10, -10]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule20 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ)) [-1] [1] := by
  have h0 := (split [1] [1] (rotate [] [1, 1] source0))
  have l0 := holds_refl [1]
  have r0 := holds_refl [-1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule21 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ)) [-2] [2] := by
  have h0 := (split [2] [2] (rotate [] [2, 2] source1))
  have l0 := holds_refl [2]
  have r0 := holds_refl [-2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule22 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule23 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule24 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ)) [-6] [6] := by
  have h0 := (split [6] [6] (rotate [] [6, 6] source4))
  have l0 := holds_refl [6]
  have r0 := holds_refl [-6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule25 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule26 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ)) [-10] [10] := by
  have h0 := (split [10] [10] (rotate [] [10, 10] source6))
  have l0 := holds_refl [10]
  have r0 := holds_refl [-10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule27 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ)) [-5, -5] [5, 5] := by
  have h0 := (split [5, 5] [5, 5] (rotate [] [5, 5, 5, 5] source7))
  have l0 := holds_refl [5, 5]
  have r0 := holds_refl [-5, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule28 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ)) [-7, -7] [7, 7] := by
  have h0 := (split [7, 7] [7, 7] (rotate [] [7, 7, 7, 7] source8))
  have l0 := holds_refl [7, 7]
  have r0 := holds_refl [-7, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule29 : Holds ((normalizedRelatorError .i_s7) ^ (-1 : ℤ)) [-9, -9] [9, 9] := by
  have h0 := (split [9, 9] [9, 9] (rotate [] [9, 9, 9, 9] source9))
  have l0 := holds_refl [9, 9]
  have r0 := holds_refl [-9, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule30 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ)) [4, 3] [3, 4] := by
  have h0 := (split [-3, -4] [3, 4] (rotate [] [-3, -4, 3, 4] source10))
  have l0 := holds_refl [-3, -4]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [] [-4])
  have l2 := holds_trans l1 (holds_context rc22_rule23 [3] [])
  have r0 := holds_refl [-4, -3]
  have r1 := holds_trans r0 (holds_context rc22_rule23 [] [-3])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [4] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule31 : Holds (normalizedRelatorError .ii_s1_s3) [3, -5] [-5, 3] := by
  have h0 := (split [-3, -5] [3, 5] (rotate [] [-3, -5, 3, 5] source11))
  have l0 := holds_refl [-3, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [] [-5])
  have r0 := holds_refl [-5, -3]
  have r1 := holds_trans r0 (holds_context rc22_rule22 [-5] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule32 : Holds (normalizedRelatorError .ii_s1_s3) [3, 5] [5, 3] := by
  have h0 := (split [3, 5] [-3, -5] (rotate [-3, -5] [3, 5] source11))
  have l0 := holds_refl [3, 5]
  have r0 := holds_refl [5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule33 : Holds (normalizedRelatorError .ii_s1_s5) [3, -7] [-7, 3] := by
  have h0 := (split [-3, -7] [3, 7] (rotate [] [-3, -7, 3, 7] source12))
  have l0 := holds_refl [-3, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [] [-7])
  have r0 := holds_refl [-7, -3]
  have r1 := holds_trans r0 (holds_context rc22_rule22 [-7] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule34 : Holds (normalizedRelatorError .ii_s1_s5) [3, 7] [7, 3] := by
  have h0 := (split [3, 7] [-3, -7] (rotate [-3, -7] [3, 7] source12))
  have l0 := holds_refl [3, 7]
  have r0 := holds_refl [7, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule35 : Holds (normalizedRelatorError .iv_s2_s4) [4, 6] [6, 4] := by
  have h0 := (split [-4, -6] [4, 6] (rotate [] [-4, -6, 4, 6] source16))
  have l0 := holds_refl [-4, -6]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [] [-6])
  have l2 := holds_trans l1 (holds_context rc22_rule24 [4] [])
  have r0 := holds_refl [-6, -4]
  have r1 := holds_trans r0 (holds_context rc22_rule24 [] [-4])
  have r2 := holds_trans r1 (holds_context rc22_rule23 [6] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule36 : Holds ((normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 4] [4, 8] := by
  have h0 := (split [-4, -8] [4, 8] (rotate [] [-4, -8, 4, 8] source17))
  have l0 := holds_refl [-4, -8]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [] [-8])
  have l2 := holds_trans l1 (holds_context rc22_rule25 [4] [])
  have r0 := holds_refl [-8, -4]
  have r1 := holds_trans r0 (holds_context rc22_rule25 [] [-4])
  have r2 := holds_trans r1 (holds_context rc22_rule23 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule37 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2) [1, 4] [10, 1] := by
  have h0 := (split [1, 4] [1, -10] (rotate [] [1, 4, 1, -10] source26))
  have l0 := holds_refl [1, 4]
  have r0 := holds_refl [10, -1]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [10] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule38 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2) [4, 1] [1, 10] := by
  have h0 := (split [4, 1] [-10, 1] (rotate [1] [4, 1, -10] source26))
  have l0 := holds_refl [4, 1]
  have r0 := holds_refl [-1, 10]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [] [10])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule39 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [8, 1] [1, 6] := by
  have h0 := (split [1, 6] [1, -8] (rotate [] [1, 6, 1, -8] source27))
  have l0 := holds_refl [1, 6]
  have r0 := holds_refl [8, -1]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule40 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [1, 8] [6, 1] := by
  have h0 := (split [6, 1] [-8, 1] (rotate [1] [6, 1, -8] source27))
  have l0 := holds_refl [6, 1]
  have r0 := holds_refl [-1, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule41 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ)) [8, 2] [2, 4] := by
  have h0 := (split [2, 4] [2, -8] (rotate [] [2, 4, 2, -8] source31))
  have l0 := holds_refl [2, 4]
  have r0 := holds_refl [8, -2]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule42 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2) [4, 2] [2, 8] := by
  have h0 := (split [4, 2] [-8, 2] (rotate [2] [4, 2, -8] source31))
  have l0 := holds_refl [4, 2]
  have r0 := holds_refl [-2, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [] [8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule43 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ)) [6, 2] [2, 6] := by
  have h0 := (split [2, 6] [2, -6] (rotate [] [2, 6, 2, -6] source32))
  have l0 := holds_refl [2, 6]
  have r0 := holds_refl [6, -2]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule44 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ)) [-9, 2] [2, 9] := by
  have h0 := (split [2, 9] [2, 9] (rotate [] [2, 9, 2, 9] source34))
  have l0 := holds_refl [2, 9]
  have r0 := holds_refl [-9, -2]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [-9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule45 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7) [9, 2] [2, -9] := by
  have h0 := (split [9, 2] [9, 2] (rotate [2] [9, 2, 9] source34))
  have l0 := holds_refl [9, 2]
  have r0 := holds_refl [-2, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule46 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [9, 7, 2] [2, 5] := by
  have h0 := (split [2, 5] [2, -7, -9] (rotate [] [2, 5, 2, -7, -9] source35))
  have l0 := holds_refl [2, 5]
  have r0 := holds_refl [9, 7, -2]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [9, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
