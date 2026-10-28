module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.FourSeedReduction

/-! Additional kernel-checked central word identities, chunk 0.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p20_rule8 : Holds ((1 : C)) [5, -5] [] := by
  have h0 := (show Holds 1 [5, -5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [5, -5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule9 : Holds ((1 : C)) [-5, 5] [] := by
  have h0 := (show Holds 1 [-5, 5] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-5, 5]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule12 : Holds ((1 : C)) [7, -7] [] := by
  have h0 := (show Holds 1 [7, -7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [7, -7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule13 : Holds ((1 : C)) [-7, 7] [] := by
  have h0 := (show Holds 1 [-7, 7] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-7, 7]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule17 : Holds ((1 : C)) [-9, 9] [] := by
  have h0 := (show Holds 1 [-9, 9] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [-9, 9]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule20 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ)) [-1] [1] := by
  have h0 := (split [1] [1] (rotate [] [1, 1] source0))
  have l0 := holds_refl [1]
  have r0 := holds_refl [-1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule21 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ)) [-2] [2] := by
  have h0 := (split [2] [2] (rotate [] [2, 2] source1))
  have l0 := holds_refl [2]
  have r0 := holds_refl [-2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule22 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ)) [-3] [3] := by
  have h0 := (split [3] [3] (rotate [] [3, 3] source2))
  have l0 := holds_refl [3]
  have r0 := holds_refl [-3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule23 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ)) [-4] [4] := by
  have h0 := (split [4] [4] (rotate [] [4, 4] source3))
  have l0 := holds_refl [4]
  have r0 := holds_refl [-4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule24 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ)) [-6] [6] := by
  have h0 := (split [6] [6] (rotate [] [6, 6] source4))
  have l0 := holds_refl [6]
  have r0 := holds_refl [-6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule25 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule26 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ)) [-10] [10] := by
  have h0 := (split [10] [10] (rotate [] [10, 10] source6))
  have l0 := holds_refl [10]
  have r0 := holds_refl [-10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule28 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ)) [-7, -7] [7, 7] := by
  have h0 := (split [7, 7] [7, 7] (rotate [] [7, 7, 7, 7] source8))
  have l0 := holds_refl [7, 7]
  have r0 := holds_refl [-7, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule30 : Holds (normalizedRelatorError .ii_s1_s2) [3, 4] [4, 3] := by
  have h0 := (split [-3, -4] [3, 4] (rotate [] [-3, -4, 3, 4] source10))
  have l0 := holds_refl [-3, -4]
  have l1 := holds_trans l0 (holds_context p20_rule22 [] [-4])
  have l2 := holds_trans l1 (holds_context p20_rule23 [3] [])
  have r0 := holds_refl [-4, -3]
  have r1 := holds_trans r0 (holds_context p20_rule23 [] [-3])
  have r2 := holds_trans r1 (holds_context p20_rule22 [4] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem p20_rule31 : Holds (normalizedRelatorError .ii_s1_s3) [3, -5] [-5, 3] := by
  have h0 := (split [-3, -5] [3, 5] (rotate [] [-3, -5, 3, 5] source11))
  have l0 := holds_refl [-3, -5]
  have l1 := holds_trans l0 (holds_context p20_rule22 [] [-5])
  have r0 := holds_refl [-5, -3]
  have r1 := holds_trans r0 (holds_context p20_rule22 [-5] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem p20_rule32 : Holds (normalizedRelatorError .ii_s1_s3) [3, 5] [5, 3] := by
  have h0 := (split [3, 5] [-3, -5] (rotate [-3, -5] [3, 5] source11))
  have l0 := holds_refl [3, 5]
  have r0 := holds_refl [5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule33 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-7, 3] [3, -7] := by
  have h0 := (split [-3, -7] [3, 7] (rotate [] [-3, -7, 3, 7] source12))
  have l0 := holds_refl [-3, -7]
  have l1 := holds_trans l0 (holds_context p20_rule22 [] [-7])
  have r0 := holds_refl [-7, -3]
  have r1 := holds_trans r0 (holds_context p20_rule22 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule34 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, 3] [3, 7] := by
  have h0 := (split [3, 7] [-3, -7] (rotate [-3, -7] [3, 7] source12))
  have l0 := holds_refl [3, 7]
  have r0 := holds_refl [7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule35 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [6, 4] [4, 6] := by
  have h0 := (split [-4, -6] [4, 6] (rotate [] [-4, -6, 4, 6] source16))
  have l0 := holds_refl [-4, -6]
  have l1 := holds_trans l0 (holds_context p20_rule23 [] [-6])
  have l2 := holds_trans l1 (holds_context p20_rule24 [4] [])
  have r0 := holds_refl [-6, -4]
  have r1 := holds_trans r0 (holds_context p20_rule24 [] [-4])
  have r2 := holds_trans r1 (holds_context p20_rule23 [6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem p20_rule36 : Holds ((normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 4] [4, 8] := by
  have h0 := (split [-4, -8] [4, 8] (rotate [] [-4, -8, 4, 8] source17))
  have l0 := holds_refl [-4, -8]
  have l1 := holds_trans l0 (holds_context p20_rule23 [] [-8])
  have l2 := holds_trans l1 (holds_context p20_rule25 [4] [])
  have r0 := holds_refl [-8, -4]
  have r1 := holds_trans r0 (holds_context p20_rule25 [] [-4])
  have r2 := holds_trans r1 (holds_context p20_rule23 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem p20_rule39 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s4) [1, 6] [8, 1] := by
  have h0 := (split [1, 6] [1, -8] (rotate [] [1, 6, 1, -8] source27))
  have l0 := holds_refl [1, 6]
  have r0 := holds_refl [8, -1]
  have r1 := holds_trans r0 (holds_context p20_rule20 [8] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p20_rule40 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [1, 8] [6, 1] := by
  have h0 := (split [6, 1] [-8, 1] (rotate [1] [6, 1, -8] source27))
  have l0 := holds_refl [6, 1]
  have r0 := holds_refl [-1, 8]
  have r1 := holds_trans r0 (holds_context p20_rule20 [] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule41 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ)) [8, 2] [2, 4] := by
  have h0 := (split [2, 4] [2, -8] (rotate [] [2, 4, 2, -8] source31))
  have l0 := holds_refl [2, 4]
  have r0 := holds_refl [8, -2]
  have r1 := holds_trans r0 (holds_context p20_rule21 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule42 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2) [4, 2] [2, 8] := by
  have h0 := (split [4, 2] [-8, 2] (rotate [2] [4, 2, -8] source31))
  have l0 := holds_refl [4, 2]
  have r0 := holds_refl [-2, 8]
  have r1 := holds_trans r0 (holds_context p20_rule21 [] [8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p20_rule44 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ)) [-9, 2] [2, 9] := by
  have h0 := (split [2, 9] [2, 9] (rotate [] [2, 9, 2, 9] source34))
  have l0 := holds_refl [2, 9]
  have r0 := holds_refl [-9, -2]
  have r1 := holds_trans r0 (holds_context p20_rule21 [-9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule45 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7) [9, 2] [2, -9] := by
  have h0 := (split [9, 2] [9, 2] (rotate [2] [9, 2, 9] source34))
  have l0 := holds_refl [9, 2]
  have r0 := holds_refl [-2, -9]
  have r1 := holds_trans r0 (holds_context p20_rule21 [] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p20_rule49 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, -5, 2] [-7, -9] := by
  have h0 := (split [-7, -9] [2, 5, 2] (rotate [2, 5, 2] [-7, -9] source35))
  have l0 := holds_refl [-7, -9]
  have r0 := holds_refl [-2, -5, -2]
  have r1 := holds_trans r0 (holds_context p20_rule21 [] [-5, -2])
  have r2 := holds_trans r1 (holds_context p20_rule21 [2, -5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem p20_rule50 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [7, 2, -5] [2, 9] := by
  have h0 := (split [-9, 2] [5, 2, -7] (rotate [2, 5, 2, -7] [-9] source35))
  have l0 := holds_refl [-9, 2]
  have l1 := holds_trans l0 (holds_context p20_rule44 [] [])
  have r0 := holds_refl [7, -2, -5]
  have r1 := holds_trans r0 (holds_context p20_rule21 [7] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem p20_rule60 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * normalizedRelatorError .iv_s2_s8) [4, 8, 6] [10, 4, 10] := by
  have h0 := (split [-8, -6, -4] [-10, 4, 10] (rotate [-4, -10, 4, 10] [-8, -6] source18))
  have l0 := holds_refl [-8, -6, -4]
  have l1 := holds_trans l0 (holds_context p20_rule25 [] [-6, -4])
  have l2 := holds_trans l1 (holds_context p20_rule24 [8] [-4])
  have l3 := holds_trans l2 (holds_context p20_rule23 [8, 6] [])
  have l4 := holds_trans l3 (holds_context p20_rule35 [8] [])
  have l5 := holds_trans l4 (holds_context p20_rule36 [] [6])
  have r0 := holds_refl [-10, -4, 10]
  have r1 := holds_trans r0 (holds_context p20_rule26 [] [-4, 10])
  have r2 := holds_trans r1 (holds_context p20_rule23 [10] [10])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r2)) (by central_nf)

theorem p20_rule226 : Holds (normalizedRelatorError .i_r8) [2, 2] [] := by
  have h0 := c1_rule2
  have l0 := holds_refl [2, -2]
  have l1 := holds_trans l0 (holds_context p20_rule21 [2] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule227 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c1_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context p20_rule22 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule228 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c1_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context p20_rule23 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule229 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c1_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context p20_rule24 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule230 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c1_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context p20_rule25 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule246 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := c1_rule205
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule255 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [6, 8] [8, 6] := by
  have h0 := c1_rule266
  have l0 := holds_refl [8, 6]
  have r0 := holds_refl [6, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p20_rule258 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6) [8, 3, 8] [4, 5, 5] := by
  have h0 := c1_rule287
  have l0 := holds_refl [8, 3, 8]
  have r0 := holds_refl [4, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule285 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 8, -9, 6] [3, 8, 3] := by
  have h0 := c1_rule434
  have l0 := holds_refl [9, 8, -9, 6]
  have r0 := holds_refl [3, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule286 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 8, -9, 8] [-7, 6, 7] := by
  have h0 := c1_rule436
  have l0 := holds_refl [9, 8, -9, 8]
  have r0 := holds_refl [-7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p20_rule287 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [4, 5, 3, 2] [2, 3, 7, -9] := by
  have h0 := c1_rule441
  have l0 := holds_refl [3, 4, 5, 2]
  have l1 := holds_trans l0 (holds_context p20_rule30 [] [5, 2])
  have l2 := holds_trans l1 (holds_context p20_rule32 [4] [2])
  have r0 := holds_refl [2, 3, 7, -9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
