module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step01

/-! Central word identities for the remaining normalized commutators, chunk 2.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule106 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [4, 5, 2, 9] [3, 2, 7, 3] := by
  have h0 := (split [-3, -2, 3, 7] [7, -2, -5, -5, -4] (rotate [3, 7, 7, -2, -5, -5, -4] [-3, -2] (inverted source36)))
  have l0 := holds_refl [-3, -2, 3, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [] [-2, 3, 7])
  have l2 := holds_trans l1 (holds_context rc22_rule21 [3] [3, 7])
  have l3 := holds_trans l2 (holds_context rc22_rule34 [3, 2] [])
  have r0 := holds_refl [4, 5, 5, 2, -7]
  have r1 := holds_trans r0 (holds_context rc22_rule55 [4, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule125 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s8) [5, 5, 3, 3, 4, -9] [10, 3, 10, 3, 9] := by
  have h0 := (split [-10, -3, 10, 3, 9] [9, 3, 4, 5, 5, 3] (rotate [9, 9, 3, 4, 5, 5, 3] [-10, -3, 10, 3] (inverted source15)))
  have l0 := holds_refl [-10, -3, 10, 3, 9]
  have l1 := holds_trans l0 (holds_context rc22_rule26 [] [-3, 10, 3, 9])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [10] [10, 3, 9])
  have r0 := holds_refl [-3, -5, -5, -4, -3, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule22 [] [-5, -5, -4, -3, -9])
  have r2 := holds_trans r1 (holds_context rc22_rule31 [] [-5, -4, -3, -9])
  have r3 := holds_trans r2 (holds_context rc22_rule31 [-5] [-4, -3, -9])
  have r4 := holds_trans r3 (holds_context rc22_rule27 [] [3, -4, -3, -9])
  have r5 := holds_trans r4 (holds_context rc22_rule23 [5, 5, 3] [-3, -9])
  have r6 := holds_trans r5 (holds_context rc22_rule22 [5, 5, 3, 4] [-9])
  have r7 := holds_trans r6 (holds_context rc22_rule30 [5, 5, 3] [-9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r7))) (by central_nf)

theorem rc22_rule131 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, 9, 5, 5, 3, 4] [4, 9, 4] := by
  have h0 := (split [9, 6, -7, -7, -3] [-5, -5, -4, -3, -9, -6] (rotate [-9, -6] [9, 6, -7, -7, -3, -5, -5, -4, -3] source20))
  have l0 := holds_refl [9, 6, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [9, 6] [-3])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [9, 6, 7, 7] [])
  have l3 := holds_trans l2 (holds_context rc22_rule71 [9] [])
  have l4 := holds_trans l3 (holds_context rc22_rule16 [] [4, 9, 4])
  have r0 := holds_refl [6, 9, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule79 [6, 9] [])
  have r2 := holds_trans r1 (holds_context rc22_rule103 [6, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule144 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [7, 7, 6, -9, 6] [10, 3, 10, 3, 9] := by
  have h0 := (split [7, 7, -6, -9, 6] [9, 3, 4, 5, 5, 3] (rotate [3, 4, 5, 5, 3] [7, 7, -6, -9, 6, 9] (inverted source20)))
  have l0 := holds_refl [7, 7, -6, -9, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule24 [7, 7] [-9, 6])
  have r0 := holds_refl [-3, -5, -5, -4, -3, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule22 [] [-5, -5, -4, -3, -9])
  have r2 := holds_trans r1 (holds_context rc22_rule31 [] [-5, -4, -3, -9])
  have r3 := holds_trans r2 (holds_context rc22_rule31 [-5] [-4, -3, -9])
  have r4 := holds_trans r3 (holds_context rc22_rule27 [] [3, -4, -3, -9])
  have r5 := holds_trans r4 (holds_context rc22_rule23 [5, 5, 3] [-3, -9])
  have r6 := holds_trans r5 (holds_context rc22_rule22 [5, 5, 3, 4] [-9])
  have r7 := holds_trans r6 (holds_context rc22_rule30 [5, 5, 3] [-9])
  have r8 := holds_trans r7 (holds_context rc22_rule125 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r8)) (by central_nf)

theorem rc22_rule148 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 9, 3, 4, 5] [4, 9, 4, -5] := by
  have h0 := (split [6, 9, 3, 4, 5] [5, 3, 7, 7, -6, -9] (rotate [3, 4, 5, 5, 3, 7, 7, -6, -9] [6, 9] (inverted source20)))
  have l0 := holds_refl [6, 9, 3, 4, 5]
  have r0 := holds_refl [9, 6, -7, -7, -3, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule28 [9, 6] [-3, -5])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [9, 6, 7, 7] [-5])
  have r3 := holds_trans r2 (holds_context rc22_rule71 [9] [-5])
  have r4 := holds_trans r3 (holds_context rc22_rule16 [] [4, 9, 4, -5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem rc22_rule153 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 6, 7, 3, 3] [-7, -5, 7, 5, 4] := by
  have h0 := (split [-6, -5, -5, -4, -3] [-4, -5, -7, 5, 7] (rotate [-5, -7, 5, 7] [-6, -5, -5, -4, -3, -4] source21))
  have l0 := holds_refl [-6, -5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule24 [] [-5, -5, -4, -3])
  have l2 := holds_trans l1 (holds_context rc22_rule27 [6] [-4, -3])
  have l3 := holds_trans l2 (holds_context rc22_rule23 [6, 5, 5] [-3])
  have l4 := holds_trans l3 (holds_context rc22_rule82 [] [-3])
  have l5 := holds_trans l4 (holds_context rc22_rule22 [-7, 6, 7, 3] [])
  have r0 := holds_refl [-7, -5, 7, 5, 4]
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule155 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s3_s5) [-5, 3, 4, 4, -5] [5, 6, -7, -5, 7] := by
  have h0 := (split [-5, -4, -3, -4, -5] [-7, 5, 7, -6, -5] (rotate [-5, -7, 5, 7, -6, -5] [-5, -4, -3, -4] source21))
  have l0 := holds_refl [-5, -4, -3, -4, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [-5] [-3, -4, -5])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [-5, 4] [-4, -5])
  have l3 := holds_trans l2 (holds_context rc22_rule30 [-5] [-4, -5])
  have l4 := holds_trans l3 (holds_context rc22_rule23 [-5, 3, 4] [-5])
  have r0 := holds_refl [5, 6, -7, -5, 7]
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule159 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [7, 1, -7, 1, 1] [7, 3, 1, -7, 1] := by
  have h0 := (split [3, 1, 3, 1, 3] [1, 3, 1, 3, 1] (rotate [] [3, 1, 3, 1, 3, 1, 3, 1, 3, 1] source24))
  have l0 := holds_refl [3, 1, 3, 1, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule88 [3] [])
  have l2 := holds_trans l1 (holds_context rc22_rule34 [] [1, -7, 1])
  have r0 := holds_refl [-1, -3, -1, -3, -1]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [] [-3, -1, -3, -1])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [1] [-1, -3, -1])
  have r3 := holds_trans r2 (holds_context rc22_rule20 [1, 3] [-3, -1])
  have r4 := holds_trans r3 (holds_context rc22_rule22 [1, 3, 1] [-1])
  have r5 := holds_trans r4 (holds_context rc22_rule88 [] [-1])
  have r6 := holds_trans r5 (holds_context rc22_rule20 [7, 1, -7, 1] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r6))) (by central_nf)

theorem rc22_rule177 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ)) [7, 2, -9, 3, 2] [5, 3, 4, -9] := by
  have h0 := (split [7, 9, -2, -3, -2] [9, 3, 4, 5, 5, 5] (rotate [9, 3, 4, 5, 5, 5] [7, 9, -2, -3, -2] (inverted source33)))
  have l0 := holds_refl [7, 9, -2, -3, -2]
  have l1 := holds_trans l0 (holds_context rc22_rule21 [7, 9] [-3, -2])
  have l2 := holds_trans l1 (holds_context rc22_rule45 [7] [-3, -2])
  have l3 := holds_trans l2 (holds_context rc22_rule22 [7, 2, -9] [-2])
  have l4 := holds_trans l3 (holds_context rc22_rule21 [7, 2, -9, 3] [])
  have r0 := holds_refl [-5, -5, -5, -4, -3, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule27 [] [-5, -4, -3, -9])
  have r2 := holds_trans r1 (holds_context rc22_rule8 [5] [-4, -3, -9])
  have r3 := holds_trans r2 (holds_context rc22_rule23 [5] [-3, -9])
  have r4 := holds_trans r3 (holds_context rc22_rule22 [5, 4] [-9])
  have r5 := holds_trans r4 (holds_context rc22_rule30 [5] [-9])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r5)) (by central_nf)

theorem rc22_rule194 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .vi_s1_r1 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ)) [3, 1, 3, 10, 1] [5, 1, -9, -7, 5] := by
  have h0 := (split [5, 1, -9, -7, -5, -5, -5] [-4, -3, -1, -3, -1, -3, 1] (rotate [1] [5, 1, -9, -7, -5, -5, -5, -4, -3, -1, -3, -1, -3] source29))
  have l0 := holds_refl [5, 1, -9, -7, -5, -5, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [5, 1, -9, -7] [-5])
  have l2 := holds_trans l1 (holds_context rc22_rule8 [5, 1, -9, -7, 5] [])
  have r0 := holds_refl [-1, 3, 1, 3, 1, 3, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [] [3, 1, 3, 1, 3, 4])
  have r2 := holds_trans r1 (holds_context rc22_rule88 [] [1, 3, 4])
  have r3 := holds_trans r2 (holds_context rc22_rule159 [] [3, 4])
  have r4 := holds_trans r3 (holds_context rc22_rule89 [7, 3] [4])
  have r5 := holds_trans r4 (holds_context rc22_rule33 [7] [1, 3, 1, 4])
  have r6 := holds_trans r5 (holds_context rc22_rule12 [] [3, 1, 3, 1, 4])
  have r7 := holds_trans r6 (holds_context rc22_rule37 [3, 1, 3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r7))) (by central_nf)

theorem rc22_rule196 : Holds (normalizedRelatorError .i_r1) [1, 1] [] := by
  have h0 := rc22_rule0
  have l0 := holds_refl [1, -1]
  have l1 := holds_trans l0 (holds_context rc22_rule20 [1] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule197 : Holds (normalizedRelatorError .i_r8) [2, 2] [] := by
  have h0 := rc22_rule2
  have l0 := holds_refl [2, -2]
  have l1 := holds_trans l0 (holds_context rc22_rule21 [2] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule198 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := rc22_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule199 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := rc22_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule200 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := rc22_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context rc22_rule24 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule201 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := rc22_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context rc22_rule25 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule202 : Holds (normalizedRelatorError .i_s8) [10, 10] [] := by
  have h0 := rc22_rule18
  have l0 := holds_refl [10, -10]
  have l1 := holds_trans l0 (holds_context rc22_rule26 [10] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule203 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule27 [5] [])) (holds_context rc22_rule8 [] [-5]))
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule204 : Holds (normalizedRelatorError .i_s5) [7, 7, 7] [-7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule28 [7] [])) (holds_context rc22_rule12 [] [-7]))
  have l0 := holds_refl [7, 7, 7]
  have r0 := holds_refl [-7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule205 : Holds (normalizedRelatorError .i_s7) [9, 9, 9] [-9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule29 [9] [])) (holds_context rc22_rule16 [] [-9]))
  have l0 := holds_refl [9, 9, 9]
  have r0 := holds_refl [-9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule207 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [4, 5, 3] [3, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule32 [4] [])) (holds_context rc22_rule30 [] [5]))
  have l0 := holds_refl [4, 5, 3]
  have r0 := holds_refl [3, 4, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule208 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [4, -7, 3] [3, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule33 [4] [])) (holds_context rc22_rule30 [] [-7]))
  have l0 := holds_refl [4, -7, 3]
  have r0 := holds_refl [3, 4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule209 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [4, 7, 3] [3, 4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule34 [4] [])) (holds_context rc22_rule30 [] [7]))
  have l0 := holds_refl [4, 7, 3]
  have r0 := holds_refl [3, 4, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule210 : Holds (normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 3, 4] [4, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule36 [] [3])) (holds_context rc22_rule30 [8] []))
  have l0 := holds_refl [4, 8, 3]
  have r0 := holds_refl [8, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule212 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .vii_s2) [1, 3, 4] [10, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule37 [] [3])) (holds_context rc22_rule30 [1] []))
  have l0 := holds_refl [10, 1, 3]
  have r0 := holds_refl [1, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule213 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2) [1, 6, 4] [10, 1, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule37 [] [6])) (holds_context rc22_rule35 [1] []))
  have l0 := holds_refl [10, 1, 6]
  have r0 := holds_refl [1, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule223 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [-5, 7, 2] [2, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule52 [-5] [])) (holds_context rc22_rule48 [] [5]))
  have l0 := holds_refl [-5, 7, 2]
  have r0 := holds_refl [2, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule224 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, -5, -9] [-7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule53 [] [-9])) (holds_context rc22_rule16 [-7, 2] []))
  have l0 := holds_refl [2, -5, -9]
  have r0 := holds_refl [-7, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule225 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ)) [-7, 5, 2] [2, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule53 [] [7])) (holds_context rc22_rule47 [-7] []))
  have l0 := holds_refl [2, -5, 7]
  have r0 := holds_refl [-7, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule226 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ)) [1, 10, 1] [4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule196 [] [4])) (holds_context rc22_rule37 [1] []))
  have l0 := holds_refl [4]
  have r0 := holds_refl [1, 10, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule227 : Holds (normalizedRelatorError .vii_s4) [1, 6, 1] [8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule196 [8] [])) (holds_context rc22_rule39 [] [1]))
  have l0 := holds_refl [8]
  have r0 := holds_refl [1, 6, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule228 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 7, 2] [9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule197 [] [9, 5])) (holds_context rc22_rule52 [2] []))
  have l0 := holds_refl [9, 5]
  have r0 := holds_refl [2, 7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule229 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, -7, 2] [-5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule224 [2] [])) (holds_context rc22_rule197 [] [-5, -9]))
  have l0 := holds_refl [2, -7, 2]
  have r0 := holds_refl [-5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule230 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [9, 5, 2] [2, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule228 [] [2])) (holds_context rc22_rule197 [2, 7] []))
  have l0 := holds_refl [9, 5, 2]
  have r0 := holds_refl [2, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule238 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 4, -5, 2] [8, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule49 [8] [])) (holds_context rc22_rule41 [] [-5, 2]))
  have l0 := holds_refl [8, -7, -9]
  have r0 := holds_refl [2, 4, -5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule245 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [7, 3, 2, -5] [3, 2, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule50 [3] [])) (holds_context rc22_rule34 [] [2, -5]))
  have l0 := holds_refl [3, 2, 9]
  have r0 := holds_refl [7, 3, 2, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule246 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s3) [2, 4, 5, 2] [8, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule51 [8] [])) (holds_context rc22_rule41 [] [5, 2]))
  have l0 := holds_refl [8, 9, 7]
  have r0 := holds_refl [2, 4, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule247 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [2, 8, 5, 2] [4, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule51 [4] [])) (holds_context rc22_rule42 [] [5, 2]))
  have l0 := holds_refl [4, 9, 7]
  have r0 := holds_refl [2, 8, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule260 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [-7, 3, 2, 9] [3, 2, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule53 [3] [])) (holds_context rc22_rule33 [] [2, 9]))
  have l0 := holds_refl [3, 2, -5]
  have r0 := holds_refl [-7, 3, 2, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule273 : Holds (normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 10, 8, 6] [6, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule56 [8] [])) (holds_context rc22_rule36 [] [10, 4]))
  have l0 := holds_refl [8, 6, 8, 10]
  have l1 := holds_trans l0 (holds_context rc22_rule59 [8] [])
  have r0 := holds_refl [4, 8, 10, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule61 [4] [])
  have r2 := holds_trans r1 (holds_context rc22_rule35 [] [4, 10])
  have r3 := holds_trans r2 (holds_context rc22_rule199 [6] [10])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
