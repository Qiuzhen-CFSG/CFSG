module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers.Certificates.Step04

/-! Additional kernel-checked central word identities, chunk 5.
Generated from `RemainingPowers/source/certificate.json`; each step
uses a source word or an earlier proved identity. Source: Parrott
(1972), §5, p.683, with commutator a⁻¹ b⁻¹ a b. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
open scoped IsMulCommutative

theorem p21_rule38 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ)) [1, 10] [4, 1] := by
  have h0 := (split [4, 1] [-10, 1] (rotate [1] [4, 1, -10] source26))
  have l0 := holds_refl [4, 1]
  have r0 := holds_refl [-1, 10]
  have r1 := holds_trans r0 (holds_context p21_rule20 [] [10])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule39 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [8, 1] [1, 6] := by
  have h0 := (split [1, 6] [1, -8] (rotate [] [1, 6, 1, -8] source27))
  have l0 := holds_refl [1, 6]
  have r0 := holds_refl [8, -1]
  have r1 := holds_trans r0 (holds_context p21_rule20 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule40 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s4) [6, 1] [1, 8] := by
  have h0 := (split [6, 1] [-8, 1] (rotate [1] [6, 1, -8] source27))
  have l0 := holds_refl [6, 1]
  have r0 := holds_refl [-1, 8]
  have r1 := holds_trans r0 (holds_context p21_rule20 [] [8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule41 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2) [2, 4] [8, 2] := by
  have h0 := (split [2, 4] [2, -8] (rotate [] [2, 4, 2, -8] source31))
  have l0 := holds_refl [2, 4]
  have r0 := holds_refl [8, -2]
  have r1 := holds_trans r0 (holds_context p21_rule21 [8] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule42 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ)) [2, 8] [4, 2] := by
  have h0 := (split [4, 2] [-8, 2] (rotate [2] [4, 2, -8] source31))
  have l0 := holds_refl [4, 2]
  have r0 := holds_refl [-2, 8]
  have r1 := holds_trans r0 (holds_context p21_rule21 [] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule43 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4) [2, 6] [6, 2] := by
  have h0 := (split [2, 6] [2, -6] (rotate [] [2, 6, 2, -6] source32))
  have l0 := holds_refl [2, 6]
  have r0 := holds_refl [6, -2]
  have r1 := holds_trans r0 (holds_context p21_rule21 [6] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule49 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, -5, 2] [-7, -9] := by
  have h0 := (split [-7, -9] [2, 5, 2] (rotate [2, 5, 2] [-7, -9] source35))
  have l0 := holds_refl [-7, -9]
  have r0 := holds_refl [-2, -5, -2]
  have r1 := holds_trans r0 (holds_context p21_rule21 [] [-5, -2])
  have r2 := holds_trans r1 (holds_context p21_rule21 [2, -5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem p21_rule51 : Holds (normalizedRelatorError .viii_s3) [2, 5, 2] [9, 7] := by
  have h0 := (split [9, 7] [-2, -5, -2] (rotate [] [9, 7, -2, -5, -2] (inverted source35)))
  have l0 := holds_refl [9, 7]
  have r0 := holds_refl [2, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule54 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [2, -7, -9] [-5, 2] := by
  have h0 := (split [-5, -2] [9, 7, -2] (rotate [9, 7, -2] [-5, -2] (inverted source35)))
  have l0 := holds_refl [-5, -2]
  have l1 := holds_trans l0 (holds_context p21_rule21 [-5] [])
  have r0 := holds_refl [2, -7, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule56 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [6, 8, 10] [4, 10, 4] := by
  have h0 := (split [-4, -10, 4] [10, -8, -6] (rotate [] [-4, -10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-4, -10, 4]
  have l1 := holds_trans l0 (holds_context p21_rule23 [] [-10, 4])
  have l2 := holds_trans l1 (holds_context p21_rule26 [4] [4])
  have r0 := holds_refl [6, 8, -10]
  have r1 := holds_trans r0 (holds_context p21_rule26 [6, 8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule74 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [-9, 4, 9, 6] [4, 3, 7, 7] := by
  have h0 := (split [4, -7, -7, -3] [-6, -9, -4, 9] (rotate [-9, -4, 9] [4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [4, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context p21_rule28 [4] [-3])
  have l2 := holds_trans l1 (holds_context p21_rule22 [4, 7, 7] [])
  have l3 := holds_trans l2 (holds_context p21_rule34 [4, 7] [])
  have l4 := holds_trans l3 (holds_context p21_rule34 [4] [7])
  have r0 := holds_refl [-9, 4, 9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule87 : Holds ((normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [3, 1, 3, 1] [1, 7, 1, -7] := by
  have h0 := (split [1, 7, 1, -7] [-1, -3, -1, -3] (rotate [] [1, 7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, 7, 1, -7]
  have r0 := holds_refl [3, 1, 3, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule88 : Holds (normalizedRelatorError .vii_s5) [7, 1, -7, 1] [1, 3, 1, 3] := by
  have h0 := (split [7, 1, -7, -1] [-3, -1, -3, 1] (rotate [1] [7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [7, 1, -7, -1]
  have l1 := holds_trans l0 (holds_context p21_rule20 [7, 1, -7] [])
  have r0 := holds_refl [-1, 3, 1, 3]
  have r1 := holds_trans r0 (holds_context p21_rule20 [] [3, 1, 3])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem p21_rule89 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [-7, 1, 3, 1] [1, -7, 1, 3] := by
  have h0 := (split [1, -7, -1, -3] [-1, -3, 1, 7] (rotate [1, 7] [1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, -7, -1, -3]
  have l1 := holds_trans l0 (holds_context p21_rule20 [1, -7] [-3])
  have l2 := holds_trans l1 (holds_context p21_rule22 [1, -7, 1] [])
  have r0 := holds_refl [-7, -1, 3, 1]
  have r1 := holds_trans r0 (holds_context p21_rule20 [-7] [3, 1])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem p21_rule198 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c1_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context p21_rule22 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule199 : Holds (normalizedRelatorError .i_s2) [4, 4] [] := by
  have h0 := c1_rule6
  have l0 := holds_refl [4, -4]
  have l1 := holds_trans l0 (holds_context p21_rule23 [4] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule200 : Holds (normalizedRelatorError .i_s4) [6, 6] [] := by
  have h0 := c1_rule10
  have l0 := holds_refl [6, -6]
  have l1 := holds_trans l0 (holds_context p21_rule24 [6] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule201 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c1_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context p21_rule25 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule202 : Holds (normalizedRelatorError .i_s8) [10, 10] [] := by
  have h0 := c1_rule18
  have l0 := holds_refl [10, -10]
  have l1 := holds_trans l0 (holds_context p21_rule26 [10] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule216 : Holds (normalizedRelatorError .i_s3) [5, 5, 5] [-5] := by
  have h0 := c1_rule205
  have l0 := holds_refl [5, 5, 5]
  have r0 := holds_refl [-5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule218 : Holds (normalizedRelatorError .i_s7) [9, 9, 9] [-9] := by
  have h0 := c1_rule207
  have l0 := holds_refl [9, 9, 9]
  have r0 := holds_refl [-9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule223 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6] [6, 8] := by
  have h0 := c1_rule266
  have l0 := holds_refl [8, 6]
  have r0 := holds_refl [6, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule230 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ)) [5, 5, 8] [4, 8, 3] := by
  have h0 := c1_rule309
  have l0 := holds_refl [5, 5, 8]
  have r0 := holds_refl [4, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule253 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [8, 2, 3, 5, 2] [3, 7, -9] := by
  have h0 := c1_rule429
  have l0 := holds_refl [2, 3, 4, 5, 2]
  have l1 := holds_trans l0 (holds_context p21_rule30 [2] [5, 2])
  have l2 := holds_trans l1 (holds_context p21_rule41 [] [3, 5, 2])
  have r0 := holds_refl [3, 7, -9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule254 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 8, -9, 6] [3, 8, 3] := by
  have h0 := c1_rule434
  have l0 := holds_refl [9, 8, -9, 6]
  have r0 := holds_refl [3, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule255 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 8, -9, 8] [-7, 6, 7] := by
  have h0 := c1_rule436
  have l0 := holds_refl [9, 8, -9, 8]
  have r0 := holds_refl [-7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule274 : Holds (normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ)) [3, 6] [6, 3] := by
  have h0 := c1_rule806
  have l0 := holds_refl [6, 3]
  have r0 := holds_refl [3, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule290 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [5, 5, 6] [6, 5, 5] := by
  have h0 := c1_rule1952
  have l0 := holds_refl [6, 5, 5]
  have r0 := holds_refl [5, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem p21_rule298 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [8, 9, 8, -9] [-7, 6, 7] := by
  have h0 := c1_rule2143
  have l0 := holds_refl [8, 9, 8, -9]
  have r0 := holds_refl [-7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule303 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ)) [7, 7, 4] [4, 7, 7] := by
  have h0 := c1_rule2181
  have l0 := holds_refl [7, 7, 4]
  have r0 := holds_refl [4, 7, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule305 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 6] [3, 7, -5] := by
  have h0 := c1_rule2309
  have l0 := holds_refl [5, 7, 6]
  have r0 := holds_refl [3, 7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule306 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 4, -5] [6, -5, 7] := by
  have h0 := c1_rule2311
  have l0 := holds_refl [7, 4, -5]
  have r0 := holds_refl [6, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule310 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .v_s3_s5) [7, 6, 5] [3, -5, 7] := by
  have h0 := c1_rule2459
  have l0 := holds_refl [7, 6, 5]
  have r0 := holds_refl [3, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule315 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [-9, 6, 9] [9, 6, -9] := by
  have h0 := c1_rule2516
  have l0 := holds_refl [-9, 6, 9]
  have r0 := holds_refl [9, 6, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule316 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [9, 6, -9, 3] [7, 6, 7] := by
  have h0 := c1_rule2552
  have l0 := holds_refl [9, 6, -9, 3]
  have r0 := holds_refl [7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule335 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, -7, 2] [-5, -9] := by
  have h0 := c2_rule255
  have l0 := holds_refl [2, -7, 2]
  have r0 := holds_refl [-5, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule338 : Holds (normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 5, 5] [4, 3, 8] := by
  have h0 := c2_rule316
  have l0 := holds_refl [8, 5, 5]
  have r0 := holds_refl [4, 3, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule342 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [3, 8, 5] [4, 8, -5] := by
  have h0 := c2_rule375
  have l0 := holds_refl [3, 8, 5]
  have r0 := holds_refl [4, 8, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule358 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7] [3, -5, 6] := by
  have h0 := c2_rule535
  have l0 := holds_refl [-7, 5, 7]
  have r0 := holds_refl [3, -5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem p21_rule360 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 7, -5] [3, 7, 6] := by
  have h0 := c2_rule538
  have l0 := holds_refl [-5, 7, -5]
  have r0 := holds_refl [3, 7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords.RemainingPowers
