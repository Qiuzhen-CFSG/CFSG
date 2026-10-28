module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step00

/-! Central word identities for the remaining normalized commutators, chunk 1.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule47 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 9, 7] [5, 2] := by
  have h0 := (split [5, 2] [-7, -9, 2] (rotate [2] [5, 2, -7, -9] source35))
  have l0 := holds_refl [5, 2]
  have r0 := holds_refl [-2, 9, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [] [9, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule48 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [-5, 2, 9] [2, -7] := by
  have h0 := (split [2, -7] [-9, 2, 5] (rotate [2, 5] [2, -7, -9] source35))
  have l0 := holds_refl [2, -7]
  have r0 := holds_refl [-5, -2, 9]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [-5] [9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule49 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, -5, 2] [-7, -9] := by
  have h0 := (split [-7, -9] [2, 5, 2] (rotate [2, 5, 2] [-7, -9] source35))
  have l0 := holds_refl [-7, -9]
  have r0 := holds_refl [-2, -5, -2]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [] [-5, -2])
  have r2 := holds_trans r1 (holds_context rc22_rule21 [2, -5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule50 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [7, 2, -5] [2, 9] := by
  have h0 := (split [-9, 2] [5, 2, -7] (rotate [2, 5, 2, -7] [-9] source35))
  have l0 := holds_refl [-9, 2]
  have l1 := holds_trans l0 (holds_context rc22_rule44 [] [])
  have r0 := holds_refl [7, -2, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [7] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule51 : Holds (normalizedRelatorError .viii_s3) [2, 5, 2] [9, 7] := by
  have h0 := (split [9, 7] [-2, -5, -2] (rotate [] [9, 7, -2, -5, -2] (inverted source35)))
  have l0 := holds_refl [9, 7]
  have r0 := holds_refl [2, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule52 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 9, 5] [7, 2] := by
  have h0 := (split [7, -2] [-5, -2, 9] (rotate [9] [7, -2, -5, -2] (inverted source35)))
  have l0 := holds_refl [7, -2]
  have l1 := holds_trans l0 (holds_context rc22_rule21 [7] [])
  have r0 := holds_refl [-9, 2, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule44 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule53 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [-7, 2, 9] [2, -5] := by
  have h0 := (split [-2, -5] [-2, 9, 7] (rotate [9, 7] [-2, -5, -2] (inverted source35)))
  have l0 := holds_refl [-2, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule21 [] [-5])
  have r0 := holds_refl [-7, -9, 2]
  have r1 := holds_trans r0 (holds_context rc22_rule44 [-7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule55 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [5, 2, -7] [2, 9] := by
  have h0 := (split [-2, 9] [7, -2, -5] (rotate [9, 7, -2, -5] [-2] (inverted source35)))
  have l0 := holds_refl [-2, 9]
  have l1 := holds_trans l0 (holds_context rc22_rule21 [] [9])
  have r0 := holds_refl [5, 2, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule56 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .iv_s2_s8) [4, 10, 4] [6, 8, 10] := by
  have h0 := (split [-4, -10, 4] [10, -8, -6] (rotate [] [-4, -10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-4, -10, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [] [-10, 4])
  have l2 := holds_trans l1 (holds_context rc22_rule26 [4] [4])
  have r0 := holds_refl [6, 8, -10]
  have r1 := holds_trans r0 (holds_context rc22_rule26 [6, 8] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule57 : Holds ((normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [6, 4, 8] [10, 4, 10] := by
  have h0 := (split [-10, 4, 10] [-8, -6, -4] (rotate [-4] [-10, 4, 10, -8, -6] source18))
  have l0 := holds_refl [-10, 4, 10]
  have l1 := holds_trans l0 (holds_context rc22_rule26 [] [4, 10])
  have r0 := holds_refl [4, 6, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule35 [] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule58 : Holds (normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s8) [4, 10, 8] [10, 6, 4] := by
  have h0 := (split [4, 10, -8] [-6, -4, -10] (rotate [-4, -10] [4, 10, -8, -6] source18))
  have l0 := holds_refl [4, 10, -8]
  have l1 := holds_trans l0 (holds_context rc22_rule25 [4, 10] [])
  have r0 := holds_refl [10, 4, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule35 [10] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule59 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ)) [6, 8, 10] [10, 8, 6] := by
  have h0 := (split [10, -8, -6] [-4, -10, 4] (rotate [-4, -10, 4] [10, -8, -6] source18))
  have l0 := holds_refl [10, -8, -6]
  have l1 := holds_trans l0 (holds_context rc22_rule25 [10] [-6])
  have l2 := holds_trans l1 (holds_context rc22_rule24 [10, 8] [])
  have r0 := holds_refl [-4, 10, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule23 [] [10, 4])
  have r2 := holds_trans r1 (holds_context rc22_rule56 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule61 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [8, 10, 4] [6, 4, 10] := by
  have h0 := (split [-6, -4, -10] [4, 10, -8] (rotate [-4, -10, 4, 10, -8] [-6] source18))
  have l0 := holds_refl [-6, -4, -10]
  have l1 := holds_trans l0 (holds_context rc22_rule24 [] [-4, -10])
  have l2 := holds_trans l1 (holds_context rc22_rule23 [6] [-10])
  have l3 := holds_trans l2 (holds_context rc22_rule26 [6, 4] [])
  have r0 := holds_refl [8, -10, -4]
  have r1 := holds_trans r0 (holds_context rc22_rule26 [8] [-4])
  have r2 := holds_trans r1 (holds_context rc22_rule23 [8, 10] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule62 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s8) ^ (2 : ℤ) * (normalizedRelatorError .vi_r8_s8) ^ (-1 : ℤ)) [10, 2, 10] [2, 10, 2] := by
  have h0 := (split [2, 10, 2] [10, 2, 10] (rotate [] [2, 10, 2, 10, 2, 10] source25))
  have l0 := holds_refl [2, 10, 2]
  have r0 := holds_refl [-10, -2, -10]
  have r1 := holds_trans r0 (holds_context rc22_rule26 [] [-2, -10])
  have r2 := holds_trans r1 (holds_context rc22_rule21 [10] [-10])
  have r3 := holds_trans r2 (holds_context rc22_rule26 [10, 2] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r3))) (by central_nf)

theorem rc22_rule65 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 3, 4] [3, 8, 5, 5] := by
  have h0 := (split [3, 8, -5, -5] [-4, -3, -3, -8] (rotate [-3, -8] [3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [3, 8, -5, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [3, 8] [])
  have r0 := holds_refl [8, 3, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule68 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [-5, 3, 3, 4] [5, 8, 3, 8] := by
  have h0 := (split [-5, -4, -3, -3] [-8, 3, 8, -5] (rotate [-3, -8, 3, 8, -5] [-5, -4, -3] source13))
  have l0 := holds_refl [-5, -4, -3, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [-5] [-3, -3])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [-5, 4] [-3])
  have l3 := holds_trans l2 (holds_context rc22_rule30 [-5] [-3])
  have l4 := holds_trans l3 (holds_context rc22_rule22 [-5, 3, 4] [])
  have l5 := holds_trans l4 (holds_context rc22_rule30 [-5, 3] [])
  have r0 := holds_refl [5, -8, -3, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule25 [5] [-3, 8])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [5, 8] [8])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule69 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [3, 3, 4, 8] [5, 5, 8, 3] := by
  have h0 := (split [-4, -3, -3, -8] [3, 8, -5, -5] (rotate [-3, -8, 3, 8, -5, -5] [-4, -3] source13))
  have l0 := holds_refl [-4, -3, -3, -8]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [] [-3, -3, -8])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [4] [-3, -8])
  have l3 := holds_trans l2 (holds_context rc22_rule30 [] [-3, -8])
  have l4 := holds_trans l3 (holds_context rc22_rule22 [3, 4] [-8])
  have l5 := holds_trans l4 (holds_context rc22_rule30 [3] [-8])
  have l6 := holds_trans l5 (holds_context rc22_rule25 [3, 3, 4] [])
  have r0 := holds_refl [5, 5, -8, -3]
  have r1 := holds_trans r0 (holds_context rc22_rule25 [5, 5] [-3])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [5, 5, 8] [])
  exact holds_factor (holds_trans (holds_symm l6) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule71 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [6, 7, 7, 3] [-9, 4, 9, 4] := by
  have h0 := (split [-9, -4, 9, 4] [-7, -7, -3, -6] (rotate [] [-9, -4, 9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [-9, -4, 9, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [-9] [9, 4])
  have r0 := holds_refl [6, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule34 [6] [7])
  have r2 := holds_trans r1 (holds_context rc22_rule34 [6, 7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule73 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, 9, 6, 3] [9, 4, 7, 7] := by
  have h0 := (split [9, 4, -7, -7] [-3, -6, -9, -4] (rotate [-9, -4] [9, 4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [9, 4, -7, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [9, 4] [])
  have r0 := holds_refl [4, 9, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule74 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * normalizedRelatorError .iv_s7_s2) [4, 7, 7, 3] [-9, 4, 9, 6] := by
  have h0 := (split [4, -7, -7, -3] [-6, -9, -4, 9] (rotate [-9, -4, 9] [4, -7, -7, -3, -6] source19))
  have l0 := holds_refl [4, -7, -7, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [4] [-3])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [4, 7, 7] [])
  have r0 := holds_refl [-9, 4, 9, 6]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule75 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, -9, 4, 9] [7, 7, 3, 6] := by
  have h0 := (split [-7, -7, -3, -6] [-9, -4, 9, 4] (rotate [-9, -4, 9, 4] [-7, -7, -3, -6] source19))
  have l0 := holds_refl [-7, -7, -3, -6]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [] [-3, -6])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [7, 7] [-6])
  have l3 := holds_trans l2 (holds_context rc22_rule24 [7, 7, 3] [])
  have r0 := holds_refl [-4, -9, 4, 9]
  have r1 := holds_trans r0 (holds_context rc22_rule23 [] [-9, 4, 9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule76 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .iv_s7_s2) [-7, 3, 6, -9] [7, 4, -9, 4] := by
  have h0 := (split [-7, -3, -6, -9] [-4, 9, 4, -7] (rotate [-9, -4, 9, 4, -7] [-7, -3, -6] source19))
  have l0 := holds_refl [-7, -3, -6, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [-7] [-6, -9])
  have l2 := holds_trans l1 (holds_context rc22_rule24 [-7, 3] [-9])
  have r0 := holds_refl [7, -4, -9, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule23 [7] [-9, 4])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule79 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 4, 5, 5] [-7, 6, 7, 6] := by
  have h0 := (split [-7, -6, 7, 6] [-5, -5, -4, -3] (rotate [] [-7, -6, 7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [-7, -6, 7, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule24 [-7] [7, 6])
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule80 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s5_s4) [6, 7, 6, -5] [7, 3, 4, 5] := by
  have h0 := (split [-6, 7, 6, -5] [-5, -4, -3, -7] (rotate [-7] [-6, 7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [-6, 7, 6, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule24 [] [7, 6, -5])
  have r0 := holds_refl [7, 3, 4, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule81 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 3, 4] [7, 6, 5, 5] := by
  have h0 := (split [7, 6, -5, -5] [-4, -3, -7, -6] (rotate [-7, -6] [7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [7, 6, -5, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [7, 6] [])
  have r0 := holds_refl [6, 7, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule82 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .v_s5_s4) [6, 5, 5, 4] [-7, 6, 7, 3] := by
  have h0 := (split [6, -5, -5, -4] [-3, -7, -6, 7] (rotate [-7, -6, 7] [6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [6, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [6] [-4])
  have l2 := holds_trans l1 (holds_context rc22_rule23 [6, 5, 5] [])
  have r0 := holds_refl [-7, 6, 7, 3]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule83 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -7, 6, 7] [5, 5, 3, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-7, -6, 7, 6] (rotate [-7, -6, 7, 6] [-5, -5, -4, -3] source22))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context rc22_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context rc22_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context rc22_rule30 [5, 5] [])
  have r0 := holds_refl [-6, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule24 [] [-7, 6, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule85 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s5_s4) [3, 4, -7, 6] [5, 5, 6, -7] := by
  have h0 := (split [-4, -3, -7, -6] [7, 6, -5, -5] (rotate [-7, -6, 7, 6, -5, -5] [-4, -3] source22))
  have l0 := holds_refl [-4, -3, -7, -6]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [] [-3, -7, -6])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [4] [-7, -6])
  have l3 := holds_trans l2 (holds_context rc22_rule30 [] [-7, -6])
  have l4 := holds_trans l3 (holds_context rc22_rule24 [3, 4, -7] [])
  have r0 := holds_refl [5, 5, -6, -7]
  have r1 := holds_trans r0 (holds_context rc22_rule24 [5, 5] [-7])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule86 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, 5, 5, 6] [-7, 3, 6, 7] := by
  have h0 := (split [-3, -7, -6, 7] [6, -5, -5, -4] (rotate [-7, -6, 7, 6, -5, -5, -4] [-3] source22))
  have l0 := holds_refl [-3, -7, -6, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [] [-7, -6, 7])
  have l2 := holds_trans l1 (holds_context rc22_rule33 [] [-6, 7])
  have l3 := holds_trans l2 (holds_context rc22_rule24 [-7, 3] [7])
  have r0 := holds_refl [4, 5, 5, -6]
  have r1 := holds_trans r0 (holds_context rc22_rule24 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule87 : Holds (normalizedRelatorError .vii_s5) [1, 7, 1, -7] [3, 1, 3, 1] := by
  have h0 := (split [1, 7, 1, -7] [-1, -3, -1, -3] (rotate [] [1, 7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, 7, 1, -7]
  have r0 := holds_refl [3, 1, 3, 1]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule88 : Holds ((normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [1, 3, 1, 3] [7, 1, -7, 1] := by
  have h0 := (split [7, 1, -7, -1] [-3, -1, -3, 1] (rotate [1] [7, 1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [7, 1, -7, -1]
  have l1 := holds_trans l0 (holds_context rc22_rule20 [7, 1, -7] [])
  have r0 := holds_refl [-1, 3, 1, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [] [3, 1, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule89 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .vii_s5) [1, -7, 1, 3] [-7, 1, 3, 1] := by
  have h0 := (split [1, -7, -1, -3] [-1, -3, 1, 7] (rotate [1, 7] [1, -7, -1, -3, -1, -3] source28))
  have l0 := holds_refl [1, -7, -1, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule20 [1, -7] [-3])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [1, -7, 1] [])
  have r0 := holds_refl [-7, -1, 3, 1]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [-7] [3, 1])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule90 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .vii_s5) [1, 3, 1, 7] [3, 1, 7, 1] := by
  have h0 := (split [-1, -3, 1, 7] [1, -7, -1, -3] (rotate [1, 7, 1, -7, -1, -3] [-1, -3] source28))
  have l0 := holds_refl [-1, -3, 1, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule20 [] [-3, 1, 7])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [1] [1, 7])
  have r0 := holds_refl [3, 1, 7, -1]
  have r1 := holds_trans r0 (holds_context rc22_rule20 [3, 1, 7] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule91 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 7, 3, 2, -5] [2, 3, 4, 5] := by
  have h0 := (split [2, 3, 4, 5] [5, 2, -7, -7, -3] (rotate [] [2, 3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [2, 3, 4, 5]
  have r0 := holds_refl [3, 7, 7, -2, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule34 [] [7, -2, -5])
  have r2 := holds_trans r1 (holds_context rc22_rule34 [7] [-2, -5])
  have r3 := holds_trans r2 (holds_context rc22_rule21 [7, 7, 3] [-5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r3))) (by central_nf)

theorem rc22_rule92 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 7, 7, 3, 2] [-7, 6, 7, 6] := by
  have h0 := (split [3, 4, 5, 5] [2, -7, -7, -3, 2] (rotate [2] [3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule79 [] [])
  have r0 := holds_refl [-2, 3, 7, 7, -2]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [] [3, 7, 7, -2])
  have r2 := holds_trans r1 (holds_context rc22_rule34 [2] [7, -2])
  have r3 := holds_trans r2 (holds_context rc22_rule34 [2, 7] [-2])
  have r4 := holds_trans r3 (holds_context rc22_rule21 [2, 7, 7, 3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r4))) (by central_nf)

theorem rc22_rule94 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 2, 8, 7, 3] [5, 2, 9] := by
  have h0 := (split [5, 5, 2, -7] [-7, -3, 2, 3, 4] (rotate [2, 3, 4] [5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [5, 5, 2, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule55 [5] [])
  have r0 := holds_refl [-4, -3, -2, 3, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule23 [] [-3, -2, 3, 7])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [4] [-2, 3, 7])
  have r3 := holds_trans r2 (holds_context rc22_rule30 [] [-2, 3, 7])
  have r4 := holds_trans r3 (holds_context rc22_rule21 [3, 4] [3, 7])
  have r5 := holds_trans r4 (holds_context rc22_rule42 [3] [3, 7])
  have r6 := holds_trans r5 (holds_context rc22_rule34 [3, 2, 8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r6))) (by central_nf)

theorem rc22_rule99 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 2, 3, 4] [7, 2, 9, -5] := by
  have h0 := (split [-3, 2, 3, 4] [5, 5, 2, -7, -7] (rotate [2, 3, 4, 5, 5, 2, -7, -7] [-3] source36))
  have l0 := holds_refl [-3, 2, 3, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule22 [] [2, 3, 4])
  have r0 := holds_refl [7, 7, -2, -5, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule21 [7, 7] [-5, -5])
  have r2 := holds_trans r1 (holds_context rc22_rule50 [7] [-5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule102 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * normalizedRelatorError .viii_r3) [7, 7, 3, 2, 3] [2, 5, 5, 4] := by
  have h0 := (split [-2, -5, -5, -4] [-3, -2, 3, 7, 7] (rotate [3, 7, 7] [-2, -5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-2, -5, -5, -4]
  have l1 := holds_trans l0 (holds_context rc22_rule21 [] [-5, -5, -4])
  have l2 := holds_trans l1 (holds_context rc22_rule27 [2] [-4])
  have l3 := holds_trans l2 (holds_context rc22_rule23 [2, 5, 5] [])
  have r0 := holds_refl [-7, -7, -3, 2, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule28 [] [-3, 2, 3])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [7, 7] [2, 3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule103 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-7, 6, 7, 6] [5, 5, 3, 4] := by
  have h0 := (split [-5, -5, -4, -3] [-2, 3, 7, 7, -2] (rotate [3, 7, 7, -2] [-5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context rc22_rule23 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context rc22_rule22 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context rc22_rule30 [5, 5] [])
  have r0 := holds_refl [2, -7, -7, -3, 2]
  have r1 := holds_trans r0 (holds_context rc22_rule28 [2] [-3, 2])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [2, 7, 7] [2])
  have r3 := holds_trans r2 (holds_context rc22_rule92 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r3))) (by central_nf)

theorem rc22_rule104 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-5, 3, 2, 8] [2, 9, -7, 3] := by
  have h0 := (split [-5, -4, -3, -2] [3, 7, 7, -2, -5] (rotate [3, 7, 7, -2, -5] [-5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -4, -3, -2]
  have l1 := holds_trans l0 (holds_context rc22_rule23 [-5] [-3, -2])
  have l2 := holds_trans l1 (holds_context rc22_rule22 [-5, 4] [-2])
  have l3 := holds_trans l2 (holds_context rc22_rule30 [-5] [-2])
  have l4 := holds_trans l3 (holds_context rc22_rule21 [-5, 3, 4] [])
  have l5 := holds_trans l4 (holds_context rc22_rule42 [-5, 3] [])
  have r0 := holds_refl [5, 2, -7, -7, -3]
  have r1 := holds_trans r0 (holds_context rc22_rule55 [] [-7, -3])
  have r2 := holds_trans r1 (holds_context rc22_rule22 [2, 9, -7] [])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r2)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
