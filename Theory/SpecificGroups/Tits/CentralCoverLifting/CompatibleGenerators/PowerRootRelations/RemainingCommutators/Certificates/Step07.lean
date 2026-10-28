module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step06

/-! Central word identities for the remaining normalized commutators, chunk 7.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule724 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 5, -9, 6] [3, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule721 [-5] [])) (holds_context rc22_rule9 [] [3, -9, 4]))
  have l0 := holds_refl [-5, -5, -9, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [] [-9, 6])
  have r0 := holds_refl [3, -9, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule725 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, -9, 6, 4] [5, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule724 [] [6])) (holds_context rc22_rule200 [5, 5, -9] []))
  have l0 := holds_refl [3, -9, 4, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule35 [3, -9] [])
  have r0 := holds_refl [5, 5, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule726 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 5, -9, 4] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule725 [] [4])) (holds_context rc22_rule199 [3, -9, 6] []))
  have l0 := holds_refl [5, 5, -9, 4]
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule728 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [5, 3, -9, 6] [-5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule726 [5] [])) (holds_context rc22_rule203 [] [-9, 4]))
  have l0 := holds_refl [5, 3, -9, 6]
  have r0 := holds_refl [-5, -9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule734 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 9, -7, 3, 8] [-5, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule201 [-5, 3, 2] [])) (holds_context rc22_rule104 [] [8]))
  have l0 := holds_refl [-5, 3, 2]
  have r0 := holds_refl [2, 9, -7, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule735 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [9, -7, 3, 8] [2, -5, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule734 [2] [])) (holds_context rc22_rule197 [] [9, -7, 3, 8]))
  have l0 := holds_refl [2, -5, 3, 2]
  have r0 := holds_refl [9, -7, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule758 : Holds ((normalizedRelatorError .i_r8) ^ (5 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-3 : ℤ)) [2, -5, 7, -5, 2] [-7, 5, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule225 [] [-5, 2])) (holds_context rc22_rule49 [-7, 5] []))
  have l0 := holds_refl [2, -5, 7, -5, 2]
  have r0 := holds_refl [-7, 5, -7, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule759 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, -5, 7, 5, 2] [-7, 5, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule225 [] [5, 2])) (holds_context rc22_rule51 [-7, 5] []))
  have l0 := holds_refl [2, -5, 7, 5, 2]
  have r0 := holds_refl [-7, 5, 9, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule856 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 3, 2, 9] [2, 3, 4, 5] := by
  have h0 := rc22_rule91
  have l0 := holds_refl [7, 7, 3, 2, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule245 [7] [])
  have r0 := holds_refl [2, 3, 4, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule867 : Holds ((normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 9, 8, 5, 2] [-9, 4, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule247 [-9] [])) (holds_context rc22_rule44 [] [8, 5, 2]))
  have l0 := holds_refl [-9, 4, 9, 7]
  have r0 := holds_refl [2, 9, 8, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule966 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [8, -9, 4, 9, 4] [6, 8, 7, 7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule280 [] [7, 7, 3])) (holds_context rc22_rule71 [8] []))
  have l0 := holds_refl [6, 8, 7, 7, 3]
  have r0 := holds_refl [8, -9, 4, 9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule980 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s8) [4, 10, 3, 8, 5] [10, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule292 [4, 10] [])) (holds_context rc22_rule56 [] [8, -5]))
  have l0 := holds_refl [4, 10, 3, 8, 5]
  have r0 := holds_refl [6, 8, 10, 8, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule327 [6] [8, -5])
  have r2 := holds_trans r1 (holds_context rc22_rule331 [] [8, 8, -5])
  have r3 := holds_trans r2 (holds_context rc22_rule201 [10, 6] [-5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule981 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s8 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [4, 10, 3, 8] [10, 5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule980 [] [-5])) (holds_context rc22_rule8 [4, 10, 3, 8] []))
  have l0 := holds_refl [10, 6, -5, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [10, 6] [])
  have l2 := holds_trans l1 (holds_context rc22_rule689 [10] [])
  have r0 := holds_refl [4, 10, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule985 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s8 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s8) [10, 4, 10, 5, 5] [3, 6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule293 [6, 4] [])) (holds_context rc22_rule57 [] [5, 5]))
  have l0 := holds_refl [6, 4, 3, 4, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule30 [6] [4, 8])
  have l2 := holds_trans l1 (holds_context rc22_rule653 [] [4, 4, 8])
  have l3 := holds_trans l2 (holds_context rc22_rule199 [3, 6] [8])
  have r0 := holds_refl [10, 4, 10, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule986 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s8) [4, 10, 5, 5] [10, 3, 6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule985 [10] [])) (holds_context rc22_rule202 [] [4, 10, 5, 5]))
  have l0 := holds_refl [10, 3, 6, 8]
  have r0 := holds_refl [4, 10, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1000 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [5, 3, 2, 9, 3] [2, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule300 [3] [])) (holds_context rc22_rule198 [] [2, 8, 7]))
  have l0 := holds_refl [3, 5, 2, 9, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [] [2, 9, 3])
  have r0 := holds_refl [2, 8, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1001 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 2, 9, 3] [-5, 2, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1000 [-5] [])) (holds_context rc22_rule9 [] [3, 2, 9, 3]))
  have l0 := holds_refl [-5, 2, 8, 7]
  have r0 := holds_refl [3, 2, 9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1022 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [3, -9, 4, 9, 6] [4, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule314 [] [3])) (holds_context rc22_rule74 [3] []))
  have l0 := holds_refl [-9, 4, 9, 6, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule653 [-9, 4, 9] [])
  have l2 := holds_trans l1 (holds_context rc22_rule674 [-9] [])
  have l3 := holds_trans l2 (holds_context rc22_rule17 [] [4, 7, 7])
  have r0 := holds_refl [3, -9, 4, 9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1023 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [4, 7, 7, 6] [3, -9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1022 [] [6])) (holds_context rc22_rule200 [3, -9, 4, 9] []))
  have l0 := holds_refl [4, 7, 7, 6]
  have r0 := holds_refl [3, -9, 4, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1031 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s6 * normalizedRelatorError .v_s3_s5) [3, 8, -5, 7, 6] [5, 5, 8, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule318 [] [-5])) (holds_context rc22_rule31 [4, 8, 7] []))
  have l0 := holds_refl [5, 5, 8, 7, -5]
  have r0 := holds_refl [4, 8, 7, -5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule645 [4, 8] [])
  have r2 := holds_trans r1 (holds_context rc22_rule383 [] [7, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule1234 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-3 : ℤ)) [-7, 2, 8, 9, 8] [2, -7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule433 [] [2])) (holds_context rc22_rule42 [-7, 4, -9] []))
  have l0 := holds_refl [7, 3, 6, -9, 2]
  have l1 := holds_trans l0 (holds_context rc22_rule648 [] [-9, 2])
  have l2 := holds_trans l1 (holds_context rc22_rule44 [-5, 7, -5] [])
  have l3 := holds_trans l2 (holds_context rc22_rule48 [-5, 7] [])
  have l4 := holds_trans l3 (holds_context rc22_rule223 [] [-7])
  have r0 := holds_refl [-7, 4, -9, 2, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule44 [-7, 4] [8])
  have r2 := holds_trans r1 (holds_context rc22_rule42 [-7] [9, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule1235 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 7, -5, -9, 4] [-7, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule433 [] [4])) (holds_context rc22_rule199 [-7, 4, -9] []))
  have l0 := holds_refl [7, 3, 6, -9, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule648 [] [-9, 4])
  have r0 := holds_refl [-7, 4, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1236 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, -9, 4] [5, -7, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1235 [5] [])) (holds_context rc22_rule8 [] [7, -5, -9, 4]))
  have l0 := holds_refl [5, -7, 4, -9]
  have r0 := holds_refl [7, -5, -9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1238 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [3, 4, -9, 6, 4] [10, 3, 10, 3, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule440 [] [6])) (holds_context rc22_rule35 [3, 4, -9] []))
  have l0 := holds_refl [7, 7, 6, -9, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule144 [] [])
  have r0 := holds_refl [3, 4, -9, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1265 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 3, 6, 4, -7] [-5, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule475 [3] [])) (holds_context rc22_rule31 [] [-7, 3, 6]))
  have l0 := holds_refl [3, 5, 6, 4, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [] [6, 4, -7])
  have r0 := holds_refl [-5, 3, -7, 3, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule33 [-5] [3, 6])
  have r2 := holds_trans r1 (holds_context rc22_rule198 [-5, -7] [6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule1266 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 6, 4, -7] [5, 5, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1265 [-5] [])) (holds_context rc22_rule9 [] [3, 6, 4, -7]))
  have l0 := holds_refl [-5, -5, -7, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [] [-7, 6])
  have r0 := holds_refl [3, 6, 4, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1289 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [6, 8, 7] [-7, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule505 [] [2])) (holds_context rc22_rule42 [-7, 3, 2] []))
  have l0 := holds_refl [2, 9, -5, 3, 2]
  have l1 := holds_trans l0 (holds_context rc22_rule715 [2] [])
  have l2 := holds_trans l1 (holds_context rc22_rule197 [] [6, 8, 7])
  have r0 := holds_refl [-7, 3, 2, 2, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule197 [-7, 3] [8])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1290 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 3, 8, -7] [6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1289 [] [-7])) (holds_context rc22_rule12 [6, 8] []))
  have l0 := holds_refl [-7, 3, 8, -7]
  have r0 := holds_refl [6, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1291 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 8, -7] [7, 6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1290 [7] [])) (holds_context rc22_rule12 [] [3, 8, -7]))
  have l0 := holds_refl [7, 6, 8]
  have r0 := holds_refl [3, 8, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1293 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [5, -7, 5, 8] [8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1289 [6] [])) (holds_context rc22_rule200 [] [8, 7]))
  have l0 := holds_refl [6, -7, 3, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule656 [] [8])
  have r0 := holds_refl [8, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1294 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 5, 8] [-5, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1293 [-5] [])) (holds_context rc22_rule9 [] [-7, 5, 8]))
  have l0 := holds_refl [-5, 8, 7]
  have r0 := holds_refl [-7, 5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1295 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [8, -7, 3, 8] [6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1289 [8] [])) (holds_context rc22_rule280 [] [8, 7]))
  have l0 := holds_refl [8, -7, 3, 8]
  have r0 := holds_refl [6, 8, 8, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule201 [6] [7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1296 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [8, -7, 3] [6, 7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1295 [] [8])) (holds_context rc22_rule201 [8, -7, 3] []))
  have l0 := holds_refl [6, 7, 8]
  have r0 := holds_refl [8, -7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1298 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [3, 8, 7, 7] [7, 6, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1291 [] [-7])) (holds_context rc22_rule28 [3, 8] []))
  have l0 := holds_refl [7, 6, 8, -7]
  have r0 := holds_refl [3, 8, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1300 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-5, 7, -5, 8] [8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1291 [3] [])) (holds_context rc22_rule198 [] [8, -7]))
  have l0 := holds_refl [3, 7, 6, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [] [6, 8])
  have l2 := holds_trans l1 (holds_context rc22_rule648 [] [8])
  have r0 := holds_refl [8, -7]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1301 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, -5, 8] [5, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1300 [5] [])) (holds_context rc22_rule8 [] [7, -5, 8]))
  have l0 := holds_refl [5, 8, -7]
  have r0 := holds_refl [7, -5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1303 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [6, 7, 6, 8] [3, 6, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1291 [6] [])) (holds_context rc22_rule653 [] [8, -7]))
  have l0 := holds_refl [6, 7, 6, 8]
  have r0 := holds_refl [3, 6, 8, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1304 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-7, -5, 8, 7] [7, 7, 5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1294 [-7] [])) (holds_context rc22_rule28 [] [5, 8]))
  have l0 := holds_refl [-7, -5, 8, 7]
  have r0 := holds_refl [7, 7, 5, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1307 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .vii_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 5, 1, 6] [-5, 8, 7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1294 [] [1])) (holds_context rc22_rule39 [-7, 5] []))
  have l0 := holds_refl [-5, 8, 7, 1]
  have r0 := holds_refl [-7, 5, 1, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1309 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [-5, 8, 7, 8] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1294 [] [8])) (holds_context rc22_rule201 [-7, 5] []))
  have l0 := holds_refl [-5, 8, 7, 8]
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
