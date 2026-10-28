module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step03

/-! Central word identities for the remaining normalized commutators, chunk 4.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule456 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 5, 5, 3] [6, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule81 [] [3])) (holds_context rc22_rule30 [6, 7, 3] []))
  have l0 := holds_refl [7, 6, 5, 5, 3]
  have r0 := holds_refl [6, 7, 3, 3, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule198 [6, 7] [4])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule457 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 5, 5, 3] [-7, 6, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule456 [-7] [])) (holds_context rc22_rule13 [] [6, 5, 5, 3]))
  have l0 := holds_refl [-7, 6, 7, 4]
  have r0 := holds_refl [6, 5, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule467 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s5_s4) [5, 5, 3, 4, -7] [6, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule83 [] [-7])) (holds_context rc22_rule12 [6, -7, 6] []))
  have l0 := holds_refl [5, 5, 3, 4, -7]
  have r0 := holds_refl [6, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule469 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [6, 7, 6, -7] [7, 6, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule467 [7] [])) (holds_context rc22_rule451 [] [-7]))
  have l0 := holds_refl [7, 6, -7, 6]
  have r0 := holds_refl [6, 7, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule474 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 6, 4, -7] [-7, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule85 [4] [])) (holds_context rc22_rule30 [] [4, -7, 6]))
  have l0 := holds_refl [4, 5, 5, 6, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule377 [] [6, -7])
  have l2 := holds_trans l1 (holds_context rc22_rule35 [5, 5] [-7])
  have r0 := holds_refl [3, 4, 4, -7, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule199 [3] [-7, 6])
  have r2 := holds_trans r1 (holds_context rc22_rule33 [] [6])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule475 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [-5, -7, 3, 6] [5, 6, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule474 [-5] [])) (holds_context rc22_rule9 [] [5, 6, 4, -7]))
  have l0 := holds_refl [-5, -7, 3, 6]
  have r0 := holds_refl [5, 6, 4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule490 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (2 : ℤ)) [1, -7, 1, 7, 3] [-7, 3, 1, 7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule89 [] [7])) (holds_context rc22_rule34 [1, -7, 1] []))
  have l0 := holds_refl [-7, 1, 3, 1, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule90 [-7] [])
  have r0 := holds_refl [1, -7, 1, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule504 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 2, 9, -5, 3] [3, 2, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule99 [] [3])) (holds_context rc22_rule30 [3, 2, 3] []))
  have l0 := holds_refl [7, 2, 9, -5, 3]
  have r0 := holds_refl [3, 2, 3, 3, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule198 [3, 2] [4])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule505 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-7, 3, 2, 4] [2, 9, -5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule504 [-7] [])) (holds_context rc22_rule13 [] [2, 9, -5, 3]))
  have l0 := holds_refl [-7, 3, 2, 4]
  have r0 := holds_refl [2, 9, -5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule509 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-7, 2, 5, 5, 4] [7, 3, 2, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule102 [-7] [])) (holds_context rc22_rule13 [] [7, 3, 2, 3]))
  have l0 := holds_refl [-7, 2, 5, 5, 4]
  have r0 := holds_refl [7, 3, 2, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule513 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, 5, 3, 6, 4] [-7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule103 [6] [])) (holds_context rc22_rule83 [] [6]))
  have l0 := holds_refl [6, 5, 5, 3, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule457 [] [4])
  have l2 := holds_trans l1 (holds_context rc22_rule199 [-7, 6, 7] [])
  have r0 := holds_refl [5, 5, 3, 4, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule35 [5, 5, 3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule516 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, 3, 6, 4] [5, -7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule513 [5] [])) (holds_context rc22_rule203 [] [3, 6, 4]))
  have l0 := holds_refl [5, -7, 6, 7]
  have r0 := holds_refl [-5, 3, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule522 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 9, -7, 3, 2] [-5, 3, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule104 [] [2])) (holds_context rc22_rule41 [-5, 3, 2] []))
  have l0 := holds_refl [2, 9, -7, 3, 2]
  have r0 := holds_refl [-5, 3, 2, 2, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule197 [-5, 3] [4])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule523 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [9, -7, 3, 2] [2, -5, 3, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule522 [2] [])) (holds_context rc22_rule197 [] [9, -7, 3, 2]))
  have l0 := holds_refl [2, -5, 3, 4]
  have r0 := holds_refl [9, -7, 3, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule527 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 2, 7, 3, -9] [4, 5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule106 [] [-9])) (holds_context rc22_rule16 [4, 5, 2] []))
  have l0 := holds_refl [3, 2, 7, 3, -9]
  have r0 := holds_refl [4, 5, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule528 : Holds (normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 4, 5, 2] [2, 7, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule527 [3] [])) (holds_context rc22_rule198 [] [2, 7, 3, -9]))
  have l0 := holds_refl [3, 4, 5, 2]
  have r0 := holds_refl [2, 7, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule531 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 2, 7, 3, 2] [4, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule106 [] [2])) (holds_context rc22_rule45 [4, 5, 2] []))
  have l0 := holds_refl [3, 2, 7, 3, 2]
  have r0 := holds_refl [4, 5, 2, 2, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule197 [4, 5] [-9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule532 : Holds (normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, 4, 5, -9] [2, 7, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule531 [3] [])) (holds_context rc22_rule198 [] [2, 7, 3, 2]))
  have l0 := holds_refl [3, 4, 5, -9]
  have r0 := holds_refl [2, 7, 3, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule534 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [4, 9, 5, 5, 4] [6, 9, 3, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule148 [] [-5])) (holds_context rc22_rule8 [6, 9, 3, 4] []))
  have l0 := holds_refl [4, 9, 4, -5, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [4, 9, 4] [])
  have l2 := holds_trans l1 (holds_context rc22_rule377 [4, 9] [])
  have r0 := holds_refl [6, 9, 3, 4]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule539 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1) [7, 3, 1, -7, 1] [7, 1, -7] := by
  have h0 := rc22_rule159
  have l0 := holds_refl [7, 1, -7, 1, 1]
  have l1 := holds_trans l0 (holds_context rc22_rule196 [7, 1, -7] [])
  have r0 := holds_refl [7, 3, 1, -7, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule540 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1) [3, 1, -7, 1] [1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule539 [-7] [])) (holds_context rc22_rule13 [] [3, 1, -7, 1]))
  have l0 := holds_refl [-7, 7, 1, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule13 [] [1, -7])
  have r0 := holds_refl [3, 1, -7, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule541 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [1, -7, 1] [3, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule540 [] [1])) (holds_context rc22_rule196 [3, 1, -7] []))
  have l0 := holds_refl [1, -7, 1]
  have r0 := holds_refl [3, 1, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule542 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s5) [3, 1, -7, 3] [-7, 1, 3, 1] := by
  have h0 := rc22_rule89
  have l0 := holds_refl [1, -7, 1, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule541 [] [3])
  have r0 := holds_refl [-7, 1, 3, 1]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule546 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s4) [1, -7, 6, 1] [3, 1, -7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule541 [] [8])) (holds_context rc22_rule40 [1, -7] []))
  have l0 := holds_refl [3, 1, -7, 8]
  have r0 := holds_refl [1, -7, 6, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule547 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1) [1, 3, 1, -7] [-7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule541 [1] [])) (holds_context rc22_rule196 [] [-7, 1]))
  have l0 := holds_refl [1, 3, 1, -7]
  have r0 := holds_refl [-7, 1]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule548 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1) [1, 3, 1] [-7, 1, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule547 [] [7])) (holds_context rc22_rule13 [1, 3, 1] []))
  have l0 := holds_refl [-7, 1, 7]
  have r0 := holds_refl [1, 3, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule549 : Holds ((normalizedRelatorError .i_r1) ^ (5 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [-7, 1, 7, 3] [7, 3, 1, -7] := by
  have h0 := rc22_rule88
  have l0 := holds_refl [1, 3, 1, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule548 [] [3])
  have r0 := holds_refl [7, 1, -7, 1]
  have r1 := holds_trans r0 (holds_context rc22_rule541 [7] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule550 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1 * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [3, 1, 7, 1] [-7, 1, 7, 7] := by
  have h0 := rc22_rule90
  have l0 := holds_refl [1, 3, 1, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule548 [] [7])
  have r0 := holds_refl [3, 1, 7, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule552 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ)) [1, 3, 10, 1] [-7, 1, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule548 [] [4])) (holds_context rc22_rule37 [1, 3] []))
  have l0 := holds_refl [-7, 1, 7, 4]
  have r0 := holds_refl [1, 3, 10, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule553 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2) [4, -7, 1, 7] [1, 10, 3, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule548 [4] [])) (holds_context rc22_rule38 [] [3, 1]))
  have l0 := holds_refl [4, -7, 1, 7]
  have r0 := holds_refl [1, 10, 3, 1]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule556 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [-7, 1, 7, 1] [1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule548 [] [1])) (holds_context rc22_rule196 [1, 3] []))
  have l0 := holds_refl [-7, 1, 7, 1]
  have r0 := holds_refl [1, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule557 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [1, 7, 1] [7, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule556 [7] [])) (holds_context rc22_rule12 [] [1, 7, 1]))
  have l0 := holds_refl [7, 1, 3]
  have r0 := holds_refl [1, 7, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule558 : Holds ((normalizedRelatorError .i_r1) ^ (5 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ)) [-7, 3, 1, 7] [7, 1, -7, 3] := by
  have h0 := rc22_rule87
  have l0 := holds_refl [1, 7, 1, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule557 [] [-7])
  have l2 := holds_trans l1 (holds_context rc22_rule33 [7, 1] [])
  have r0 := holds_refl [3, 1, 3, 1]
  have r1 := holds_trans r0 (holds_context rc22_rule548 [3] [])
  have r2 := holds_trans r1 (holds_context rc22_rule33 [] [1, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule559 : Holds ((normalizedRelatorError .i_r1) ^ (5 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-2 : ℤ) * normalizedRelatorError .vii_s5) [-7, 1, 7, 7] [7, 3, 1, 3] := by
  have h0 := rc22_rule550
  have l0 := holds_refl [3, 1, 7, 1]
  have l1 := holds_trans l0 (holds_context rc22_rule557 [3] [])
  have l2 := holds_trans l1 (holds_context rc22_rule34 [] [1, 3])
  have r0 := holds_refl [-7, 1, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule564 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ)) [5, 3, 2, 8, 9] [7, 2, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule197 [7, 2, -9, 3] [])) (holds_context rc22_rule177 [] [2]))
  have l0 := holds_refl [7, 2, -9, 3]
  have r0 := holds_refl [5, 3, 4, -9, 2]
  have r1 := holds_trans r0 (holds_context rc22_rule44 [5, 3, 4] [])
  have r2 := holds_trans r1 (holds_context rc22_rule42 [5, 3] [9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule567 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, -5, 7, 5, 4] [-7, 6, 7] := by
  have h0 := rc22_rule153
  have l0 := holds_refl [-7, 6, 7, 3, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule198 [-7, 6, 7] [])
  have r0 := holds_refl [-7, -5, 7, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule568 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-5, 7, 5, 4] [6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule567 [7] [])) (holds_context rc22_rule12 [] [-5, 7, 5, 4]))
  have l0 := holds_refl [7, -7, 6, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule12 [] [6, 7])
  have r0 := holds_refl [-5, 7, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule569 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 5, 4] [5, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule568 [5] [])) (holds_context rc22_rule8 [] [7, 5, 4]))
  have l0 := holds_refl [5, 6, 7]
  have r0 := holds_refl [7, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule570 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, 6, 7] [5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule569 [-7] [])) (holds_context rc22_rule13 [] [5, 4]))
  have l0 := holds_refl [-7, 5, 6, 7]
  have r0 := holds_refl [5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule571 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, 6] [5, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule570 [] [-7])) (holds_context rc22_rule12 [-7, 5, 6] []))
  have l0 := holds_refl [5, 4, -7]
  have r0 := holds_refl [-7, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
