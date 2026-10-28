module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step05

/-! Central word identities for the remaining normalized commutators, chunk 6.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule656 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, -7, 3] [5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule653 [] [-7])) (holds_context rc22_rule33 [6] []))
  have l0 := holds_refl [3, 6, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule636 [] [])
  have r0 := holds_refl [6, -7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule657 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [6, 7, 3] [3, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule653 [] [7])) (holds_context rc22_rule34 [6] []))
  have l0 := holds_refl [3, 6, 7]
  have r0 := holds_refl [6, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule658 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 3, 6] [6, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule653 [8] [])) (holds_context rc22_rule280 [] [3]))
  have l0 := holds_refl [8, 3, 6]
  have r0 := holds_refl [6, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule660 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 6, 7, 7] [5, -7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule636 [] [-7])) (holds_context rc22_rule28 [3, 6] []))
  have l0 := holds_refl [5, -7, 5, -7]
  have r0 := holds_refl [3, 6, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule661 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s3_s5) [4, 5, -7, 5] [3, 6, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule636 [4] [])) (holds_context rc22_rule30 [] [6, -7]))
  have l0 := holds_refl [4, 5, -7, 5]
  have r0 := holds_refl [3, 4, 6, -7]
  have r1 := holds_trans r0 (holds_context rc22_rule35 [3] [-7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule663 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, 7, 3] [-7, -5, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule639 [] [7])) (holds_context rc22_rule34 [6, 5] []))
  have l0 := holds_refl [-7, -5, 7, 7]
  have r0 := holds_refl [6, 5, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule665 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [8, -7, -5, 7] [6, 8, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule639 [8] [])) (holds_context rc22_rule280 [] [5, 3]))
  have l0 := holds_refl [8, -7, -5, 7]
  have r0 := holds_refl [6, 8, 5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule667 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [-5, 7, 5, 6] [5, 7, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule645 [] [-5])) (holds_context rc22_rule31 [7, -5] []))
  have l0 := holds_refl [5, 7, 6, -5]
  have r0 := holds_refl [7, -5, -5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule27 [7] [3])
  have r2 := holds_trans r1 (holds_context rc22_rule587 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule668 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, -7, 3] [5, 7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule645 [] [-7])) (holds_context rc22_rule33 [7, -5] []))
  have l0 := holds_refl [5, 7, 6, -7]
  have r0 := holds_refl [7, -5, -7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule669 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 7, 3] [5, 7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule645 [] [7])) (holds_context rc22_rule34 [7, -5] []))
  have l0 := holds_refl [5, 7, 6, 7]
  have r0 := holds_refl [7, -5, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule670 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .viii_s4) [7, 3, 2, 6] [-5, 7, -5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule648 [] [2])) (holds_context rc22_rule43 [7, 3] []))
  have l0 := holds_refl [-5, 7, -5, 2]
  have r0 := holds_refl [7, 3, 2, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule673 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ)) [7, 5, -7, 5] [-5, 7, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule648 [] [-7])) (holds_context rc22_rule636 [7] []))
  have l0 := holds_refl [-5, 7, -5, -7]
  have r0 := holds_refl [7, 5, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule674 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, 9, 3, 6] [9, 4, 7, 7] := by
  have h0 := rc22_rule73
  have l0 := holds_refl [4, 9, 6, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule653 [4, 9] [])
  have r0 := holds_refl [9, 4, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule675 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [3, 6, 8, 5] [10, 4, 10, -5] := by
  have h0 := rc22_rule381
  have l0 := holds_refl [6, 3, 8, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule653 [] [8, 5])
  have r0 := holds_refl [10, 4, 10, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule676 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [3, 6, 8, -5] [10, 4, 10, 5] := by
  have h0 := rc22_rule412
  have l0 := holds_refl [6, 3, 8, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule653 [] [8, -5])
  have r0 := holds_refl [10, 4, 10, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule680 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, 5, -7] [-9, 4, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule656 [] [-7])) (holds_context rc22_rule33 [6, -7] []))
  have l0 := holds_refl [5, -7, 5, -7]
  have r0 := holds_refl [6, -7, -7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule28 [6] [3])
  have r2 := holds_trans r1 (holds_context rc22_rule71 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule684 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 6, 7, 6] [7, 5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule657 [] [6])) (holds_context rc22_rule648 [6] []))
  have l0 := holds_refl [3, 6, 7, 6]
  have r0 := holds_refl [6, -5, 7, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule591 [] [-5])
  have r2 := holds_trans r1 (holds_context rc22_rule27 [7, 4] [])
  have r3 := holds_trans r2 (holds_context rc22_rule377 [7] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule687 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [-5, 6, 8, 3] [5, 10, 4, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule658 [-5] [])) (holds_context rc22_rule299 [] [6]))
  have l0 := holds_refl [-5, 6, 8, 3]
  have r0 := holds_refl [5, 4, 8, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule280 [5, 4] [])
  have r2 := holds_trans r1 (holds_context rc22_rule35 [5] [8])
  have r3 := holds_trans r2 (holds_context rc22_rule57 [5] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule689 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [6, 5, 5] [5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule199 [6, 5, 5] [])) (holds_context rc22_rule82 [] [4]))
  have l0 := holds_refl [6, 5, 5]
  have r0 := holds_refl [-7, 6, 7, 3, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule657 [-7] [4])
  have r2 := holds_trans r1 (holds_context rc22_rule407 [] [4])
  have r3 := holds_trans r2 (holds_context rc22_rule199 [5, 5, 6] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule690 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, 5, 6, -5] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule689 [] [-5])) (holds_context rc22_rule8 [6, 5] []))
  have l0 := holds_refl [5, 5, 6, -5]
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule691 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [-5, 6, 5] [5, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule690 [-5] [])) (holds_context rc22_rule9 [] [5, 6, -5]))
  have l0 := holds_refl [-5, 6, 5]
  have r0 := holds_refl [5, 6, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule692 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [-5, 6, -5] [5, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule690 [5] [])) (holds_context rc22_rule203 [] [6, -5]))
  have l0 := holds_refl [5, 6, 5]
  have r0 := holds_refl [-5, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule693 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, 5, 6, 5] [6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule689 [] [5])) (holds_context rc22_rule203 [6] []))
  have l0 := holds_refl [5, 5, 6, 5]
  have r0 := holds_refl [6, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule698 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [-5, 3, 6, -5] [5, -7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule692 [3] [])) (holds_context rc22_rule31 [] [6, -5]))
  have l0 := holds_refl [3, 5, 6, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [] [6, 5])
  have l2 := holds_trans l1 (holds_context rc22_rule655 [5] [])
  have r0 := holds_refl [-5, 3, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule699 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ)) [-5, 7, 4, -5] [5, 6, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule692 [] [7])) (holds_context rc22_rule591 [-5] []))
  have l0 := holds_refl [5, 6, 5, 7]
  have r0 := holds_refl [-5, 7, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule700 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [7, 5, 6, 5] [5, 5, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule692 [7] [])) (holds_context rc22_rule628 [] [-5]))
  have l0 := holds_refl [7, 5, 6, 5]
  have r0 := holds_refl [5, 7, 3, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule31 [5, 7] [])
  have r2 := holds_trans r1 (holds_context rc22_rule645 [5] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule702 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, 9, 5, 5, 3] [4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule199 [6, 9, 5, 5, 3] [])) (holds_context rc22_rule131 [] [4]))
  have l0 := holds_refl [6, 9, 5, 5, 3]
  have r0 := holds_refl [4, 9, 4, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule199 [4, 9] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule703 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, 9, 5, 5] [4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule702 [] [3])) (holds_context rc22_rule198 [6, 9, 5, 5] []))
  have l0 := holds_refl [4, 9, 3]
  have r0 := holds_refl [6, 9, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule704 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [4, 9, -5, 3] [6, 9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule703 [] [-5])) (holds_context rc22_rule8 [6, 9, 5] []))
  have l0 := holds_refl [4, 9, 3, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule31 [4, 9] [])
  have r0 := holds_refl [6, 9, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule705 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [6, 4, 9, 3] [9, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule703 [6] [])) (holds_context rc22_rule200 [] [9, 5, 5]))
  have l0 := holds_refl [6, 4, 9, 3]
  have r0 := holds_refl [9, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule706 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [4, 9, 5, 3] [6, 9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule703 [] [5])) (holds_context rc22_rule203 [6, 9] []))
  have l0 := holds_refl [4, 9, 3, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [4, 9] [])
  have r0 := holds_refl [6, 9, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule709 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, 4, 9, 5] [9, -5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule704 [4] [])) (holds_context rc22_rule199 [] [9, -5, 3]))
  have l0 := holds_refl [4, 6, 9, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule35 [] [9, 5])
  have r0 := holds_refl [9, -5, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule710 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [9, 5, 5, 3] [6, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule705 [] [3])) (holds_context rc22_rule198 [6, 4, 9] []))
  have l0 := holds_refl [9, 5, 5, 3]
  have r0 := holds_refl [6, 4, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule715 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [9, -5, 3, 2] [2, 6, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule709 [] [2])) (holds_context rc22_rule230 [6, 4] []))
  have l0 := holds_refl [9, -5, 3, 2]
  have r0 := holds_refl [6, 4, 2, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule42 [6] [7])
  have r2 := holds_trans r1 (holds_context rc22_rule43 [] [8, 7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule716 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-9, 6, 4, 9] [5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule710 [-9] [])) (holds_context rc22_rule17 [] [5, 5, 3]))
  have l0 := holds_refl [-9, 6, 4, 9]
  have r0 := holds_refl [5, 5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule718 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [5, 5, 3, -9] [-9, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule716 [] [-9])) (holds_context rc22_rule16 [-9, 6, 4] []))
  have l0 := holds_refl [5, 5, 3, -9]
  have r0 := holds_refl [-9, 6, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule719 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-5, -9, 6, 4] [5, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule718 [-5] [])) (holds_context rc22_rule9 [] [5, 3, -9]))
  have l0 := holds_refl [-5, -9, 6, 4]
  have r0 := holds_refl [5, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule720 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [5, -9, 6, 4] [-5, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule718 [5] [])) (holds_context rc22_rule203 [] [3, -9]))
  have l0 := holds_refl [5, -9, 6, 4]
  have r0 := holds_refl [-5, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule721 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [5, 3, -9, 4] [-5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule719 [] [4])) (holds_context rc22_rule199 [-5, -9, 6] []))
  have l0 := holds_refl [5, 3, -9, 4]
  have r0 := holds_refl [-5, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule723 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-5, 3, -9, 4] [5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule720 [] [4])) (holds_context rc22_rule199 [5, -9, 6] []))
  have l0 := holds_refl [-5, 3, -9, 4]
  have r0 := holds_refl [5, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
