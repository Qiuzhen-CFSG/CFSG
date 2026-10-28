module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step04

/-! Central word identities for the remaining normalized commutators, chunk 5.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule576 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 6, 7, 4] [7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule569 [] [4])) (holds_context rc22_rule199 [7, 5] []))
  have l0 := holds_refl [5, 6, 7, 4]
  have r0 := holds_refl [7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule577 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 4] [-5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule576 [-5] [])) (holds_context rc22_rule9 [] [6, 7, 4]))
  have l0 := holds_refl [-5, 7, 5]
  have r0 := holds_refl [6, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule581 : Holds ((normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 4, -7, 6] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule571 [] [6])) (holds_context rc22_rule200 [-7, 5] []))
  have l0 := holds_refl [5, 4, -7, 6]
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule582 : Holds ((normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [4, -7, 6] [-5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule581 [-5] [])) (holds_context rc22_rule9 [] [4, -7, 6]))
  have l0 := holds_refl [-5, -7, 5]
  have r0 := holds_refl [4, -7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule587 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [7, 5, 5, 3] [-5, 7, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule577 [] [6])) (holds_context rc22_rule35 [6, 7] []))
  have l0 := holds_refl [-5, 7, 5, 6]
  have r0 := holds_refl [6, 7, 6, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule452 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule589 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ)) [6, 7, 2, 8] [-5, 7, 5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule577 [] [2])) (holds_context rc22_rule42 [6, 7] []))
  have l0 := holds_refl [-5, 7, 5, 2]
  have r0 := holds_refl [6, 7, 2, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule590 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, -5, 7, 5] [7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule577 [6] [])) (holds_context rc22_rule200 [] [7, 4]))
  have l0 := holds_refl [6, -5, 7, 5]
  have r0 := holds_refl [7, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule591 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, -5, 7] [7, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule590 [] [-5])) (holds_context rc22_rule8 [6, -5, 7] []))
  have l0 := holds_refl [7, 4, -5]
  have r0 := holds_refl [6, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule596 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2) [1, -5, -7, 5] [10, 1, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule582 [1] [])) (holds_context rc22_rule37 [] [-7, 6]))
  have l0 := holds_refl [1, -5, -7, 5]
  have r0 := holds_refl [10, 1, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule602 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [7, 4, -5, 2] [2, 6, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule591 [] [2])) (holds_context rc22_rule223 [6] []))
  have l0 := holds_refl [7, 4, -5, 2]
  have r0 := holds_refl [6, 2, -7, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule43 [] [-7, 5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule609 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 3, 4] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule198 [6, 7, 7] [])) (holds_context rc22_rule71 [] [3]))
  have l0 := holds_refl [6, 7, 7]
  have r0 := holds_refl [-9, 4, 9, 4, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule30 [-9, 4, 9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule610 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [4, 9, 3, 4] [9, 6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule609 [9] [])) (holds_context rc22_rule16 [] [4, 9, 3, 4]))
  have l0 := holds_refl [9, 6, 7, 7]
  have r0 := holds_refl [4, 9, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule616 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [5, 6, -7, -5, 7] [5, 5, 3] := by
  have h0 := rc22_rule155
  have l0 := holds_refl [-5, 3, 4, 4, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule199 [-5, 3] [-5])
  have l2 := holds_trans l1 (holds_context rc22_rule31 [-5] [])
  have l3 := holds_trans l2 (holds_context rc22_rule27 [] [3])
  have r0 := holds_refl [5, 6, -7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule617 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, -7, -5, 7] [5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule616 [-5] [])) (holds_context rc22_rule9 [] [6, -7, -5, 7]))
  have l0 := holds_refl [-5, 5, 5, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule9 [] [5, 3])
  have r0 := holds_refl [6, -7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule618 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, -7, -5] [5, -7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule617 [] [-7])) (holds_context rc22_rule12 [6, -7, -5] []))
  have l0 := holds_refl [5, 3, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule33 [5] [])
  have r0 := holds_refl [6, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule619 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, 5, 3] [6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule618 [] [5])) (holds_context rc22_rule9 [6, -7] []))
  have l0 := holds_refl [5, -7, 3, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [5, -7] [])
  have r0 := holds_refl [6, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule620 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 3] [-5, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule619 [-5] [])) (holds_context rc22_rule9 [] [-7, 5, 3]))
  have l0 := holds_refl [-5, 6, -7]
  have r0 := holds_refl [-7, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule623 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, -7, 3] [-7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule618 [6] [])) (holds_context rc22_rule200 [] [-7, -5]))
  have l0 := holds_refl [6, 5, -7, 3]
  have r0 := holds_refl [-7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule624 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, -7] [-7, -5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule623 [] [3])) (holds_context rc22_rule198 [6, 5, -7] []))
  have l0 := holds_refl [-7, -5, 3]
  have r0 := holds_refl [6, 5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule627 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 6, -7] [5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule620 [7] [])) (holds_context rc22_rule12 [] [5, 3]))
  have l0 := holds_refl [7, -5, 6, -7]
  have r0 := holds_refl [5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule628 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 6] [5, 7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule627 [] [7])) (holds_context rc22_rule13 [7, -5, 6] []))
  have l0 := holds_refl [5, 3, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [5] [])
  have r0 := holds_refl [7, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule630 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 5, 3] [-5, 6, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule620 [] [5])) (holds_context rc22_rule32 [-7, 5] []))
  have l0 := holds_refl [-5, 6, -7, 5]
  have r0 := holds_refl [-7, 5, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule631 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [-5, 6, -7, 3] [-5, 3, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule620 [3] [])) (holds_context rc22_rule33 [] [5, 3]))
  have l0 := holds_refl [3, -5, 6, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule31 [] [6, -7])
  have r0 := holds_refl [-7, 3, 5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule32 [-7] [3])
  have r2 := holds_trans r1 (holds_context rc22_rule620 [] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule633 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7, 3] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule620 [] [7])) (holds_context rc22_rule34 [-7, 5] []))
  have l0 := holds_refl [-5, 6, -7, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule13 [-5, 6] [])
  have r0 := holds_refl [-7, 5, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule634 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, 7] [-5, 6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule633 [] [3])) (holds_context rc22_rule198 [-7, 5, 7] []))
  have l0 := holds_refl [-5, 6, 3]
  have r0 := holds_refl [-7, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule635 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 3, 6, -7] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule620 [] [3])) (holds_context rc22_rule198 [-7, 5] []))
  have l0 := holds_refl [-5, 6, -7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule631 [] [])
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule636 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 6, -7] [5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule635 [5] [])) (holds_context rc22_rule8 [] [3, 6, -7]))
  have l0 := holds_refl [5, -7, 5]
  have r0 := holds_refl [3, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule637 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, -5, 7, 3] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule624 [] [7])) (holds_context rc22_rule13 [6, 5] []))
  have l0 := holds_refl [-7, -5, 3, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [-7, -5] [])
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule639 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, 3] [-7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule637 [] [3])) (holds_context rc22_rule198 [-7, -5, 7] []))
  have l0 := holds_refl [6, 5, 3]
  have r0 := holds_refl [-7, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule642 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [8, -7, -5, 3] [6, 8, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule624 [8] [])) (holds_context rc22_rule280 [] [5, -7]))
  have l0 := holds_refl [8, -7, -5, 3]
  have r0 := holds_refl [6, 8, 5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule643 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 3, 6] [5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule628 [3] [])) (holds_context rc22_rule34 [] [-5, 6]))
  have l0 := holds_refl [3, 5, 7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [] [7, 3])
  have l2 := holds_trans l1 (holds_context rc22_rule34 [5] [3])
  have l3 := holds_trans l2 (holds_context rc22_rule198 [5, 7] [])
  have r0 := holds_refl [7, 3, -5, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule31 [7] [6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule644 : Holds ((1 : C)) [-5, 6, 3] [-5, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule643 [-7] [])) (holds_context rc22_rule13 [] [-5, 3, 6]))
  have l0 := holds_refl [-7, 5, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule634 [] [])
  have r0 := holds_refl [-5, 3, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule645 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 3] [5, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule643 [] [6])) (holds_context rc22_rule200 [7, -5, 3] []))
  have l0 := holds_refl [5, 7, 6]
  have r0 := holds_refl [7, -5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule647 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 3, 6] [7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule628 [] [6])) (holds_context rc22_rule200 [7, -5] []))
  have l0 := holds_refl [5, 7, 3, 6]
  have r0 := holds_refl [7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule648 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 3, 6] [-5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule647 [-5] [])) (holds_context rc22_rule9 [] [7, 3, 6]))
  have l0 := holds_refl [-5, 7, -5]
  have r0 := holds_refl [7, 3, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule651 : Holds (normalizedRelatorError .i_s1) [-5, 3, 6, 3] [-5, 6] := by
  have h0 := rc22_rule633
  have l0 := holds_refl [-7, 5, 7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule634 [] [3])
  have l2 := holds_trans l1 (holds_context rc22_rule644 [] [3])
  have r0 := holds_refl [-5, 6]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule652 : Holds (normalizedRelatorError .i_s1) [3, 6, 3] [6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule651 [5] [])) (holds_context rc22_rule8 [] [3, 6, 3]))
  have l0 := holds_refl [5, -5, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule8 [] [6])
  have r0 := holds_refl [3, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule653 : Holds ((1 : C)) [6, 3] [3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule652 [3] [])) (holds_context rc22_rule198 [] [6, 3]))
  have l0 := holds_refl [3, 6]
  have r0 := holds_refl [6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule654 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ)) [6, -5, 3] [3, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule653 [] [-5])) (holds_context rc22_rule31 [6] []))
  have l0 := holds_refl [3, 6, -5]
  have r0 := holds_refl [6, -5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule655 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s3_s5) [3, 6, 5] [-7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule653 [] [5])) (holds_context rc22_rule32 [6] []))
  have l0 := holds_refl [3, 6, 5]
  have r0 := holds_refl [6, 5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule639 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
