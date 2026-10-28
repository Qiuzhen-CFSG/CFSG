module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step29

/-! Kernel-checked central word identities, chunk 30.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c9_rule1583 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 7, 6, 7, 5] [6, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule634 [-7] [])) (holds_context c9_rule28 [] [6, 7, 5]))
  have l0 := holds_refl [-7, 6, 3, 4, -5]
  have l1 := holds_trans l0 (holds_context c9_rule480 [] [4, -5])
  have l2 := holds_trans l1 (holds_context c9_rule1568 [3] [])
  have l3 := holds_trans l2 (holds_context c9_rule477 [] [3, -7, 5])
  have l4 := holds_trans l3 (holds_context c9_rule224 [6] [-7, 5])
  have r0 := holds_refl [7, 7, 6, 7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1584 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 7, 6, 7] [6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1583 [] [-5])) (holds_context c9_rule8 [7, 7, 6, 7] []))
  have l0 := holds_refl [6, -7, 5, -5]
  have l1 := holds_trans l0 (holds_context c9_rule8 [6, -7] [])
  have r0 := holds_refl [7, 7, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1585 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 7, 6] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1584 [] [-7])) (holds_context c9_rule12 [7, 7, 6] []))
  have l0 := holds_refl [6, -7, -7]
  have l1 := holds_trans l0 (holds_context c9_rule28 [6] [])
  have r0 := holds_refl [7, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1586 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-7, 6, -7] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1584 [-7] [])) (holds_context c9_rule13 [] [7, 6, 7]))
  have l0 := holds_refl [-7, 6, -7]
  have r0 := holds_refl [7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1590 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [7, 6, 7, 7] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1585 [7] [])) (holds_context c9_rule230 [] [6]))
  have l0 := holds_refl [7, 6, 7, 7]
  have r0 := holds_refl [-7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1593 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 6, 7, -5] [3, -7, 5, -7] := by
  have h0 := c9_rule489
  have l0 := holds_refl [-7, 6, -7, -5]
  have l1 := holds_trans l0 (holds_context c9_rule1586 [] [-5])
  have r0 := holds_refl [3, -7, 5, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1645 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ)) [6, 3, -5, 4, -7] [-7, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule858 [-5, -7] [])) (holds_context c9_rule320 [] [5, 6]))
  have l0 := holds_refl [-5, -7, 6, 5, 5]
  have l1 := holds_trans l0 (holds_context c9_rule1569 [-5] [])
  have l2 := holds_trans l1 (holds_context c9_rule478 [] [-7, 4])
  have l3 := holds_trans l2 (holds_context c9_rule482 [3] [4])
  have l4 := holds_trans l3 (holds_context c9_rule224 [] [-7, 5, 4])
  have r0 := holds_refl [4, -7, 6, 5, 6]
  have r1 := holds_trans r0 (holds_context c9_rule626 [] [6])
  have r2 := holds_trans r1 (holds_context c9_rule84 [6] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule1646 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ)) [-7, 5, 4, 7] [6, 3, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1645 [] [7])) (holds_context c9_rule13 [6, 3, -5, 4] []))
  have l0 := holds_refl [-7, 5, 4, 7]
  have r0 := holds_refl [6, 3, -5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1650 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, -7, -5, 6] [6, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule858 [3, -7] [])) (holds_context c9_rule468 [] [6]))
  have l0 := holds_refl [3, -7, 6, 5, 5]
  have l1 := holds_trans l0 (holds_context c9_rule1569 [3] [])
  have l2 := holds_trans l1 (holds_context c9_rule477 [] [3, -7, 4])
  have l3 := holds_trans l2 (holds_context c9_rule224 [6] [-7, 4])
  have r0 := holds_refl [6, 5, -7, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1651 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, -5, 6] [-7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1650 [6] [])) (holds_context c9_rule226 [] [5, -7, -5, 6]))
  have l0 := holds_refl [6, 6, -7, 4]
  have l1 := holds_trans l0 (holds_context c9_rule226 [] [-7, 4])
  have r0 := holds_refl [5, -7, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1652 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, -7, 4] [-7, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1651 [-5] [])) (holds_context c9_rule9 [] [-7, -5, 6]))
  have l0 := holds_refl [-5, -7, 4]
  have r0 := holds_refl [-7, -5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1653 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, -5] [-7, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1651 [] [6])) (holds_context c9_rule226 [5, -7, -5] []))
  have l0 := holds_refl [-7, 4, 6]
  have l1 := holds_trans l0 (holds_context c9_rule35 [-7] [])
  have r0 := holds_refl [5, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1660 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, -5, 6, 4] [-5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1652 [] [4])) (holds_context c9_rule225 [-5, -7] []))
  have l0 := holds_refl [-7, -5, 6, 4]
  have r0 := holds_refl [-5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1661 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [-5, 6, 4] [7, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1660 [7] [])) (holds_context c9_rule12 [] [-5, 6, 4]))
  have l0 := holds_refl [7, -5, -7]
  have r0 := holds_refl [-5, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1664 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, 6, 4, 5] [5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1653 [] [5])) (holds_context c9_rule9 [5, -7] []))
  have l0 := holds_refl [-7, 6, 4, 5]
  have r0 := holds_refl [5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1665 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 5, -7] [6, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1664 [7] [])) (holds_context c9_rule12 [] [6, 4, 5]))
  have l0 := holds_refl [7, 5, -7]
  have r0 := holds_refl [6, 4, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1667 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ)) [-7, 6, 4, 7] [3, 5, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1653 [] [7])) (holds_context c9_rule457 [5] []))
  have l0 := holds_refl [-7, 6, 4, 7]
  have r0 := holds_refl [5, 3, 6, 5]
  have r1 := holds_trans r0 (holds_context c9_rule32 [] [6, 5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule1682 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, 4, 5, 7] [7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1665 [] [7])) (holds_context c9_rule13 [7, 5] []))
  have l0 := holds_refl [6, 4, 5, 7]
  have r0 := holds_refl [7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1683 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [4, 5, 7] [6, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1682 [6] [])) (holds_context c9_rule226 [] [4, 5, 7]))
  have l0 := holds_refl [6, 7, 5]
  have r0 := holds_refl [4, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1692 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ)) [3, 4, 7, -5] [6, 7, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1683 [] [6])) (holds_context c9_rule462 [4] []))
  have l0 := holds_refl [6, 7, 5, 6]
  have r0 := holds_refl [4, 3, 7, -5]
  have r1 := holds_trans r0 (holds_context c9_rule30 [] [7, -5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule1811 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, 6, 7, 5, 5] [-9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1167 [7] [])) (holds_context c9_rule34 [] [7, 6, 4]))
  have l0 := holds_refl [7, 6, 7, 5, 5]
  have r0 := holds_refl [3, 7, 7, 6, 4]
  have r1 := holds_trans r0 (holds_context c9_rule1585 [3] [4])
  have r2 := holds_trans r1 (holds_context c9_rule477 [] [7, 7, 4])
  have r3 := holds_trans r2 (holds_context c9_rule71 [] [4])
  have r4 := holds_trans r3 (holds_context c9_rule225 [-9, 4, 9] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem c9_rule1814 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, -7, 5, -7] [-9, 4, 9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1811 [] [5])) (holds_context c9_rule229 [7, 6, 7] []))
  have l0 := holds_refl [-9, 4, 9, 5]
  have r0 := holds_refl [7, 6, 7, -5]
  have r1 := holds_trans r0 (holds_context c9_rule1593 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule1987 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, -9, 6, 9] [7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1308 [3] [])) (holds_context c9_rule1226 [] [9]))
  have l0 := holds_refl [3, -7, 5, -7, 4]
  have l1 := holds_trans l0 (holds_context c9_rule1814 [] [4])
  have l2 := holds_trans l1 (holds_context c9_rule1326 [-9] [])
  have l3 := holds_trans l2 (holds_context c9_rule17 [] [7, -5, 7])
  have r0 := holds_refl [5, -9, 6, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1988 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * normalizedRelatorError .viii_r3) [3, 7, 6, 7] [-9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1987 [-5] [])) (holds_context c9_rule9 [] [-9, 6, 9]))
  have l0 := holds_refl [-5, 7, -5, 7]
  have l1 := holds_trans l0 (holds_context c9_rule454 [] [7])
  have r0 := holds_refl [-9, 6, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1992 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -9, 6, 9] [7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1988 [3] [])) (holds_context c9_rule224 [] [7, 6, 7]))
  have l0 := holds_refl [3, -9, 6, 9]
  have r0 := holds_refl [7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1993 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * normalizedRelatorError .viii_r3) [-9, 6, 9, 7] [3, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1988 [] [7])) (holds_context c9_rule1590 [3] []))
  have l0 := holds_refl [-9, 6, 9, 7]
  have r0 := holds_refl [3, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1996 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * normalizedRelatorError .viii_r3) [7, 6, 7, -9] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1992 [] [-9])) (holds_context c9_rule16 [3, -9, 6] []))
  have l0 := holds_refl [7, 6, 7, -9]
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1997 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 3, -7, 6] [6, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1993 [9] [])) (holds_context c9_rule16 [] [6, 9, 7]))
  have l0 := holds_refl [9, 3, -7, 6]
  have r0 := holds_refl [6, 9, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule2002 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -7, -9, 6] [6, 7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1996 [-7] [])) (holds_context c9_rule13 [] [6, 7, -9]))
  have l0 := holds_refl [-7, 3, -9, 6]
  have l1 := holds_trans l0 (holds_context c9_rule33 [] [-9, 6])
  have r0 := holds_refl [6, 7, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule2003 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * normalizedRelatorError .viii_r3) [6, 9, 7, 6] [9, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1997 [] [6])) (holds_context c9_rule226 [9, 3, -7] []))
  have l0 := holds_refl [6, 9, 7, 6]
  have r0 := holds_refl [9, 3, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule2006 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * normalizedRelatorError .viii_r3) [6, 3, 7, -9] [-7, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule2002 [3] [])) (holds_context c9_rule224 [] [-7, -9, 6]))
  have l0 := holds_refl [3, 6, 7, -9]
  have l1 := holds_trans l0 (holds_context c9_rule477 [] [7, -9])
  have r0 := holds_refl [-7, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule2009 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, 9, 3, -7] [9, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule2003 [6] [])) (holds_context c9_rule226 [] [9, 7, 6]))
  have l0 := holds_refl [6, 9, 3, -7]
  have r0 := holds_refl [9, 7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule2034 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ)) [3, 5, 6, 5, 7] [7, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1348 [-7] [])) (holds_context c9_rule13 [] [7, 6, 4]))
  have l0 := holds_refl [-7, 6, 4, 7, 7]
  have l1 := holds_trans l0 (holds_context c9_rule1667 [] [7])
  have r0 := holds_refl [7, 6, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule2036 : Holds ((normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 6, 5, 7] [6, 7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule2034 [3] [])) (holds_context c9_rule224 [] [5, 6, 5, 7]))
  have l0 := holds_refl [3, 7, 6, 4]
  have l1 := holds_trans l0 (holds_context c9_rule1167 [] [])
  have r0 := holds_refl [5, 6, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule2075 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-9, -7, 5, 4, -5] [-5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1387 [2] [])) (holds_context c9_rule179 [] [-5]))
  have l0 := holds_refl [2, -7, 2, 4]
  have l1 := holds_trans l0 (holds_context c9_rule247 [] [4])
  have r0 := holds_refl [-9, -7, 5, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule2077 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-7, 5, 4, -5] [9, -5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule2075 [9] [])) (holds_context c9_rule16 [] [-7, 5, 4, -5]))
  have l0 := holds_refl [9, -5, -9, 4]
  have r0 := holds_refl [-7, 5, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule2167 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-9, 3, 5, 2, 3] [2, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1478 [] [7])) (holds_context c9_rule254 [-9, 3] []))
  have l0 := holds_refl [2, -7, 5, 4, 7]
  have l1 := holds_trans l0 (holds_context c9_rule1646 [2] [])
  have l2 := holds_trans l1 (holds_context c9_rule43 [] [3, -5, 4])
  have l3 := holds_trans l2 (holds_context c9_rule618 [6] [])
  have l4 := holds_trans l3 (holds_context c9_rule2009 [] [2])
  have l5 := holds_trans l4 (holds_context c9_rule250 [] [])
  have r0 := holds_refl [-9, 3, 5, 2, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule2168 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-3 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [3, 5, 2, 3] [9, 2, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule2167 [9] [])) (holds_context c9_rule16 [] [3, 5, 2, 3]))
  have l0 := holds_refl [9, 2, 5, 6]
  have r0 := holds_refl [3, 5, 2, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule2203 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ)) [7, 5, 4, 5, 4] [7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule1497 [] [7])) (holds_context c9_rule428 [5, 6] []))
  have l0 := holds_refl [6, 5, 6, 5, 7]
  have l1 := holds_trans l0 (holds_context c9_rule2036 [6] [])
  have l2 := holds_trans l1 (holds_context c9_rule226 [] [7, 5, 5])
  have r0 := holds_refl [5, 6, 7, 5, 4]
  have r1 := holds_trans r0 (holds_context c9_rule428 [] [5, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule2204 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ)) [5, 4, 5, 4] [5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule2203 [-7] [])) (holds_context c9_rule13 [] [5, 4, 5, 4]))
  have l0 := holds_refl [-7, 7, 5, 5]
  have l1 := holds_trans l0 (holds_context c9_rule13 [] [5, 5])
  have r0 := holds_refl [5, 4, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
