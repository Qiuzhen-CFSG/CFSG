module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step27

/-! Kernel-checked central word identities, chunk 28.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c9_rule478 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [-5, 6, 3] [3, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule477 [-5] [])) (holds_context c9_rule31 [] [6]))
  have l0 := holds_refl [-5, 6, 3]
  have r0 := holds_refl [3, -5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule479 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [5, 6, 3] [3, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule477 [5] [])) (holds_context c9_rule32 [] [6]))
  have l0 := holds_refl [5, 6, 3]
  have r0 := holds_refl [3, 5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule480 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ)) [-7, 6, 3] [3, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule477 [-7] [])) (holds_context c9_rule33 [] [6]))
  have l0 := holds_refl [-7, 6, 3]
  have r0 := holds_refl [3, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule481 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .v_s3_s5) [3, -7, 5, 7] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule463 [-7] [])) (holds_context c9_rule13 [] [-5, 6]))
  have l0 := holds_refl [-7, 3, 5, 7]
  have l1 := holds_trans l0 (holds_context c9_rule33 [] [5, 7])
  have r0 := holds_refl [-5, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule482 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 6, -7] [3, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule481 [] [-7])) (holds_context c9_rule12 [3, -7, 5] []))
  have l0 := holds_refl [-5, 6, -7]
  have r0 := holds_refl [3, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule483 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .v_s3_s5) [-7, 5, 7] [3, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule481 [3] [])) (holds_context c9_rule224 [] [-7, 5, 7]))
  have l0 := holds_refl [3, -5, 6]
  have r0 := holds_refl [-7, 5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule485 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [5, 2, -5, 7] [6, 3, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule467 [] [2])) (holds_context c9_rule245 [5] []))
  have l0 := holds_refl [6, 3, -7, 2]
  have r0 := holds_refl [5, 2, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule489 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, 6, -7, -5] [3, -7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule472 [-7] [])) (holds_context c9_rule33 [] [5, -7]))
  have l0 := holds_refl [-7, 6, -7, -5]
  have r0 := holds_refl [3, -7, 5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule493 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 6, 7, 7] [3, -7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule481 [] [7, 7])) (holds_context c9_rule230 [3, -7, 5] []))
  have l0 := holds_refl [-5, 6, 7, 7]
  have r0 := holds_refl [3, -7, 5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule495 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s5_s4) [4, -7, 6, 7] [3, 5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule483 [-5] [])) (holds_context c9_rule320 [] [7]))
  have l0 := holds_refl [-5, 3, -5, 6]
  have l1 := holds_trans l0 (holds_context c9_rule31 [] [-5, 6])
  have l2 := holds_trans l1 (holds_context c9_rule27 [3] [6])
  have r0 := holds_refl [4, -7, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule501 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 3, 4] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule71 [] [3])) (holds_context c9_rule34 [6, 3, 7] []))
  have l0 := holds_refl [-9, 4, 9, 4, 3]
  have l1 := holds_trans l0 (holds_context c9_rule30 [-9, 4, 9] [])
  have r0 := holds_refl [6, 3, 7, 3, 7]
  have r1 := holds_trans r0 (holds_context c9_rule34 [6, 3] [7])
  have r2 := holds_trans r1 (holds_context c9_rule224 [6] [7, 7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c9_rule503 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [6, 7, 7, 4] [-9, 4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule501 [] [4])) (holds_context c9_rule225 [-9, 4, 9, 3] []))
  have l0 := holds_refl [6, 7, 7, 4]
  have r0 := holds_refl [-9, 4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule541 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [6, 3, 5, 5, 6] [3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule83 [4] [])) (holds_context c9_rule30 [] [5, 5, 4]))
  have l0 := holds_refl [4, 6, -7, 6, 7]
  have l1 := holds_trans l0 (holds_context c9_rule35 [] [-7, 6, 7])
  have l2 := holds_trans l1 (holds_context c9_rule495 [6] [])
  have r0 := holds_refl [3, 4, 5, 5, 4]
  have r1 := holds_trans r0 (holds_context c9_rule388 [3] [4])
  have r2 := holds_trans r1 (holds_context c9_rule104 [] [4])
  have r3 := holds_trans r2 (holds_context c9_rule449 [6] [])
  have r4 := holds_trans r3 (holds_context c9_rule226 [] [3, 5, 5])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r4)) (by central_nf)

theorem c9_rule542 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [3, 5, 5, 6] [6, 3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule541 [6] [])) (holds_context c9_rule226 [] [3, 5, 5, 6]))
  have l0 := holds_refl [6, 3, 5, 5]
  have r0 := holds_refl [3, 5, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule549 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 3, 5, 5, -7] [4, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule85 [] [3])) (holds_context c9_rule33 [5, 5, 6] []))
  have l0 := holds_refl [3, 4, -7, 6, 3]
  have l1 := holds_trans l0 (holds_context c9_rule480 [3, 4] [])
  have l2 := holds_trans l1 (holds_context c9_rule30 [3] [-7, 6])
  have l3 := holds_trans l2 (holds_context c9_rule224 [] [4, -7, 6])
  have r0 := holds_refl [5, 5, 6, 3, -7]
  have r1 := holds_trans r0 (holds_context c9_rule479 [5] [-7])
  have r2 := holds_trans r1 (holds_context c9_rule32 [] [5, 6, -7])
  have r3 := holds_trans r2 (holds_context c9_rule542 [] [-7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r3))) (by central_nf)

theorem c9_rule550 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 5, 5, -7] [6, 4, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule549 [6] [])) (holds_context c9_rule226 [] [3, 5, 5, -7]))
  have l0 := holds_refl [6, 4, -7, 6]
  have r0 := holds_refl [3, 5, 5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule569 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-7, 2, 3, 4, 5] [3, -9, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule91 [-7] [])) (holds_context c9_rule33 [] [7, -9, 2]))
  have l0 := holds_refl [-7, 2, 3, 4, 5]
  have r0 := holds_refl [3, -7, 7, -9, 2]
  have r1 := holds_trans r0 (holds_context c9_rule13 [3] [-9, 2])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule570 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-7, 2, 3, 4] [3, -9, 2, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule569 [] [-5])) (holds_context c9_rule8 [-7, 2, 3, 4] []))
  have l0 := holds_refl [3, -9, 2, -5]
  have r0 := holds_refl [-7, 2, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule598 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-9, 2, 3, -7, 2] [3, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule105 [] [2])) (holds_context c9_rule41 [3, -5, 2] []))
  have l0 := holds_refl [-9, 2, 3, -7, 2]
  have r0 := holds_refl [3, -5, 2, 2, 4]
  have r1 := holds_trans r0 (holds_context c9_rule223 [3, -5] [4])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule599 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 3, -7, 2] [9, 3, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule598 [9] [])) (holds_context c9_rule16 [] [2, 3, -7, 2]))
  have l0 := holds_refl [9, 3, -5, 4]
  have r0 := holds_refl [2, 3, -7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule616 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ)) [9, 2, -7, 5, 4] [3, -9, 2, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule223 [] [3, -9, 2, 3])) (holds_context c9_rule179 [2] []))
  have l0 := holds_refl [3, -9, 2, 3]
  have r0 := holds_refl [2, -9, -7, 5, 4]
  have r1 := holds_trans r0 (holds_context c9_rule45 [] [-7, 5, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule617 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-9, 2, 3, -5, 4] [3, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule224 [3, -7, 2] [])) (holds_context c9_rule98 [] [3]))
  have l0 := holds_refl [3, -7, 2]
  have r0 := holds_refl [-9, 2, -5, 4, 3]
  have r1 := holds_trans r0 (holds_context c9_rule30 [-9, 2, -5] [])
  have r2 := holds_trans r1 (holds_context c9_rule31 [-9, 2] [4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule618 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 3, -5, 4] [9, 3, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule617 [9] [])) (holds_context c9_rule16 [] [2, 3, -5, 4]))
  have l0 := holds_refl [9, 3, -7, 2]
  have r0 := holds_refl [2, 3, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule621 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [3, -9, 2, 3, -7] [-5, 2, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule224 [] [-5, 2, 8])) (holds_context c9_rule105 [3] []))
  have l0 := holds_refl [-5, 2, 8]
  have r0 := holds_refl [3, -9, 2, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule622 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-5, 2, 8, 7] [3, -9, 2, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule621 [] [7])) (holds_context c9_rule13 [3, -9, 2, 3] []))
  have l0 := holds_refl [-5, 2, 8, 7]
  have r0 := holds_refl [3, -9, 2, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule625 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 4, -7, 6, 5] [5, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule226 [5, 6, -7] [])) (holds_context c9_rule84 [] [6]))
  have l0 := holds_refl [5, 6, -7]
  have r0 := holds_refl [3, -5, 4, -7, 6]
  have r1 := holds_trans r0 (holds_context c9_rule403 [3] [])
  have r2 := holds_trans r1 (holds_context c9_rule550 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c9_rule626 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -7, 6, 5] [6, 5, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule625 [6] [])) (holds_context c9_rule226 [] [4, -7, 6, 5]))
  have l0 := holds_refl [6, 5, 6, -7]
  have r0 := holds_refl [4, -7, 6, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule628 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-9, 2, 8, -9, 8] [2, -7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule226 [] [2, -7, 6, 7])) (holds_context c9_rule97 [6] []))
  have l0 := holds_refl [2, -7, 6, 7]
  have r0 := holds_refl [6, 3, 7, 7, 2]
  have r1 := holds_trans r0 (holds_context c9_rule71 [] [2])
  have r2 := holds_trans r1 (holds_context c9_rule42 [-9, 4, 9] [])
  have r3 := holds_trans r2 (holds_context c9_rule242 [-9] [8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r3))) (by central_nf)

theorem c9_rule631 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [-9, 2, 3, -7, 8] [3, -5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule227 [3, -5, 2] [])) (holds_context c9_rule105 [] [8]))
  have l0 := holds_refl [3, -5, 2]
  have r0 := holds_refl [-9, 2, 3, -7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule632 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3) [2, 3, -7, 8] [9, 3, -5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule631 [9] [])) (holds_context c9_rule16 [] [2, 3, -7, 8]))
  have l0 := holds_refl [9, 3, -5, 2]
  have r0 := holds_refl [2, 3, -7, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule633 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, -7, 6, 7, 5] [3, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule229 [3, 4] [])) (holds_context c9_rule63 [] [5]))
  have l0 := holds_refl [3, 4, -5]
  have r0 := holds_refl [3, 8, 3, 8, 5]
  have r1 := holds_trans r0 (holds_context c9_rule104 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule634 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-7, 6, 7, 5] [6, 3, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule633 [6] [])) (holds_context c9_rule226 [] [-7, 6, 7, 5]))
  have l0 := holds_refl [6, 3, 4, -5]
  have r0 := holds_refl [-7, 6, 7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule854 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ)) [5, 6, 8, 3, 8] [-5, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule304 [5, 8, 3] [])) (holds_context c9_rule68 [] [6]))
  have l0 := holds_refl [5, 8, 3, 6, 8]
  have l1 := holds_trans l0 (holds_context c9_rule477 [5, 8] [8])
  have l2 := holds_trans l1 (holds_context c9_rule304 [5] [3, 8])
  have r0 := holds_refl [3, 3, -5, 4, 6]
  have r1 := holds_trans r0 (holds_context c9_rule224 [] [-5, 4, 6])
  have r2 := holds_trans r1 (holds_context c9_rule35 [-5] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c9_rule856 : Holds ((normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ)) [5, 6, 5, 5] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule854 [] [4])) (holds_context c9_rule391 [5, 6] []))
  have l0 := holds_refl [-5, 6, 4, 4]
  have l1 := holds_trans l0 (holds_context c9_rule225 [-5, 6] [])
  have r0 := holds_refl [5, 6, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule858 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ)) [5, 5, 6] [6, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule856 [-5] [])) (holds_context c9_rule9 [] [6, 5, 5]))
  have l0 := holds_refl [-5, -5, 6]
  have l1 := holds_trans l0 (holds_context c9_rule27 [] [6])
  have r0 := holds_refl [6, 5, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule859 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ)) [-5, 6, 5] [5, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule856 [] [5])) (holds_context c9_rule229 [5, 6] []))
  have l0 := holds_refl [-5, 6, 5]
  have r0 := holds_refl [5, 6, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule864 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, 5, 6, -5] [3, 5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule859 [7] [])) (holds_context c9_rule463 [] [5]))
  have l0 := holds_refl [7, 5, 6, -5]
  have r0 := holds_refl [3, 5, 7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule998 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 4, -7, 6, 2] [8, -5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule359 [] [6])) (holds_context c9_rule43 [2, 4, -7] []))
  have l0 := holds_refl [8, -5, -9, 6]
  have r0 := holds_refl [2, 4, -7, 6, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule1122 : Holds ((normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4) [8, -5, -9, 6] [-7, -9, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule405 [2] [])) (holds_context c9_rule49 [] [-5, 7]))
  have l0 := holds_refl [2, 4, -7, 6, 2]
  have l1 := holds_trans l0 (holds_context c9_rule998 [] [])
  have r0 := holds_refl [-7, -9, -5, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule1166 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 3, 7, 6, 4] [7, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule425 [] [4])) (holds_context c9_rule391 [7] []))
  have l0 := holds_refl [6, -5, 7, -5, 4]
  have l1 := holds_trans l0 (holds_context c9_rule454 [6] [4])
  have r0 := holds_refl [7, 5, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
