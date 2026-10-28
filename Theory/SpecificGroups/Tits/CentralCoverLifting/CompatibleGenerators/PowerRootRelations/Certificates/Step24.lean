module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step23

/-! Kernel-checked central word identities, chunk 24.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c7_rule319 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, 5, 6, -5] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule317 [] [-5])) (holds_context c7_rule8 [6, 5] []))
  have l0 := holds_refl [5, 5, 6, -5]
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule321 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [-5, 6, -5] [5, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule319 [5] [])) (holds_context c7_rule134 [] [6, -5]))
  have l0 := holds_refl [5, 6, 5]
  have r0 := holds_refl [-5, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule328 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [7, 5, 6, 5] [5, 5, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule321 [7] [])) (holds_context c7_rule290 [] [-5]))
  have l0 := holds_refl [7, 5, 6, 5]
  have r0 := holds_refl [5, 7, 3, -5]
  have r1 := holds_trans r0 (holds_context c7_rule29 [5, 7] [])
  have r2 := holds_trans r1 (holds_context c7_rule248 [5] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c7_rule335 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [4, 9, 8, 3, 8] [6, 9, 3, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule106 [] [-5])) (holds_context c7_rule8 [6, 9, 3, 4] []))
  have l0 := holds_refl [4, 9, 4, -5, -5]
  have l1 := holds_trans l0 (holds_context c7_rule25 [4, 9, 4] [])
  have l2 := holds_trans l1 (holds_context c7_rule153 [4, 9] [])
  have r0 := holds_refl [6, 9, 3, 4]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule342 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [9, 8, 3, 8, 3] [6, 4, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule131 [] [9, -7, 6, 7, 6])) (holds_context c7_rule89 [6] []))
  have l0 := holds_refl [9, -7, 6, 7, 6]
  have l1 := holds_trans l0 (holds_context c7_rule169 [9] [])
  have r0 := holds_refl [6, 4, 9, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule481 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [3, 4, -9, 6, 4] [7, 7, 6, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule238 [] [6])) (holds_context c7_rule33 [3, 4, -9] []))
  have l0 := holds_refl [7, 7, 6, -9, 6]
  have r0 := holds_refl [3, 4, -9, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule621 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 7, 5, -9, 4] [8, 3, 8, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule295 [] [-9])) (holds_context c7_rule277 [6] []))
  have l0 := holds_refl [8, 3, 8, -7, -9]
  have r0 := holds_refl [6, 7, 4, -9, 4]
  have r1 := holds_trans r0 (holds_context c7_rule208 [] [-9, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule653 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -7, 5, 5, 6] [-5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule317 [4, -7] [])) (holds_context c7_rule165 [] [5, 5]))
  have l0 := holds_refl [4, -7, 5, 5, 6]
  have r0 := holds_refl [-5, -7, 5, 5, 5]
  have r1 := holds_trans r0 (holds_context c7_rule134 [-5, -7] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c7_rule654 : Holds ((normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -7, 5, 5] [-5, -7, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule653 [] [6])) (holds_context c7_rule131 [4, -7, 5, 5] []))
  have l0 := holds_refl [-5, -7, -5, 6]
  have r0 := holds_refl [4, -7, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule674 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [7, 5, -7, -5, 7] [5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule328 [] [3])) (holds_context c7_rule268 [7, 5] []))
  have l0 := holds_refl [5, 5, 7, 6, 3]
  have l1 := holds_trans l0 (holds_context c7_rule258 [5, 5] [])
  have l2 := holds_trans l1 (holds_context c7_rule8 [5] [7, -5])
  have r0 := holds_refl [7, 5, -7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule675 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [7, 5, -7, -5] [5, 7, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule674 [] [-7])) (holds_context c7_rule12 [7, 5, -7, -5] []))
  have l0 := holds_refl [5, 7, -5, -7]
  have r0 := holds_refl [7, 5, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule692 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [-9, 6, 4, 9, 4] [8, 3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule342 [-9] [])) (holds_context c7_rule17 [] [8, 3, 8, 3]))
  have l0 := holds_refl [-9, 6, 4, 9, 4]
  have r0 := holds_refl [8, 3, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule784 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -7, 8, 3, 8] [-5, -7, -5, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule654 [] [4])) (holds_context c7_rule157 [4, -7] []))
  have l0 := holds_refl [-5, -7, -5, 6, 4]
  have r0 := holds_refl [4, -7, 8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule806 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [-9, 6, 4, 9] [5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule692 [] [4])) (holds_context c7_rule130 [-9, 6, 4, 9] []))
  have l0 := holds_refl [8, 3, 8, 3, 4]
  have l1 := holds_trans l0 (holds_context c7_rule185 [8] [])
  have l2 := holds_trans l1 (holds_context c7_rule132 [] [5, 5, 3])
  have r0 := holds_refl [-9, 6, 4, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule808 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [5, 5, 3, -9] [-9, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule806 [] [-9])) (holds_context c7_rule16 [-9, 6, 4] []))
  have l0 := holds_refl [5, 5, 3, -9]
  have r0 := holds_refl [-9, 6, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule810 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [-5, -9, 6, 4] [5, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule808 [-5] [])) (holds_context c7_rule9 [] [5, 3, -9]))
  have l0 := holds_refl [-5, -9, 6, 4]
  have r0 := holds_refl [5, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule813 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [5, 3, -9, 4] [-5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule810 [] [4])) (holds_context c7_rule130 [-5, -9, 6] []))
  have l0 := holds_refl [5, 3, -9, 4]
  have r0 := holds_refl [-5, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule817 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [5, 5, -9, 6] [3, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule813 [-5] [])) (holds_context c7_rule9 [] [3, -9, 4]))
  have l0 := holds_refl [-5, -5, -9, 6]
  have l1 := holds_trans l0 (holds_context c7_rule25 [] [-9, 6])
  have r0 := holds_refl [3, -9, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule822 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [3, -9, 6, 4] [5, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule817 [] [6])) (holds_context c7_rule131 [5, 5, -9] []))
  have l0 := holds_refl [3, -9, 4, 6]
  have l1 := holds_trans l0 (holds_context c7_rule33 [3, -9] [])
  have r0 := holds_refl [5, 5, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule823 : Holds (normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [5, 5, -9, 4] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule822 [] [4])) (holds_context c7_rule130 [3, -9, 6] []))
  have l0 := holds_refl [5, 5, -9, 4]
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule824 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [-5, 3, -9, 6] [5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule823 [-5] [])) (holds_context c7_rule9 [] [5, -9, 4]))
  have l0 := holds_refl [-5, 3, -9, 6]
  have r0 := holds_refl [5, -9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule920 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [7, 7, 6, -9, 6] [8, 3, 8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule822 [4] [])) (holds_context c7_rule28 [] [-9, 6, 4]))
  have l0 := holds_refl [4, 5, 5, -9]
  have l1 := holds_trans l0 (holds_context c7_rule153 [] [-9])
  have r0 := holds_refl [3, 4, -9, 6, 4]
  have r1 := holds_trans r0 (holds_context c7_rule481 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c7_rule932 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 6, -9, 6] [7, 5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule824 [7] [])) (holds_context c7_rule248 [] [-9, 6]))
  have l0 := holds_refl [7, 5, -9, 4]
  have r0 := holds_refl [5, 7, 6, -9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule991 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4) [-7, 8, 3, 8, -9] [7, 6, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule920 [-7] [])) (holds_context c7_rule13 [] [7, 6, -9, 6]))
  have l0 := holds_refl [-7, 8, 3, 8, -9]
  have r0 := holds_refl [7, 6, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule1000 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * normalizedRelatorError .v_s7_s4) [8, 3, 8, -7, -9] [7, 6, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule932 [-5] [])) (holds_context c7_rule9 [] [7, 6, -9, 6]))
  have l0 := holds_refl [-5, 7, 5, -9, 4]
  have l1 := holds_trans l0 (holds_context c7_rule621 [] [])
  have r0 := holds_refl [7, 6, -9, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule1041 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [7, 6, -9, 6, 9] [-7, 8, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule991 [] [9])) (holds_context c7_rule17 [-7, 8, 3, 8] []))
  have l0 := holds_refl [7, 6, -9, 6, 9]
  have r0 := holds_refl [-7, 8, 3, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule1046 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ)) [-7, 8, 3, 8] [8, 3, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule1000 [] [9])) (holds_context c7_rule17 [8, 3, 8, -7] []))
  have l0 := holds_refl [7, 6, -9, 6, 9]
  have l1 := holds_trans l0 (holds_context c7_rule1041 [] [])
  have r0 := holds_refl [8, 3, 8, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c7_rule1093 : Holds ((normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [-5, -7, -5, 6, 4] [5, 5, -7] := by
  have h0 := c7_rule784
  have l0 := holds_refl [4, -7, 8, 3, 8]
  have l1 := holds_trans l0 (holds_context c7_rule1046 [4] [])
  have l2 := holds_trans l1 (holds_context c7_rule34 [] [3, 8, -7])
  have l3 := holds_trans l2 (holds_context c7_rule28 [8] [8, -7])
  have l4 := holds_trans l3 (holds_context c7_rule34 [8, 3] [-7])
  have l5 := holds_trans l4 (holds_context c7_rule156 [8] [-7])
  have l6 := holds_trans l5 (holds_context c7_rule132 [] [5, 5, -7])
  have r0 := holds_refl [-5, -7, -5, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule1094 : Holds ((normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4) [-7, -5, 6, 4] [-5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule1093 [5] [])) (holds_context c7_rule8 [] [-7, -5, 6, 4]))
  have l0 := holds_refl [5, 5, 5, -7]
  have l1 := holds_trans l0 (holds_context c7_rule134 [] [-7])
  have r0 := holds_refl [-7, -5, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c7_rule1095 : Holds ((normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, -5, -7] [-5, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule1094 [7] [])) (holds_context c7_rule12 [] [-5, 6, 4]))
  have l0 := holds_refl [7, -5, -7]
  have r0 := holds_refl [-5, 6, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem equation_r7_0 : (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) = 1 := by
  have h0 := (split [-4, 3] [4, -3] (rotate [-3] [-4, 3, 4] source10))
  have l0 := holds_refl [-4, 3]
  have l1 := holds_trans l0 (holds_context c7_rule21 [] [3])
  have l2 := holds_trans l1 (holds_context c7_rule28 [] [])
  have r0 := holds_refl [3, -4]
  have r1 := holds_trans r0 (holds_context c7_rule21 [3] [])
  have hh : Holds ((normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ)) [3, 4] [3, 4] := holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_1037 : (normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule342 [4] [])) (holds_context c7_rule335 [] [3]))
  have l0 := holds_refl [4, 6, 4, 9, 4]
  have l1 := holds_trans l0 (holds_context c7_rule33 [] [4, 9, 4])
  have l2 := holds_trans l1 (holds_context c7_rule130 [6] [9, 4])
  have r0 := holds_refl [6, 9, 3, 4, 3]
  have r1 := holds_trans r0 (holds_context c7_rule28 [6, 9, 3] [])
  have r2 := holds_trans r1 (holds_context c7_rule129 [6, 9] [4])
  have hh : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ)) [6, 9, 4] [6, 9, 4] := holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_12 : (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) = 1 := by
  have h0 := (split [-6, 4] [6, -4] (rotate [-4] [-6, 4, 6] source16))
  have l0 := holds_refl [-6, 4]
  have l1 := holds_trans l0 (holds_context c7_rule22 [] [4])
  have r0 := holds_refl [4, -6]
  have r1 := holds_trans r0 (holds_context c7_rule22 [4] [])
  have r2 := holds_trans r1 (holds_context c7_rule33 [] [])
  have hh : Holds ((normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ)) [6, 4] [6, 4] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_12570 : (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule675 [] [8, 4])) (holds_context c7_rule159 [7, 5, -7] []))
  have l0 := holds_refl [5, 7, -5, -7, 8, 4]
  have l1 := holds_trans l0 (holds_context c7_rule1095 [5] [8, 4])
  have l2 := holds_trans l1 (holds_context c7_rule8 [] [6, 4, 8, 4])
  have l3 := holds_trans l2 (holds_context c7_rule34 [6] [4])
  have l4 := holds_trans l3 (holds_context c7_rule145 [] [4, 4])
  have l5 := holds_trans l4 (holds_context c7_rule130 [8, 6] [])
  have r0 := holds_refl [7, 5, -7, 5, 8, 3]
  have r1 := holds_trans r0 (holds_context c7_rule271 [] [8, 3])
  have r2 := holds_trans r1 (holds_context c7_rule1095 [-5] [8, 3])
  have r3 := holds_trans r2 (holds_context c7_rule25 [] [6, 4, 8, 3])
  have r4 := holds_trans r3 (holds_context c7_rule188 [] [8, 3])
  have r5 := holds_trans r4 (holds_context c7_rule266 [8] [8, 3])
  have r6 := holds_trans r5 (holds_context c7_rule132 [8, 6, 3] [3])
  have r7 := holds_trans r6 (holds_context c7_rule129 [8, 6] [])
  have hh : Holds ((normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [8, 6] [8, 6] := holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r7)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_145 : (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule49 [4] [])) (holds_context c7_rule33 [] [7, 7, 3]))
  have l0 := holds_refl [4, -9, 4, 9, 4]
  have l1 := holds_trans l0 (holds_context c7_rule53 [] [4])
  have r0 := holds_refl [6, 4, 7, 7, 3]
  have r1 := holds_trans r0 (holds_context c7_rule52 [6] [])
  have r2 := holds_trans r1 (holds_context c7_rule56 [] [6])
  have r3 := holds_trans r2 (holds_context c7_rule33 [7, 7, 3] [])
  have hh : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ)) [7, 7, 3, 6, 4] [7, 7, 3, 6, 4] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_16 : (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) = 1 := by
  have h0 := (split [-8, 4] [8, -4] (rotate [-4] [-8, 4, 8] source17))
  have l0 := holds_refl [-8, 4]
  have l1 := holds_trans l0 (holds_context c7_rule23 [] [4])
  have r0 := holds_refl [4, -8]
  have r1 := holds_trans r0 (holds_context c7_rule23 [4] [])
  have r2 := holds_trans r1 (holds_context c7_rule34 [] [])
  have hh : Holds ((normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ)) [8, 4] [8, 4] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_276 : (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule145 [4, 5, 5] [])) (holds_context c7_rule64 [] [8]))
  have l0 := holds_refl [4, 5, 5, 8, 6]
  have l1 := holds_trans l0 (holds_context c7_rule153 [] [8, 6])
  have l2 := holds_trans l1 (holds_context c7_rule132 [8, 3] [6])
  have l3 := holds_trans l2 (holds_context c7_rule264 [8] [])
  have r0 := holds_refl [-7, 3, 6, 7, 8]
  have r1 := holds_trans r0 (holds_context c7_rule264 [-7] [7, 8])
  have r2 := holds_trans r1 (holds_context c7_rule32 [-7, 6] [8])
  have r3 := holds_trans r2 (holds_context c7_rule187 [] [8])
  have r4 := holds_trans r3 (holds_context c7_rule132 [8, 6, 3] [])
  have hh : Holds ((normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [8, 6, 3] [8, 6, 3] := holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r4)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_684 : (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule263 [-7, 5] [])) (holds_context c7_rule212 [] [3]))
  have l0 := holds_refl [-7, 5, 6]
  have l1 := holds_trans l0 (holds_context c7_rule203 [] [])
  have r0 := holds_refl [5, 3, 4, -7, 3]
  have r1 := holds_trans r0 (holds_context c7_rule139 [5, 3] [])
  have r2 := holds_trans r1 (holds_context c7_rule129 [5] [4, -7])
  have hh : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ)) [5, 4, -7] [5, 4, -7] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)
  exact holds_cancel hh

theorem equation_r7_78 : (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c7_rule154 [4] [])) (holds_context c7_rule28 [] [8, -5]))
  have l0 := holds_refl [4, 8, 4, 5]
  have l1 := holds_trans l0 (holds_context c7_rule34 [] [4, 5])
  have l2 := holds_trans l1 (holds_context c7_rule130 [8] [5])
  have r0 := holds_refl [3, 4, 8, -5]
  have r1 := holds_trans r0 (holds_context c7_rule34 [3] [-5])
  have r2 := holds_trans r1 (holds_context c7_rule156 [] [-5])
  have r3 := holds_trans r2 (holds_context c7_rule8 [8, 5] [])
  have hh : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ)) [8, 5] [8, 5] := holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r3)) (by central_nf)
  exact holds_cancel hh

theorem c9_rule2 : Holds ((1 : C)) [2, -2] [] := by
  have h0 := (show Holds 1 [2, -2] [] by simp [Holds, value, letter, numbered])
  have l0 := holds_refl [2, -2]
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
