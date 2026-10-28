module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step33

/-! Kernel-checked central word identities, chunk 34.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c10_rule361 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ)) [8, 3, 8, 5] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule302 [8] [])) (holds_context c10_rule36 [] [8, -5]))
  have l0 := holds_refl [8, 3, 8, 5]
  have r0 := holds_refl [4, 8, 8, -5]
  have r1 := holds_trans r0 (holds_context c10_rule228 [4] [-5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule362 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ)) [8, 3, 8] [4, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule361 [] [-5])) (holds_context c10_rule8 [8, 3, 8] []))
  have l0 := holds_refl [4, -5, -5]
  have l1 := holds_trans l0 (holds_context c10_rule27 [4] [])
  have r0 := holds_refl [8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule363 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 3, 5, 5] [3, 4, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule303 [] [3])) (holds_context c10_rule32 [8, 5] []))
  have l0 := holds_refl [3, 4, 8, 3]
  have r0 := holds_refl [8, 5, 3, 5]
  have r1 := holds_trans r0 (holds_context c10_rule32 [8] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c10_rule366 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, -5, 7] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule310 [] [7])) (holds_context c10_rule13 [4, -5] []))
  have l0 := holds_refl [-7, 6, -5, 7]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule367 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [6, -5, 7] [7, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule366 [7] [])) (holds_context c10_rule12 [] [6, -5, 7]))
  have l0 := holds_refl [7, 4, -5]
  have r0 := holds_refl [6, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule377 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 5, 6] [4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule311 [] [6])) (holds_context c10_rule227 [4, -7] []))
  have l0 := holds_refl [-5, -7, 5, 6]
  have r0 := holds_refl [4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule378 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, 6] [5, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule377 [5] [])) (holds_context c10_rule8 [] [-7, 5, 6]))
  have l0 := holds_refl [5, 4, -7]
  have r0 := holds_refl [-7, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule381 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ)) [5, 4, 5, 5] [-5, 4] := by
  have h0 := c10_rule68
  have l0 := holds_refl [5, 8, 3, 8]
  have l1 := holds_trans l0 (holds_context c10_rule362 [5] [])
  have r0 := holds_refl [3, 3, -5, 4]
  have r1 := holds_trans r0 (holds_context c10_rule225 [] [-5, 4])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule383 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ)) [4, 5, 5] [5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule381 [-5] [])) (holds_context c10_rule9 [] [4, 5, 5]))
  have l0 := holds_refl [-5, -5, 4]
  have l1 := holds_trans l0 (holds_context c10_rule27 [] [4])
  have r0 := holds_refl [4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule388 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [5, 5, 4, 8] [8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule362 [] [8])) (holds_context c10_rule228 [8, 3] []))
  have l0 := holds_refl [4, 5, 5, 8]
  have l1 := holds_trans l0 (holds_context c10_rule383 [] [8])
  have r0 := holds_refl [8, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule389 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [-5, 8, 3] [5, 4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule388 [-5] [])) (holds_context c10_rule9 [] [5, 4, 8]))
  have l0 := holds_refl [-5, 8, 3]
  have r0 := holds_refl [5, 4, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule394 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 4, -5] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule367 [6] [])) (holds_context c10_rule227 [] [-5, 7]))
  have l0 := holds_refl [6, 7, 4, -5]
  have r0 := holds_refl [-5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule395 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 7, 4] [-5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule394 [] [5])) (holds_context c10_rule9 [6, 7, 4] []))
  have l0 := holds_refl [-5, 7, 5]
  have r0 := holds_refl [6, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule398 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 5, 4, -7] [5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule378 [7] [])) (holds_context c10_rule12 [] [5, 6]))
  have l0 := holds_refl [7, 5, 4, -7]
  have r0 := holds_refl [5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule399 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 5, 4] [5, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule398 [] [7])) (holds_context c10_rule13 [7, 5, 4] []))
  have l0 := holds_refl [5, 6, 7]
  have r0 := holds_refl [7, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule407 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 4, 6] [3, -7, 6, 7] := by
  have h0 := c10_rule86
  have l0 := holds_refl [4, 5, 5, 6]
  have l1 := holds_trans l0 (holds_context c10_rule383 [] [6])
  have r0 := holds_refl [3, -7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule409 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [5, 4, 8, 3] [-5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule389 [] [3])) (holds_context c10_rule225 [-5, 8] []))
  have l0 := holds_refl [5, 4, 8, 3]
  have r0 := holds_refl [-5, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule410 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [4, 8, 3] [5, 5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule409 [-5] [])) (holds_context c10_rule9 [] [4, 8, 3]))
  have l0 := holds_refl [-5, -5, 8]
  have l1 := holds_trans l0 (holds_context c10_rule27 [] [8])
  have r0 := holds_refl [4, 8, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule420 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ)) [3, 6, 3, 7] [6, 7] := by
  have h0 := c10_rule308
  have l0 := holds_refl [-5, 7, 5, 4]
  have l1 := holds_trans l0 (holds_context c10_rule399 [-5] [])
  have l2 := holds_trans l1 (holds_context c10_rule9 [] [6, 7])
  have r0 := holds_refl [3, 6, 3, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule421 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ)) [3, 6, 3] [6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule420 [] [-7])) (holds_context c10_rule12 [3, 6, 3] []))
  have l0 := holds_refl [6, 7, -7]
  have l1 := holds_trans l0 (holds_context c10_rule12 [6] [])
  have r0 := holds_refl [3, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule422 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ)) [6, 3] [3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule421 [3] [])) (holds_context c10_rule225 [] [6, 3]))
  have l0 := holds_refl [3, 6]
  have r0 := holds_refl [6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule423 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 3, 6] [6, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule422 [8] [])) (holds_context c10_rule285 [] [3]))
  have l0 := holds_refl [8, 3, 6]
  have r0 := holds_refl [6, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule492 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [3, -7, -5, 7, 5] [5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule86 [] [4])) (holds_context c10_rule35 [4, 5, 5] []))
  have l0 := holds_refl [3, -7, 6, 7, 4]
  have l1 := holds_trans l0 (holds_context c10_rule395 [3, -7] [])
  have r0 := holds_refl [4, 5, 5, 4, 6]
  have r1 := holds_trans r0 (holds_context c10_rule383 [] [4, 6])
  have r2 := holds_trans r1 (holds_context c10_rule226 [5, 5] [6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c10_rule493 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, 5, 6, -5] [3, -7, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule492 [] [-5])) (holds_context c10_rule8 [3, -7, -5, 7] []))
  have l0 := holds_refl [5, 5, 6, -5]
  have r0 := holds_refl [3, -7, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule494 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [-7, -5, 7, 5] [3, 5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule492 [3] [])) (holds_context c10_rule225 [] [-7, -5, 7, 5]))
  have l0 := holds_refl [3, 5, 5, 6]
  have r0 := holds_refl [-7, -5, 7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule529 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 9, 3, -5, 4] [3, -7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule98 [] [3])) (holds_context c10_rule30 [2, 9, -5] []))
  have l0 := holds_refl [3, -7, 2, 3, 3]
  have l1 := holds_trans l0 (holds_context c10_rule225 [3, -7, 2] [])
  have r0 := holds_refl [2, 9, -5, 3, 4]
  have r1 := holds_trans r0 (holds_context c10_rule31 [2, 9] [4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c10_rule531 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 9, 3, -5] [3, -7, 2, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule529 [] [4])) (holds_context c10_rule226 [2, 9, 3, -5] []))
  have l0 := holds_refl [3, -7, 2, 4]
  have r0 := holds_refl [2, 9, 3, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule550 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 3, -5, 2, 8] [2, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule104 [9] [])) (holds_context c10_rule45 [] [9, 3, -7]))
  have l0 := holds_refl [9, 3, -5, 2, 8]
  have r0 := holds_refl [2, -9, 9, 3, -7]
  have r1 := holds_trans r0 (holds_context c10_rule17 [2] [3, -7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule551 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [9, 3, -5, 2] [2, 3, -7, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule550 [] [8])) (holds_context c10_rule228 [9, 3, -5, 2] []))
  have l0 := holds_refl [2, 3, -7, 8]
  have r0 := holds_refl [9, 3, -5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule552 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, -7, -5, 2, 8] [2, 3, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule104 [-7] [])) (holds_context c10_rule53 [] [3, -7]))
  have l0 := holds_refl [-7, 3, -5, 2, 8]
  have l1 := holds_trans l0 (holds_context c10_rule33 [] [-5, 2, 8])
  have r0 := holds_refl [2, -5, 3, -7]
  have r1 := holds_trans r0 (holds_context c10_rule31 [2] [-7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule581 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [6, 5, 5] [5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule226 [6, 5, 5] [])) (holds_context c10_rule82 [] [4]))
  have l0 := holds_refl [6, 5, 5]
  have r0 := holds_refl [-7, 6, 3, 7, 4]
  have r1 := holds_trans r0 (holds_context c10_rule422 [-7] [7, 4])
  have r2 := holds_trans r1 (holds_context c10_rule33 [] [6, 7, 4])
  have r3 := holds_trans r2 (holds_context c10_rule395 [3, -7] [])
  have r4 := holds_trans r3 (holds_context c10_rule494 [3] [])
  have r5 := holds_trans r4 (holds_context c10_rule225 [] [5, 5, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r5)) (by central_nf)

theorem c10_rule583 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -7, -5, 7] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule581 [] [-5])) (holds_context c10_rule8 [6, 5] []))
  have l0 := holds_refl [5, 5, 6, -5]
  have l1 := holds_trans l0 (holds_context c10_rule493 [] [])
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule584 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, -7] [3, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule583 [] [-7])) (holds_context c10_rule12 [3, -7, -5] []))
  have l0 := holds_refl [6, 5, -7]
  have r0 := holds_refl [3, -7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule590 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 6, -7, -5] [5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule584 [6] [])) (holds_context c10_rule227 [] [5, -7]))
  have l0 := holds_refl [6, 3, -7, -5]
  have l1 := holds_trans l0 (holds_context c10_rule422 [] [-7, -5])
  have r0 := holds_refl [5, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c10_rule592 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, -7, -5] [3, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule590 [3] [])) (holds_context c10_rule225 [] [6, -7, -5]))
  have l0 := holds_refl [3, 5, -7]
  have r0 := holds_refl [6, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule625 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, 9, 3, 5, 5] [4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule226 [6, 9, 3, 5, 5] [])) (holds_context c10_rule131 [] [4]))
  have l0 := holds_refl [6, 9, 3, 5, 5]
  have r0 := holds_refl [4, 9, 4, 4]
  have r1 := holds_trans r0 (holds_context c10_rule226 [4, 9] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c10_rule627 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [9, 3, 5, 5] [4, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule625 [6] [])) (holds_context c10_rule227 [] [9, 3, 5, 5]))
  have l0 := holds_refl [6, 4, 9]
  have l1 := holds_trans l0 (holds_context c10_rule35 [] [9])
  have r0 := holds_refl [9, 3, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule882 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 8, -7, 6, 7] [3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule285 [] [-7, 6, 7])) (holds_context c10_rule83 [8] []))
  have l0 := holds_refl [6, 8, -7, 6, 7]
  have r0 := holds_refl [8, 3, 5, 5, 4]
  have r1 := holds_trans r0 (holds_context c10_rule363 [] [4])
  have r2 := holds_trans r1 (holds_context c10_rule410 [3] [4])
  have r3 := holds_trans r2 (holds_context c10_rule36 [3, 5, 5] [])
  have r4 := holds_trans r3 (holds_context c10_rule388 [3] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem c10_rule884 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [8, -7, 6, 7] [3, 6, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule882 [6] [])) (holds_context c10_rule227 [] [8, -7, 6, 7]))
  have l0 := holds_refl [6, 3, 8, 3]
  have l1 := holds_trans l0 (holds_context c10_rule422 [] [8, 3])
  have r0 := holds_refl [8, -7, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c10_rule1044 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, -7, 6, 7, 5] [4, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c10_rule360 [8] [])) (holds_context c10_rule285 [] [3, 8, 5]))
  have l0 := holds_refl [8, 10, 4, 10, -5]
  have l1 := holds_trans l0 (holds_context c10_rule321 [] [4, 10, -5])
  have l2 := holds_trans l1 (holds_context c10_rule36 [10] [10, -5])
  have l3 := holds_trans l2 (holds_context c10_rule321 [10, 4] [-5])
  have l4 := holds_trans l3 (holds_context c10_rule58 [10] [-5])
  have l5 := holds_trans l4 (holds_context c10_rule229 [] [4, 6, -5])
  have r0 := holds_refl [6, 8, 3, 8, 5]
  have r1 := holds_trans r0 (holds_context c10_rule362 [6] [5])
  have r2 := holds_trans r1 (holds_context c10_rule35 [] [5, 5, 5])
  have r3 := holds_trans r2 (holds_context c10_rule581 [4] [5])
  have r4 := holds_trans r3 (holds_context c10_rule383 [] [6, 5])
  have r5 := holds_trans r4 (holds_context c10_rule407 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r5))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
