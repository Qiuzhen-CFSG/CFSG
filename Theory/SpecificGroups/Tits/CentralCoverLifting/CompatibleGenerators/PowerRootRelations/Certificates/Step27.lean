module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step26

/-! Kernel-checked central word identities, chunk 27.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c9_rule315 : Holds (normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [8, 5, 5] [3, 8, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule313 [3] [])) (holds_context c9_rule224 [] [8, 5, 5]))
  have l0 := holds_refl [3, 8, 4]
  have r0 := holds_refl [8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule318 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7, 5] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule224 [] [4, -5, -7, 5])) (holds_context c9_rule158 [3] []))
  have l0 := holds_refl [4, -5, -7, 5]
  have r0 := holds_refl [3, 3, -7, 6]
  have r1 := holds_trans r0 (holds_context c9_rule224 [] [-7, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule319 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -5, -7] [-7, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule318 [] [-5])) (holds_context c9_rule8 [4, -5, -7] []))
  have l0 := holds_refl [-7, 6, -5]
  have r0 := holds_refl [4, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule320 : Holds (normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -7, 5] [4, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule318 [4] [])) (holds_context c9_rule225 [] [-5, -7, 5]))
  have l0 := holds_refl [4, -7, 6]
  have r0 := holds_refl [-5, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule359 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 4, -7, 2] [8, -5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule247 [8] [])) (holds_context c9_rule41 [] [-7, 2]))
  have l0 := holds_refl [8, -5, -9]
  have r0 := holds_refl [2, 4, -7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule361 : Holds ((normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, -7, 6, 2] [-5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule247 [] [6])) (holds_context c9_rule43 [2, -7] []))
  have l0 := holds_refl [-5, -9, 6]
  have r0 := holds_refl [2, -7, 6, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule387 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6) [8, 3, 8, 5] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule314 [8] [])) (holds_context c9_rule227 [] [4, -5]))
  have l0 := holds_refl [8, 3, 8, 5]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule388 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [4, 5, 5] [8, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule387 [] [-5])) (holds_context c9_rule8 [8, 3, 8] []))
  have l0 := holds_refl [4, -5, -5]
  have l1 := holds_trans l0 (holds_context c9_rule27 [4] [])
  have r0 := holds_refl [8, 3, 8]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule391 : Holds (normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 8, 4] [5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule315 [8] [])) (holds_context c9_rule227 [] [5, 5]))
  have l0 := holds_refl [8, 3, 8, 4]
  have r0 := holds_refl [5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule395 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 6, -5, 7] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule319 [] [7])) (holds_context c9_rule13 [4, -5] []))
  have l0 := holds_refl [-7, 6, -5, 7]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule396 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 4, -5] [6, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule395 [7] [])) (holds_context c9_rule12 [] [6, -5, 7]))
  have l0 := holds_refl [7, 4, -5]
  have r0 := holds_refl [6, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule401 : Holds ((normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 4, -7, 6] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule320 [5] [])) (holds_context c9_rule8 [] [-7, 5]))
  have l0 := holds_refl [5, 4, -7, 6]
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule402 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 4, -7] [-7, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule401 [] [6])) (holds_context c9_rule226 [5, 4, -7] []))
  have l0 := holds_refl [-7, 5, 6]
  have r0 := holds_refl [5, 4, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule403 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [-5, 4, -7, 6] [5, 5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule320 [-5] [])) (holds_context c9_rule27 [] [-7, 5]))
  have l0 := holds_refl [-5, 4, -7, 6]
  have r0 := holds_refl [5, 5, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule405 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [-5, 2, -5, 7] [4, -7, 6, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule320 [] [2])) (holds_context c9_rule245 [-5] []))
  have l0 := holds_refl [4, -7, 6, 2]
  have r0 := holds_refl [-5, 2, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule425 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 8, 3, 8] [6, -5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule396 [] [-5])) (holds_context c9_rule27 [7, 4] []))
  have l0 := holds_refl [6, -5, 7, -5]
  have r0 := holds_refl [7, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c9_rule388 [7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c9_rule426 : Holds (normalizedRelatorError .ii_s1_s2) [3, 6, -5, 7] [6, 3, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule396 [] [3])) (holds_context c9_rule31 [7, 4] []))
  have l0 := holds_refl [6, -5, 7, 3]
  have l1 := holds_trans l0 (holds_context c9_rule34 [6, -5] [])
  have l2 := holds_trans l1 (holds_context c9_rule31 [6] [7])
  have r0 := holds_refl [7, 4, 3, -5]
  have r1 := holds_trans r0 (holds_context c9_rule30 [7] [-5])
  have r2 := holds_trans r1 (holds_context c9_rule34 [] [4, -5])
  have r3 := holds_trans r2 (holds_context c9_rule396 [3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r3))) (by central_nf)

theorem c9_rule427 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, 6, 7] [5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule402 [] [7])) (holds_context c9_rule13 [5, 4] []))
  have l0 := holds_refl [-7, 5, 6, 7]
  have r0 := holds_refl [5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule428 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 6, 7] [7, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule427 [7] [])) (holds_context c9_rule12 [] [5, 6, 7]))
  have l0 := holds_refl [7, 5, 4]
  have r0 := holds_refl [5, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule448 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [6, -7, 6, 7, 4] [3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule63 [4] [])) (holds_context c9_rule30 [] [4, 5, 5]))
  have l0 := holds_refl [4, 3, 8, 3, 8]
  have l1 := holds_trans l0 (holds_context c9_rule30 [] [8, 3, 8])
  have l2 := holds_trans l1 (holds_context c9_rule36 [3] [3, 8])
  have l3 := holds_trans l2 (holds_context c9_rule30 [3, 8] [8])
  have l4 := holds_trans l3 (holds_context c9_rule36 [3, 8, 3] [])
  have l5 := holds_trans l4 (holds_context c9_rule104 [] [4])
  have r0 := holds_refl [3, 4, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c9_rule225 [3] [5, 5])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r1)) (by central_nf)

theorem c9_rule449 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [-7, 6, 7, 4] [6, 3, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule448 [6] [])) (holds_context c9_rule226 [] [-7, 6, 7, 4]))
  have l0 := holds_refl [6, 3, 5, 5]
  have r0 := holds_refl [-7, 6, 7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule450 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, 3, -5, 7, -5] [6, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule63 [7] [])) (holds_context c9_rule34 [] [4, 5, 5]))
  have l0 := holds_refl [7, 3, 8, 3, 8]
  have l1 := holds_trans l0 (holds_context c9_rule34 [] [8, 3, 8])
  have l2 := holds_trans l1 (holds_context c9_rule425 [3] [])
  have l3 := holds_trans l2 (holds_context c9_rule426 [] [-5])
  have r0 := holds_refl [3, 7, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c9_rule80 [] [5])
  have r2 := holds_trans r1 (holds_context c9_rule9 [6, 7, 6] [])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r2)) (by central_nf)

theorem c9_rule452 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -5, 7, -5] [7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule450 [6] [])) (holds_context c9_rule226 [] [3, -5, 7, -5]))
  have l0 := holds_refl [6, 6, 7, 6]
  have l1 := holds_trans l0 (holds_context c9_rule226 [] [7, 6])
  have r0 := holds_refl [3, -5, 7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule453 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 6, 5] [3, -5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule452 [] [5])) (holds_context c9_rule9 [3, -5, 7] []))
  have l0 := holds_refl [7, 6, 5]
  have r0 := holds_refl [3, -5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule454 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 7, -5] [3, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule452 [3] [])) (holds_context c9_rule224 [] [-5, 7, -5]))
  have l0 := holds_refl [3, 7, 6]
  have r0 := holds_refl [-5, 7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule455 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -7, -5, 7] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule453 [-7] [])) (holds_context c9_rule13 [] [6, 5]))
  have l0 := holds_refl [-7, 3, -5, 7]
  have l1 := holds_trans l0 (holds_context c9_rule33 [] [-5, 7])
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule456 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -7, -5] [6, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule455 [] [-7])) (holds_context c9_rule12 [3, -7, -5] []))
  have l0 := holds_refl [6, 5, -7]
  have r0 := holds_refl [3, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule457 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, -5, 7] [3, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule455 [3] [])) (holds_context c9_rule224 [] [-7, -5, 7]))
  have l0 := holds_refl [3, 6, 5]
  have r0 := holds_refl [-7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule458 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 6, 3, 5] [-5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule453 [] [3])) (holds_context c9_rule32 [7, 6] []))
  have l0 := holds_refl [3, -5, 7, 3]
  have l1 := holds_trans l0 (holds_context c9_rule34 [3, -5] [])
  have l2 := holds_trans l1 (holds_context c9_rule31 [3] [7])
  have l3 := holds_trans l2 (holds_context c9_rule224 [] [-5, 7])
  have r0 := holds_refl [7, 6, 3, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule459 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ)) [7, 6, 3] [3, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule458 [] [-5])) (holds_context c9_rule8 [7, 6, 3] []))
  have l0 := holds_refl [-5, 7, -5]
  have l1 := holds_trans l0 (holds_context c9_rule454 [] [])
  have r0 := holds_refl [7, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule460 : Holds ((1 : C)) [3, 6, 5] [6, 3, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule458 [-7] [])) (holds_context c9_rule13 [] [6, 3, 5]))
  have l0 := holds_refl [-7, -5, 7]
  have l1 := holds_trans l0 (holds_context c9_rule457 [] [])
  have r0 := holds_refl [6, 3, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule461 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [3, 5, 7, 6] [7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule454 [5] [])) (holds_context c9_rule8 [] [7, -5]))
  have l0 := holds_refl [5, 3, 7, 6]
  have l1 := holds_trans l0 (holds_context c9_rule32 [] [7, 6])
  have r0 := holds_refl [7, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule462 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 7, 6] [3, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule461 [3] [])) (holds_context c9_rule224 [] [5, 7, 6]))
  have l0 := holds_refl [3, 7, -5]
  have r0 := holds_refl [5, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule463 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, 6] [3, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule461 [] [6])) (holds_context c9_rule226 [3, 5, 7] []))
  have l0 := holds_refl [7, -5, 6]
  have r0 := holds_refl [3, 5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule466 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, -7, 5] [3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule456 [] [5])) (holds_context c9_rule9 [3, -7] []))
  have l0 := holds_refl [6, 5, -7, 5]
  have r0 := holds_refl [3, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c9_rule467 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, 5] [6, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule466 [6] [])) (holds_context c9_rule226 [] [5, -7, 5]))
  have l0 := holds_refl [6, 3, -7]
  have r0 := holds_refl [5, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule468 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, -7, 5, 5] [6, 5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule456 [] [-5])) (holds_context c9_rule27 [3, -7] []))
  have l0 := holds_refl [6, 5, -7, -5]
  have r0 := holds_refl [3, -7, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule471 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 3, 5, -7] [-7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule456 [] [3])) (holds_context c9_rule31 [3, -7] []))
  have l0 := holds_refl [6, 5, -7, 3]
  have l1 := holds_trans l0 (holds_context c9_rule33 [6, 5] [])
  have l2 := holds_trans l1 (holds_context c9_rule32 [6] [-7])
  have r0 := holds_refl [3, -7, 3, -5]
  have r1 := holds_trans r0 (holds_context c9_rule33 [3] [-5])
  have r2 := holds_trans r1 (holds_context c9_rule224 [] [-7, -5])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r2)) (by central_nf)

theorem c9_rule472 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [3, 5, -7] [6, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule471 [6] [])) (holds_context c9_rule226 [] [3, 5, -7]))
  have l0 := holds_refl [6, -7, -5]
  have r0 := holds_refl [3, 5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c9_rule477 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ)) [3, 6] [6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c9_rule457 [] [-5])) (holds_context c9_rule454 [-7] []))
  have l0 := holds_refl [3, 6, 5, -5]
  have l1 := holds_trans l0 (holds_context c9_rule460 [] [-5])
  have l2 := holds_trans l1 (holds_context c9_rule8 [6, 3] [])
  have r0 := holds_refl [-7, 3, 7, 6]
  have r1 := holds_trans r0 (holds_context c9_rule33 [] [7, 6])
  have r2 := holds_trans r1 (holds_context c9_rule13 [3] [6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
