module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step15

/-! Kernel-checked central word identities, chunk 16.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule341 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 5, 3, -7] [-7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule328 [] [3])) (holds_context c6_rule32 [6, 5] []))
  have l0 := holds_refl [3, -7, -5, 3]
  have l1 := holds_trans l0 (holds_context c6_rule180 [3] [])
  have l2 := holds_trans l1 (holds_context c6_rule170 [] [-7, -5])
  have r0 := holds_refl [6, 5, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule343 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, -7, -5] [5, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule341 [6] [])) (holds_context c6_rule172 [] [5, 3, -7]))
  have l0 := holds_refl [6, -7, -5]
  have r0 := holds_refl [5, 3, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule345 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, 3, -7, -5] [5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule328 [6] [])) (holds_context c6_rule172 [] [5, -7]))
  have l0 := holds_refl [6, 3, -7, -5]
  have r0 := holds_refl [5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule346 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, 3, -7] [5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule345 [] [5])) (holds_context c6_rule9 [6, 3, -7] []))
  have l0 := holds_refl [5, -7, 5]
  have r0 := holds_refl [6, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule349 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, 7, -5, 7] [3, -7, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule329 [-7] [])) (holds_context c6_rule27 [] [-5, 7]))
  have l0 := holds_refl [-7, 3, 6, 5]
  have l1 := holds_trans l0 (holds_context c6_rule32 [] [6, 5])
  have r0 := holds_refl [7, 7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule350 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 3, 6, -7] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule333 [] [-7])) (holds_context c6_rule12 [-7, 5] []))
  have l0 := holds_refl [-5, 3, 6, -7]
  have r0 := holds_refl [-7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule351 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 6, -7] [5, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule350 [5] [])) (holds_context c6_rule8 [] [3, 6, -7]))
  have l0 := holds_refl [5, -7, 5]
  have r0 := holds_refl [3, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule353 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [-5, 3, 6, 3] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule333 [] [3])) (holds_context c6_rule33 [-7, 5] []))
  have l0 := holds_refl [-5, 3, 6, 3]
  have r0 := holds_refl [-7, 5, 3, 7]
  have r1 := holds_trans r0 (holds_context c6_rule181 [] [7])
  have r2 := holds_trans r1 (holds_context c6_rule333 [3] [])
  have r3 := holds_trans r2 (holds_context c6_rule30 [] [3, 6])
  have r4 := holds_trans r3 (holds_context c6_rule170 [-5] [6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem c6_rule354 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [3, 6, 3] [6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule353 [5] [])) (holds_context c6_rule8 [] [3, 6, 3]))
  have l0 := holds_refl [5, -5, 6]
  have l1 := holds_trans l0 (holds_context c6_rule8 [] [6])
  have r0 := holds_refl [3, 6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule355 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ)) [6, 3] [3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule354 [3] [])) (holds_context c6_rule170 [] [6, 3]))
  have l0 := holds_refl [3, 6]
  have r0 := holds_refl [6, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule358 : Holds ((normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6) [10, 3, 6] [6, 10, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule355 [10] [])) (holds_context c6_rule224 [] [3]))
  have l0 := holds_refl [10, 3, 6]
  have r0 := holds_refl [6, 10, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule364 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [5, 3, -7, 5] [6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule343 [] [5])) (holds_context c6_rule9 [6, -7] []))
  have l0 := holds_refl [5, 3, -7, 5]
  have r0 := holds_refl [6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule365 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s3_s5) [3, -7, 5] [-5, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule364 [-5] [])) (holds_context c6_rule9 [] [3, -7, 5]))
  have l0 := holds_refl [-5, 6, -7]
  have r0 := holds_refl [3, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule370 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 6, 7, 7] [5, -7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule346 [] [-7])) (holds_context c6_rule27 [6, 3] []))
  have l0 := holds_refl [5, -7, 5, -7]
  have r0 := holds_refl [6, 3, 7, 7]
  have r1 := holds_trans r0 (holds_context c6_rule355 [] [7, 7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule375 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, 5, -7, 5] [3, -7, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule351 [-7] [])) (holds_context c6_rule32 [] [6, -7]))
  have l0 := holds_refl [-7, 5, -7, 5]
  have r0 := holds_refl [3, -7, 6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule377 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [4, 9, 3, 6] [9, 4, 7, 7] := by
  have h0 := c6_rule56
  have l0 := holds_refl [4, 9, 6, 3]
  have l1 := holds_trans l0 (holds_context c6_rule355 [4, 9] [])
  have r0 := holds_refl [9, 4, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule387 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [6, 5, 5] [5, 5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule64 [-7] [])) (holds_context c6_rule13 [] [6, 5, 5]))
  have l0 := holds_refl [-7, 6, 3, 7, 4]
  have l1 := holds_trans l0 (holds_context c6_rule355 [-7] [7, 4])
  have l2 := holds_trans l1 (holds_context c6_rule32 [] [6, 7, 4])
  have l3 := holds_trans l2 (holds_context c6_rule264 [] [4])
  have l4 := holds_trans l3 (holds_context c6_rule171 [5, 5, 6] [])
  have r0 := holds_refl [6, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule388 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, 5, 6, -5] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule387 [] [-5])) (holds_context c6_rule8 [6, 5] []))
  have l0 := holds_refl [5, 5, 6, -5]
  have r0 := holds_refl [6, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule389 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [-5, 6, 5] [5, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule388 [-5] [])) (holds_context c6_rule9 [] [5, 6, -5]))
  have l0 := holds_refl [-5, 6, 5]
  have r0 := holds_refl [5, 6, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule400 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 5, 6, 4, -7] [3, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule65 [] [-7])) (holds_context c6_rule12 [-7, 6, 3] []))
  have l0 := holds_refl [6, 5, 5, 4, -7]
  have l1 := holds_trans l0 (holds_context c6_rule387 [] [4, -7])
  have r0 := holds_refl [-7, 6, 3]
  have r1 := holds_trans r0 (holds_context c6_rule355 [-7] [])
  have r2 := holds_trans r1 (holds_context c6_rule32 [] [6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule401 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [-5, 3, -7, 6] [5, 6, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule400 [-5] [])) (holds_context c6_rule9 [] [5, 6, 4, -7]))
  have l0 := holds_refl [-5, 3, -7, 6]
  have r0 := holds_refl [5, 6, 4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule407 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .v_s5_s4) [5, 5, 3, 4, -7] [6, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule66 [] [-7])) (holds_context c6_rule12 [6, -7, 6] []))
  have l0 := holds_refl [5, 5, 3, 4, -7]
  have r0 := holds_refl [6, -7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule421 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [3, 4, 7, 7, 6] [-9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule171 [] [-9, 4, 9])) (holds_context c6_rule58 [4] []))
  have l0 := holds_refl [-9, 4, 9]
  have r0 := holds_refl [4, 3, 7, 7, 6]
  have r1 := holds_trans r0 (holds_context c6_rule29 [] [7, 7, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule422 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [4, 7, 7, 6] [3, -9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule421 [3] [])) (holds_context c6_rule170 [] [4, 7, 7, 6]))
  have l0 := holds_refl [3, -9, 4, 9]
  have r0 := holds_refl [4, 7, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule423 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-5, 7, -5, -9, 4] [-7, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule176 [] [4, -9])) (holds_context c6_rule60 [7] []))
  have l0 := holds_refl [-7, 4, -9]
  have r0 := holds_refl [7, 3, 6, -9, 4]
  have r1 := holds_trans r0 (holds_context c6_rule33 [] [6, -9, 4])
  have r2 := holds_trans r1 (holds_context c6_rule336 [] [-9, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem c6_rule424 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, -9, 4] [5, -7, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule423 [5] [])) (holds_context c6_rule8 [] [7, -5, -9, 4]))
  have l0 := holds_refl [5, -7, 4, -9]
  have r0 := holds_refl [7, -5, -9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule539 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [9, 5, -7, 5, -7] [4, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule293 [] [-7])) (holds_context c6_rule12 [4, 9, 4] []))
  have l0 := holds_refl [9, 6, 3, -7, -7]
  have l1 := holds_trans l0 (holds_context c6_rule355 [9] [-7, -7])
  have l2 := holds_trans l1 (holds_context c6_rule351 [9] [-7])
  have r0 := holds_refl [4, 9, 4]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule546 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 5, 3] [6, 7, 7, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule297 [] [5])) (holds_context c6_rule31 [-9, 4, 9] []))
  have l0 := holds_refl [6, 7, 7, 4, 5]
  have r0 := holds_refl [-9, 4, 9, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule560 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 4, 5, 7, -5] [5, 5, 4, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule325 [5, 5, 4] [])) (holds_context c6_rule235 [] [3, 7, -5]))
  have l0 := holds_refl [5, 5, 4, 7, 6]
  have r0 := holds_refl [4, 5, 3, 7, -5]
  have r1 := holds_trans r0 (holds_context c6_rule179 [] [7, -5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule654 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 5, 5, 4, -7] [3, -7, 6, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule375 [] [6])) (holds_context c6_rule259 [-7, 5] []))
  have l0 := holds_refl [3, -7, 6, -7, 6]
  have r0 := holds_refl [-7, 5, 5, 4, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule656 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ)) [9, 3, -9, 4, 9] [4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule377 [] [6])) (holds_context c6_rule172 [4, 9, 3] []))
  have l0 := holds_refl [9, 4, 7, 7, 6]
  have l1 := holds_trans l0 (holds_context c6_rule422 [9] [])
  have r0 := holds_refl [4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule658 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [6, 7, 7, 4] [3, -9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule656 [-9] [])) (holds_context c6_rule17 [] [3, -9, 4, 9]))
  have l0 := holds_refl [-9, 4, 9, 3]
  have l1 := holds_trans l0 (holds_context c6_rule297 [] [])
  have r0 := holds_refl [3, -9, 4, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule674 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [4, -7, 5, 5, 6] [-5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule387 [4, -7] [])) (holds_context c6_rule215 [] [5, 5]))
  have l0 := holds_refl [4, -7, 5, 5, 6]
  have r0 := holds_refl [-5, -7, 5, 5, 5]
  have r1 := holds_trans r0 (holds_context c6_rule175 [-5, -7] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule696 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [-5, 3, -7, 1, 8] [5, 6, 4, -7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule401 [] [1])) (holds_context c6_rule39 [-5, 3, -7] []))
  have l0 := holds_refl [5, 6, 4, -7, 1]
  have r0 := holds_refl [-5, 3, -7, 1, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule813 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [-5, -7, -5, 4, -7] [-9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule674 [] [4, -7])) (holds_context c6_rule400 [4, -7] []))
  have l0 := holds_refl [-5, -7, -5, 4, -7]
  have r0 := holds_refl [4, -7, 3, -7, 6]
  have r1 := holds_trans r0 (holds_context c6_rule32 [4] [-7, 6])
  have r2 := holds_trans r1 (holds_context c6_rule29 [] [-7, -7, 6])
  have r3 := holds_trans r2 (holds_context c6_rule27 [3, 4] [6])
  have r4 := holds_trans r3 (holds_context c6_rule422 [3] [])
  have r5 := holds_trans r4 (holds_context c6_rule170 [] [-9, 4, 9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r5)) (by central_nf)

theorem c6_rule814 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [-7, -5, 4, -7] [5, -9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule813 [5] [])) (holds_context c6_rule8 [] [-7, -5, 4, -7]))
  have l0 := holds_refl [5, -9, 4, 9]
  have r0 := holds_refl [-7, -5, 4, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule815 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-9, 4, 9, 7] [-5, -7, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule813 [] [7])) (holds_context c6_rule13 [-5, -7, -5, 4] []))
  have l0 := holds_refl [-9, 4, 9, 7]
  have r0 := holds_refl [-5, -7, -5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule839 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, 5, -9, 4, 9] [-5, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule814 [7] [])) (holds_context c6_rule12 [] [-5, 4, -7]))
  have l0 := holds_refl [7, 5, -9, 4, 9]
  have r0 := holds_refl [-5, 4, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule840 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, 5, -9, 4] [-5, 4, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule839 [] [-9])) (holds_context c6_rule16 [7, 5, -9, 4] []))
  have l0 := holds_refl [-5, 4, -7, -9]
  have r0 := holds_refl [7, 5, -9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule844 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [9, -5, -7, -5, 4] [4, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule815 [9] [])) (holds_context c6_rule16 [] [4, 9, 7]))
  have l0 := holds_refl [9, -5, -7, -5, 4]
  have r0 := holds_refl [4, 9, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
