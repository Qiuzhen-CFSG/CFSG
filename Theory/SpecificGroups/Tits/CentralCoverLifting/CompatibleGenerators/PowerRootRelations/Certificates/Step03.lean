module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step02

/-! Kernel-checked central word identities, chunk 3.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c1_rule208 : Holds (normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [6, 3, 4] [4, 6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule35 [] [3])) (holds_context c1_rule30 [6] []))
  have l0 := holds_refl [4, 6, 3]
  have r0 := holds_refl [6, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule209 : Holds (normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 3, 4] [4, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule36 [] [3])) (holds_context c1_rule30 [8] []))
  have l0 := holds_refl [4, 8, 3]
  have r0 := holds_refl [8, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule213 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 9, 3, 7] [5, 2, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule47 [] [3])) (holds_context c1_rule34 [2, 9] []))
  have l0 := holds_refl [5, 2, 3]
  have r0 := holds_refl [2, 9, 3, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule220 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s3 * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [5, 5, 2, 9] [-5, 2, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule48 [-5] [])) (holds_context c1_rule27 [] [2, 9]))
  have l0 := holds_refl [-5, 2, -7]
  have r0 := holds_refl [5, 5, 2, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule230 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s3) [2, 4, 5, 2] [8, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule51 [8] [])) (holds_context c1_rule41 [] [5, 2]))
  have l0 := holds_refl [8, 9, 7]
  have r0 := holds_refl [2, 4, 5, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule234 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [9, 7, 9, 7] [2, 5, 5, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule51 [9, 7] [])) (holds_context c1_rule46 [] [5, 2]))
  have l0 := holds_refl [9, 7, 9, 7]
  have r0 := holds_refl [2, 5, 5, 2]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule238 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * normalizedRelatorError .viii_s2 * normalizedRelatorError .viii_s7 * normalizedRelatorError .viii_s3) [2, 4, 9, 5] [8, 7, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule52 [8] [])) (holds_context c1_rule41 [] [9, 5]))
  have l0 := holds_refl [8, 7, 2]
  have r0 := holds_refl [2, 4, 9, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule243 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-2 : ℤ)) [-5, 7, 2] [2, -7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule52 [-5] [])) (holds_context c1_rule48 [] [5]))
  have l0 := holds_refl [-5, 7, 2]
  have r0 := holds_refl [2, -7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule266 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6] [6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule60 [] [4])) (holds_context c1_rule35 [4, 8] []))
  have l0 := holds_refl [4, 6, 8, 4]
  have l1 := holds_trans l0 (holds_context c1_rule36 [4, 6] [])
  have l2 := holds_trans l1 (holds_context c1_rule35 [4] [8])
  have l3 := holds_trans l2 (holds_context c1_rule201 [] [6, 8])
  have r0 := holds_refl [4, 8, 4, 6]
  have r1 := holds_trans r0 (holds_context c1_rule36 [4] [6])
  have r2 := holds_trans r1 (holds_context c1_rule201 [] [8, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule279 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ)) [3, 5, 4, 5, 5] [3, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule63 [5] [])) (holds_context c1_rule32 [] [8, 3, 8]))
  have l0 := holds_refl [5, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule32 [] [4, 5, 5])
  have r0 := holds_refl [3, 5, 8, 3, 8]
  have r1 := holds_trans r0 (holds_context c1_rule68 [3] [])
  have r2 := holds_trans r1 (holds_context c1_rule200 [] [3, -5, 4])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c1_rule281 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6) [3, 7, 8, 3, 8] [3, 7, 4, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule63 [7] [])) (holds_context c1_rule34 [] [8, 3, 8]))
  have l0 := holds_refl [7, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule34 [] [4, 5, 5])
  have r0 := holds_refl [3, 7, 8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule287 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6) [8, 3, 8] [4, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule64 [] [5])) (holds_context c1_rule9 [8, 3, 8] []))
  have l0 := holds_refl [3, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [4, 5, 5])
  have r0 := holds_refl [8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule296 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ)) [5, 5, 4] [4, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule67 [3] [])) (holds_context c1_rule63 [] [3]))
  have l0 := holds_refl [3, 3, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [5, 5, 4])
  have r0 := holds_refl [3, 4, 5, 5, 3]
  have r1 := holds_trans r0 (holds_context c1_rule32 [3, 4, 5] [])
  have r2 := holds_trans r1 (holds_context c1_rule32 [3, 4] [5])
  have r3 := holds_trans r2 (holds_context c1_rule30 [3] [5, 5])
  have r4 := holds_trans r3 (holds_context c1_rule200 [] [4, 5, 5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r4)) (by central_nf)

theorem c1_rule297 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [4, 8, 3, 5] [3, 8, 3, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule67 [] [8, -5])) (holds_context c1_rule64 [8, 3] []))
  have l0 := holds_refl [3, 5, 5, 4, 8, -5]
  have l1 := holds_trans l0 (holds_context c1_rule296 [3] [8, -5])
  have l2 := holds_trans l1 (holds_context c1_rule70 [3] [-5])
  have l3 := holds_trans l2 (holds_context c1_rule200 [] [3, 8, 3, -5])
  have r0 := holds_refl [8, 3, 3, 3, 4, 5]
  have r1 := holds_trans r0 (holds_context c1_rule200 [8] [3, 4, 5])
  have r2 := holds_trans r1 (holds_context c1_rule209 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule308 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4) [4, 6, 5, 5, 8] [6, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule70 [6] [])) (holds_context c1_rule35 [] [5, 5, 8]))
  have l0 := holds_refl [6, 3, 3, 8, 3]
  have l1 := holds_trans l0 (holds_context c1_rule200 [6] [8, 3])
  have r0 := holds_refl [4, 6, 5, 5, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule309 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ)) [5, 5, 8] [4, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule70 [] [4])) (holds_context c1_rule36 [4, 5, 5] []))
  have l0 := holds_refl [3, 3, 8, 3, 4]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [8, 3, 4])
  have l2 := holds_trans l1 (holds_context c1_rule209 [] [])
  have r0 := holds_refl [4, 5, 5, 4, 8]
  have r1 := holds_trans r0 (holds_context c1_rule296 [4] [8])
  have r2 := holds_trans r1 (holds_context c1_rule201 [] [5, 5, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule311 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .viii_s2) [4, 5, 5, 2, 4] [8, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule70 [] [2])) (holds_context c1_rule41 [4, 5, 5] []))
  have l0 := holds_refl [3, 3, 8, 3, 2]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [8, 3, 2])
  have r0 := holds_refl [4, 5, 5, 2, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule313 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [8, 3, 10, 4] [5, 5, 6, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule70 [] [10, 4])) (holds_context c1_rule61 [4, 5, 5] []))
  have l0 := holds_refl [3, 3, 8, 3, 10, 4]
  have l1 := holds_trans l0 (holds_context c1_rule200 [] [8, 3, 10, 4])
  have r0 := holds_refl [4, 5, 5, 4, 6, 10]
  have r1 := holds_trans r0 (holds_context c1_rule296 [4] [6, 10])
  have r2 := holds_trans r1 (holds_context c1_rule201 [] [5, 5, 6, 10])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c1_rule315 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2) [-9, 4, 9, 3, 4] [6, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule71 [] [3])) (holds_context c1_rule30 [-9, 4, 9] []))
  have l0 := holds_refl [6, 3, 7, 7, 3]
  have l1 := holds_trans l0 (holds_context c1_rule34 [6, 3, 7] [])
  have l2 := holds_trans l1 (holds_context c1_rule34 [6, 3] [7])
  have l3 := holds_trans l2 (holds_context c1_rule200 [6] [7, 7])
  have r0 := holds_refl [-9, 4, 9, 3, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule317 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ)) [6, 3, 7, 7, 2] [2, 9, 8, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule71 [] [2])) (holds_context c1_rule42 [-9, 4, 9] []))
  have l0 := holds_refl [6, 3, 7, 7, 2]
  have r0 := holds_refl [-9, 4, 9, 2, 8]
  have r1 := holds_trans r0 (holds_context c1_rule45 [-9, 4] [8])
  have r2 := holds_trans r1 (holds_context c1_rule42 [-9] [-9, 8])
  have r3 := holds_trans r2 (holds_context c1_rule44 [] [8, -9, 8])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem c1_rule320 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iv_s7_s2) [4, 9, 3, 4, -7] [9, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule72 [] [3])) (holds_context c1_rule34 [9, 6, 3] []))
  have l0 := holds_refl [4, 9, 4, -7, 3]
  have l1 := holds_trans l0 (holds_context c1_rule33 [4, 9, 4] [])
  have l2 := holds_trans l1 (holds_context c1_rule30 [4, 9] [-7])
  have r0 := holds_refl [9, 6, 3, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule200 [9, 6] [7])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule330 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ)) [6, 3, 7, 7, 6] [3, 4, 7, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule74 [] [4])) (holds_context c1_rule35 [-9, 4, 9] []))
  have l0 := holds_refl [3, 4, 7, 7, 4]
  have r0 := holds_refl [-9, 4, 9, 4, 6]
  have r1 := holds_trans r0 (holds_context c1_rule71 [] [6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule332 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .viii_s2 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ)) [3, 4, 7, 7, 2] [2, 9, 8, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule74 [] [2])) (holds_context c1_rule43 [-9, 4, 9] []))
  have l0 := holds_refl [3, 4, 7, 7, 2]
  have r0 := holds_refl [-9, 4, 9, 2, 6]
  have r1 := holds_trans r0 (holds_context c1_rule45 [-9, 4] [6])
  have r2 := holds_trans r1 (holds_context c1_rule42 [-9] [-9, 6])
  have r3 := holds_trans r2 (holds_context c1_rule44 [] [8, -9, 6])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem c1_rule337 : Holds ((normalizedRelatorError .i_r8) ^ (-3 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * normalizedRelatorError .viii_s4) [3, 7, 7, 2, 6] [2, 8, 9, 8, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule75 [] [2])) (holds_context c1_rule45 [4, -9, 4] []))
  have l0 := holds_refl [3, 7, 7, 6, 2]
  have l1 := holds_trans l0 (holds_context c1_rule43 [3, 7, 7] [])
  have r0 := holds_refl [4, -9, 4, 2, -9]
  have r1 := holds_trans r0 (holds_context c1_rule42 [4, -9] [-9])
  have r2 := holds_trans r1 (holds_context c1_rule44 [4] [8, -9])
  have r3 := holds_trans r2 (holds_context c1_rule42 [] [9, 8, -9])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r3)) (by central_nf)

theorem c1_rule340 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ)) [4, 6, 3, 7, 7] [3, 7, 7, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule75 [] [4])) (holds_context c1_rule71 [4] []))
  have l0 := holds_refl [3, 7, 7, 6, 4]
  have l1 := holds_trans l0 (holds_context c1_rule35 [3, 7, 7] [])
  have r0 := holds_refl [4, 6, 3, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule345 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iv_s7_s2) [3, -7, 6, -9, 4] [7, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule77 [-7] [])) (holds_context c1_rule13 [] [7, 4, -9]))
  have l0 := holds_refl [-7, 3, 6, -9, 4]
  have l1 := holds_trans l0 (holds_context c1_rule33 [] [6, -9, 4])
  have r0 := holds_refl [7, 4, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule355 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 7, 4, 5, 5] [6, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule79 [7] [])) (holds_context c1_rule12 [] [6, 7, 6]))
  have l0 := holds_refl [7, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c1_rule34 [] [4, 5, 5])
  have r0 := holds_refl [6, 7, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule367 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 3, 7, 4, -5] [7, 6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule81 [] [-5])) (holds_context c1_rule8 [7, 6, 5] []))
  have l0 := holds_refl [6, 3, 7, 4, -5]
  have r0 := holds_refl [7, 6, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule368 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [7, 6, 3, 5, 5] [6, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule81 [] [3])) (holds_context c1_rule32 [7, 6, 5] []))
  have l0 := holds_refl [6, 3, 7, 4, 3]
  have l1 := holds_trans l0 (holds_context c1_rule30 [6, 3, 7] [])
  have l2 := holds_trans l1 (holds_context c1_rule34 [6, 3] [4])
  have l3 := holds_trans l2 (holds_context c1_rule200 [6] [7, 4])
  have r0 := holds_refl [7, 6, 5, 3, 5]
  have r1 := holds_trans r0 (holds_context c1_rule32 [7, 6] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c1_rule370 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3) [6, 3, 7, 2, 8, -7] [7, 6, 5, 2, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule81 [] [2, -7])) (holds_context c1_rule55 [7, 6, 5] []))
  have l0 := holds_refl [6, 3, 7, 4, 2, -7]
  have l1 := holds_trans l0 (holds_context c1_rule42 [6, 3, 7] [-7])
  have r0 := holds_refl [7, 6, 5, 2, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule371 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 3, 7, 5, 5] [7, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule81 [] [8, 3, 8])) (holds_context c1_rule68 [7, 6, 5] []))
  have l0 := holds_refl [6, 3, 7, 4, 8, 3, 8]
  have l1 := holds_trans l0 (holds_context c1_rule287 [6, 3, 7, 4] [])
  have l2 := holds_trans l1 (holds_context c1_rule201 [6, 3, 7] [5, 5])
  have r0 := holds_refl [7, 6, 5, 3, 3, -5, 4]
  have r1 := holds_trans r0 (holds_context c1_rule32 [7, 6] [3, -5, 4])
  have r2 := holds_trans r1 (holds_context c1_rule32 [7, 6, 3] [-5, 4])
  have r3 := holds_trans r2 (holds_context c1_rule200 [7, 6] [5, -5, 4])
  have r4 := holds_trans r3 (holds_context c1_rule8 [7, 6] [4])
  have r5 := holds_trans r4 (holds_context c1_rule35 [7] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r5)) (by central_nf)

theorem c1_rule373 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [4, 6, 5, 5, -7] [-7, 6, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule82 [] [-7])) (holds_context c1_rule12 [-7, 6, 3] []))
  have l0 := holds_refl [6, 5, 5, 4, -7]
  have l1 := holds_trans l0 (holds_context c1_rule296 [6] [-7])
  have l2 := holds_trans l1 (holds_context c1_rule35 [] [5, 5, -7])
  have r0 := holds_refl [-7, 6, 3]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule374 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [-7, 4, 6, 5, 5] [7, 7, 6, 3, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule82 [-7] [])) (holds_context c1_rule28 [] [6, 3, 7]))
  have l0 := holds_refl [-7, 6, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c1_rule296 [-7, 6] [])
  have l2 := holds_trans l1 (holds_context c1_rule35 [-7] [5, 5])
  have r0 := holds_refl [7, 7, 6, 3, 7]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule375 : Holds ((normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .v_s5_s4) [4, 6, 3, 5, 5] [-7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule82 [] [3])) (holds_context c1_rule34 [-7, 6, 3] []))
  have l0 := holds_refl [6, 5, 5, 4, 3]
  have l1 := holds_trans l0 (holds_context c1_rule296 [6] [3])
  have l2 := holds_trans l1 (holds_context c1_rule35 [] [5, 5, 3])
  have l3 := holds_trans l2 (holds_context c1_rule32 [4, 6, 5] [])
  have l4 := holds_trans l3 (holds_context c1_rule32 [4, 6] [5])
  have r0 := holds_refl [-7, 6, 3, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule200 [-7, 6] [7])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule377 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s3) [5, 2, 4, 6, 5, 5] [2, 4, 9, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule82 [5, 2] [])) (holds_context c1_rule55 [] [6, 3, 7]))
  have l0 := holds_refl [5, 2, 6, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c1_rule296 [5, 2, 6] [])
  have l2 := holds_trans l1 (holds_context c1_rule35 [5, 2] [5, 5])
  have r0 := holds_refl [2, 9, 6, 3, 7]
  have r1 := holds_trans r0 (holds_context c1_rule72 [2] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule379 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [3, 4, 5, 5, -7] [6, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule83 [] [-7])) (holds_context c1_rule12 [6, -7, 6] []))
  have l0 := holds_refl [3, 5, 5, 4, -7]
  have l1 := holds_trans l0 (holds_context c1_rule296 [3] [-7])
  have r0 := holds_refl [6, -7, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c1_rule384 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 7, 7, 5, 5] [3, 4, 7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule83 [-9, 4, 9] [])) (holds_context c1_rule74 [] [-7, 6, 7]))
  have l0 := holds_refl [-9, 4, 9, 3, 5, 5, 4]
  have l1 := holds_trans l0 (holds_context c1_rule296 [-9, 4, 9, 3] [])
  have l2 := holds_trans l1 (holds_context c1_rule315 [] [5, 5])
  have r0 := holds_refl [3, 4, 7, 7, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context c1_rule12 [3, 4, 7] [6, 7])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem c1_rule387 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [5, 6, -7, 4, 6] [3, -5, 4, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule84 [] [4])) (holds_context c1_rule35 [5, 6, -7] []))
  have l0 := holds_refl [3, -5, 4, -7, 4]
  have r0 := holds_refl [5, 6, -7, 4, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c1_rule392 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ)) [5, -7, 6, 7] [3, -5, 4, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule84 [] [7, 6])) (holds_context c1_rule79 [5, 6] []))
  have l0 := holds_refl [3, -5, 4, -7, 7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule13 [3, -5, 4] [6])
  have r0 := holds_refl [5, 6, 3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c1_rule208 [5] [5, 5])
  have r2 := holds_trans r1 (holds_context c1_rule375 [5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r2))) (by central_nf)

theorem c1_rule394 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * normalizedRelatorError .v_s5_s4) [3, -5, 4, -7, 6] [5, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c1_rule85 [-5] [])) (holds_context c1_rule9 [] [5, 6, -7]))
  have l0 := holds_refl [-5, 3, 4, -7, 6]
  have l1 := holds_trans l0 (holds_context c1_rule31 [] [4, -7, 6])
  have r0 := holds_refl [5, 6, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
