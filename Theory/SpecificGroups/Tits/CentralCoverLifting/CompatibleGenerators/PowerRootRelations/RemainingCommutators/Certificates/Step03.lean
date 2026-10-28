module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step02

/-! Central word identities for the remaining normalized commutators, chunk 3.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule274 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 10, 8] [6, 10, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule273 [] [6])) (holds_context rc22_rule200 [8, 10, 8] []))
  have l0 := holds_refl [6, 10, 6]
  have r0 := holds_refl [8, 10, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule280 : Holds (normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ)) [8, 6] [6, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule57 [] [4])) (holds_context rc22_rule36 [6, 4] []))
  have l0 := holds_refl [10, 4, 10, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule56 [10] [])
  have l2 := holds_trans l1 (holds_context rc22_rule59 [10] [])
  have l3 := holds_trans l2 (holds_context rc22_rule202 [] [8, 6])
  have r0 := holds_refl [6, 4, 4, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule199 [6] [8])
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule291 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [3, 8, 5, 5] [4, 8] := by
  have h0 := rc22_rule65
  have l0 := holds_refl [8, 3, 3, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule198 [8] [4])
  have l2 := holds_trans l1 (holds_context rc22_rule36 [] [])
  have r0 := holds_refl [3, 8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule292 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [4, 8, -5] [3, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule291 [] [-5])) (holds_context rc22_rule8 [3, 8, 5] []))
  have l0 := holds_refl [4, 8, -5]
  have r0 := holds_refl [3, 8, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule293 : Holds (normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [8, 5, 5] [3, 4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule291 [3] [])) (holds_context rc22_rule198 [] [8, 5, 5]))
  have l0 := holds_refl [3, 4, 8]
  have r0 := holds_refl [8, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule294 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [5, 8, 3, 8] [-5, 4] := by
  have h0 := rc22_rule68
  have l0 := holds_refl [-5, 3, 3, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule198 [-5] [4])
  have r0 := holds_refl [5, 8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule295 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [8, 3, 8] [5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule294 [-5] [])) (holds_context rc22_rule9 [] [8, 3, 8]))
  have l0 := holds_refl [-5, -5, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [] [4])
  have r0 := holds_refl [8, 3, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule296 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [5, 5, 8, 3] [4, 8] := by
  have h0 := rc22_rule69
  have l0 := holds_refl [3, 3, 4, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule198 [] [4, 8])
  have r0 := holds_refl [5, 5, 8, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule297 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [-5, 4, 8] [5, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule296 [-5] [])) (holds_context rc22_rule9 [] [5, 8, 3]))
  have l0 := holds_refl [-5, 4, 8]
  have r0 := holds_refl [5, 8, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule298 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [4, 8, 3] [5, 5, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule296 [] [3])) (holds_context rc22_rule198 [5, 5, 8] []))
  have l0 := holds_refl [4, 8, 3]
  have r0 := holds_refl [5, 5, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule299 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [-5, 8, 3] [5, 4, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule296 [5] [])) (holds_context rc22_rule203 [] [8, 3]))
  have l0 := holds_refl [5, 4, 8]
  have r0 := holds_refl [-5, 8, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule300 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s2 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [3, 2, 8, 7] [5, 2, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule198 [3, 2, 8, 7] [])) (holds_context rc22_rule94 [] [3]))
  have l0 := holds_refl [3, 2, 8, 7]
  have r0 := holds_refl [5, 2, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule314 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2) [3, 4, 7, 7] [-9, 4, 9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule208 [] [-7])) (holds_context rc22_rule33 [4, -7] []))
  have l0 := holds_refl [3, 4, -7, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [3, 4] [])
  have r0 := holds_refl [4, -7, -7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule28 [4] [3])
  have r2 := holds_trans r1 (holds_context rc22_rule74 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule318 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s6) [4, 8, 7, 3] [5, 5, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule209 [8] [])) (holds_context rc22_rule36 [] [7, 3]))
  have l0 := holds_refl [8, 3, 4, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule210 [] [7])
  have l2 := holds_trans l1 (holds_context rc22_rule298 [] [7])
  have r0 := holds_refl [4, 8, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule322 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ)) [5, 5, 4, 8] [8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule210 [] [4])) (holds_context rc22_rule199 [8, 3] []))
  have l0 := holds_refl [4, 8, 3, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule298 [] [4])
  have l2 := holds_trans l1 (holds_context rc22_rule36 [5, 5] [])
  have r0 := holds_refl [8, 3]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule327 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ)) [8, 10] [10, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule213 [] [1])) (holds_context rc22_rule38 [1, 6] []))
  have l0 := holds_refl [10, 1, 6, 1]
  have l1 := holds_trans l0 (holds_context rc22_rule227 [10] [])
  have r0 := holds_refl [1, 6, 1, 10]
  have r1 := holds_trans r0 (holds_context rc22_rule227 [] [10])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule330 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s6) [6, 10, 6] [10] := by
  have h0 := rc22_rule274
  have l0 := holds_refl [8, 10, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule327 [] [8])
  have l2 := holds_trans l1 (holds_context rc22_rule201 [10] [])
  have r0 := holds_refl [6, 10, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule331 : Holds ((normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [6, 10] [10, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule330 [6] [])) (holds_context rc22_rule200 [] [10, 6]))
  have l0 := holds_refl [6, 10]
  have r0 := holds_refl [10, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule354 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ)) [2, 6, 7, 2] [6, 9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule228 [6] [])) (holds_context rc22_rule43 [] [7, 2]))
  have l0 := holds_refl [6, 9, 5]
  have r0 := holds_refl [2, 6, 7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule365 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * normalizedRelatorError .viii_s3) [2, 9, -7, 2] [-9, -5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule229 [-9] [])) (holds_context rc22_rule44 [] [-7, 2]))
  have l0 := holds_refl [-9, -5, -9]
  have r0 := holds_refl [2, 9, -7, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule376 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ)) [5, 5, 4, 5] [4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule292 [8] [])) (holds_context rc22_rule36 [] [8, -5]))
  have l0 := holds_refl [8, 3, 8, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule295 [] [5])
  have r0 := holds_refl [4, 8, 8, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule201 [4] [-5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule377 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ)) [4, 5, 5] [5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule376 [] [-5])) (holds_context rc22_rule8 [5, 5, 4] []))
  have l0 := holds_refl [4, -5, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule27 [4] [])
  have r0 := holds_refl [5, 5, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule379 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ)) [-5, 4, 5] [5, 4, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule376 [5] [])) (holds_context rc22_rule203 [] [4, 5]))
  have l0 := holds_refl [5, 4, -5]
  have r0 := holds_refl [-5, 4, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule381 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [6, 3, 8, 5] [10, 4, 10, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule292 [6] [])) (holds_context rc22_rule57 [] [-5]))
  have l0 := holds_refl [6, 3, 8, 5]
  have r0 := holds_refl [10, 4, 10, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule382 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [3, 4, 8, 5] [8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule292 [4] [])) (holds_context rc22_rule199 [] [8, -5]))
  have l0 := holds_refl [4, 3, 8, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule30 [] [8, 5])
  have r0 := holds_refl [8, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule383 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ)) [4, 8, 5] [3, 8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule382 [3] [])) (holds_context rc22_rule198 [] [4, 8, 5]))
  have l0 := holds_refl [3, 8, -5]
  have r0 := holds_refl [4, 8, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule390 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6) [-5, 3, 4, 8] [5, 3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule297 [3] [])) (holds_context rc22_rule31 [] [4, 8]))
  have l0 := holds_refl [3, 5, 8, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [] [8, 3])
  have r0 := holds_refl [-5, 3, 4, 8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule395 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6) [3, 8, -5, 3] [5, 5, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule298 [] [5])) (holds_context rc22_rule32 [4, 8] []))
  have l0 := holds_refl [5, 5, 8, 5]
  have r0 := holds_refl [4, 8, 5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule383 [] [3])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule401 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [-5, 8, -7, 3] [5, 4, 8, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule299 [] [-7])) (holds_context rc22_rule33 [-5, 8] []))
  have l0 := holds_refl [5, 4, 8, -7]
  have r0 := holds_refl [-5, 8, -7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule402 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [-5, 8, 7, 3] [5, 4, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule299 [] [7])) (holds_context rc22_rule34 [-5, 8] []))
  have l0 := holds_refl [5, 4, 8, 7]
  have r0 := holds_refl [-5, 8, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule407 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [-7, 3, 6, 7] [5, 5, 6, 4] := by
  have h0 := rc22_rule86
  have l0 := holds_refl [4, 5, 5, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule377 [] [6])
  have l2 := holds_trans l1 (holds_context rc22_rule35 [5, 5] [])
  have r0 := holds_refl [-7, 3, 6, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule411 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * normalizedRelatorError .vii_s2 * (normalizedRelatorError .vii_s4) ^ (-1 : ℤ)) [1, 3, 8, -5] [10, 6, 1, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule383 [1] [])) (holds_context rc22_rule37 [] [8, 5]))
  have l0 := holds_refl [1, 3, 8, -5]
  have r0 := holds_refl [10, 1, 8, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule40 [10] [5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule412 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ)) [6, 3, 8, -5] [10, 4, 10, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule383 [6] [])) (holds_context rc22_rule57 [] [5]))
  have l0 := holds_refl [6, 3, 8, -5]
  have r0 := holds_refl [10, 4, 10, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule432 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * normalizedRelatorError .iv_s7_s2) [7, 7, 3, 6, -9] [4, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule75 [] [-9])) (holds_context rc22_rule16 [4, -9, 4] []))
  have l0 := holds_refl [7, 7, 3, 6, -9]
  have r0 := holds_refl [4, -9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule433 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [-7, 4, -9, 4] [7, 3, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule432 [-7] [])) (holds_context rc22_rule13 [] [7, 3, 6, -9]))
  have l0 := holds_refl [-7, 4, -9, 4]
  have r0 := holds_refl [7, 3, 6, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule434 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2) [8, 7, 7, 3, 6] [4, 8, -9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule75 [8] [])) (holds_context rc22_rule36 [] [-9, 4, 9]))
  have l0 := holds_refl [8, 7, 7, 3, 6]
  have r0 := holds_refl [4, 8, -9, 4, 9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule439 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [7, 3, 4, -9, 4] [-7, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule76 [3] [])) (holds_context rc22_rule33 [] [3, 6, -9]))
  have l0 := holds_refl [3, 7, 4, -9, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [] [4, -9, 4])
  have r0 := holds_refl [-7, 3, 3, 6, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule198 [-7] [6, -9])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule440 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ)) [3, 4, -9, 4] [7, 7, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule439 [-7] [])) (holds_context rc22_rule13 [] [3, 4, -9, 4]))
  have l0 := holds_refl [-7, -7, 6, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [] [6, -9])
  have r0 := holds_refl [3, 4, -9, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule451 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [7, 5, 5, 3, 4] [6, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule80 [] [5])) (holds_context rc22_rule9 [6, 7, 6] []))
  have l0 := holds_refl [7, 3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule377 [7, 3] [])
  have l2 := holds_trans l1 (holds_context rc22_rule32 [7] [5, 4])
  have l3 := holds_trans l2 (holds_context rc22_rule32 [7, 5] [4])
  have r0 := holds_refl [6, 7, 6]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule452 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4) [6, 7, 6, 4] [7, 5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule451 [] [4])) (holds_context rc22_rule199 [7, 5, 5, 3] []))
  have l0 := holds_refl [6, 7, 6, 4]
  have r0 := holds_refl [7, 5, 5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
