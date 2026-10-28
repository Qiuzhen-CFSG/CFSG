module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step11

/-! Central word identities for the remaining normalized commutators, chunk 12.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule2287 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [5, 6, 5, 6] [3, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2273 [-5] [])) (holds_context rc22_rule692 [] [6]))
  have l0 := holds_refl [-5, 5, 3, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule9 [] [3, 4])
  have r0 := holds_refl [5, 6, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2288 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [6, 5, 6] [-5, 3, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2287 [-5] [])) (holds_context rc22_rule9 [] [6, 5, 6]))
  have l0 := holds_refl [-5, 3, 4]
  have r0 := holds_refl [6, 5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2290 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-5, 6, -7, 5] [4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2277 [-7] [])) (holds_context rc22_rule13 [] [4, -7]))
  have l0 := holds_refl [-7, 5, 5, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule630 [] [])
  have r0 := holds_refl [4, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2291 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [6, -7, 5] [5, 4, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2290 [5] [])) (holds_context rc22_rule8 [] [6, -7, 5]))
  have l0 := holds_refl [5, 4, -7]
  have r0 := holds_refl [6, -7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2292 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 5, 7, 3] [7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2277 [] [7])) (holds_context rc22_rule13 [7, 4] []))
  have l0 := holds_refl [5, 5, 3, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule34 [5, 5] [])
  have r0 := holds_refl [7, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2293 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_r3) [-5, 7, 4] [5, 7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2292 [-5] [])) (holds_context rc22_rule9 [] [5, 7, 3]))
  have l0 := holds_refl [-5, 7, 4]
  have r0 := holds_refl [5, 7, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2294 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_r3) [7, 3, 4] [5, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2292 [] [3])) (holds_context rc22_rule198 [5, 5, 7] []))
  have l0 := holds_refl [7, 4, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule30 [7] [])
  have r0 := holds_refl [5, 5, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2295 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-5, 7, 3] [5, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2292 [5] [])) (holds_context rc22_rule203 [] [7, 3]))
  have l0 := holds_refl [5, 7, 4]
  have r0 := holds_refl [-5, 7, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2299 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .viii_r3) [5, -7, 3, 6] [-7, -5] := by
  have h0 := rc22_rule1877
  have l0 := holds_refl [6, -5, -7, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule2281 [6] [])
  have l2 := holds_trans l1 (holds_context rc22_rule624 [] [3])
  have l3 := holds_trans l2 (holds_context rc22_rule198 [-7, -5] [])
  have r0 := holds_refl [5, -7, 3, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2300 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .viii_r3) [-7, 3, 6] [-5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2299 [-5] [])) (holds_context rc22_rule9 [] [-7, 3, 6]))
  have l0 := holds_refl [-5, -7, -5]
  have r0 := holds_refl [-7, 3, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2301 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-9 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 5, -7, 3] [-7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2281 [5] [])) (holds_context rc22_rule8 [] [-7, 4]))
  have l0 := holds_refl [5, 5, -7, 3]
  have r0 := holds_refl [-7, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2302 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [-7, 3, 4] [5, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2301 [] [3])) (holds_context rc22_rule198 [5, 5, -7] []))
  have l0 := holds_refl [-7, 4, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule30 [-7] [])
  have r0 := holds_refl [5, 5, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2304 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .viii_r3) [5, 5, -7, 4] [-7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2281 [-5] [])) (holds_context rc22_rule27 [] [-7, 4]))
  have l0 := holds_refl [-5, 5, -7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule9 [] [-7, 3])
  have r0 := holds_refl [5, 5, -7, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2311 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (4 : ℤ) * normalizedRelatorError .iv_s2_s8 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .viii_r3) [8, -5, 3, 6] [10, 4, 10, 5] := by
  have h0 := rc22_rule1761
  have l0 := holds_refl [8, 7, 5, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule2282 [8] [])
  have r0 := holds_refl [-7, 8, -7, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule1838 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule2312 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_r3) [5, -7, -5, 7] [6, 4] := by
  have h0 := rc22_rule1841
  have l0 := holds_refl [7, 5, -7, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule2282 [] [-5])
  have l2 := holds_trans l1 (holds_context rc22_rule698 [] [])
  have r0 := holds_refl [6, 4]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2313 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_r3) [-7, -5, 7] [-5, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2312 [-5] [])) (holds_context rc22_rule9 [] [-7, -5, 7]))
  have l0 := holds_refl [-5, 6, 4]
  have r0 := holds_refl [-7, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2315 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * normalizedRelatorError .viii_r3) [5, 4, 7, 6] [7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2282 [] [7])) (holds_context rc22_rule13 [7, 5] []))
  have l0 := holds_refl [-5, 3, 6, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule1919 [] [])
  have r0 := holds_refl [7, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2316 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (4 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * normalizedRelatorError .viii_r3) [4, 7, 6] [-5, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2315 [-5] [])) (holds_context rc22_rule9 [] [4, 7, 6]))
  have l0 := holds_refl [-5, 7, 5]
  have r0 := holds_refl [4, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2317 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 5, 7, 7] [-7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2282 [] [-7])) (holds_context rc22_rule28 [7, 5] []))
  have l0 := holds_refl [-5, 3, 6, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule636 [-5] [])
  have l2 := holds_trans l1 (holds_context rc22_rule9 [] [-7, 5])
  have r0 := holds_refl [7, 5, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2318 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .viii_r3) [-7, 5, -7] [7, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2317 [] [-7])) (holds_context rc22_rule12 [7, 5, 7] []))
  have l0 := holds_refl [-7, 5, -7]
  have r0 := holds_refl [7, 5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2319 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .viii_r3) [7, 7, 5] [5, 7, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2317 [-7] [])) (holds_context rc22_rule13 [] [5, 7, 7]))
  have l0 := holds_refl [-7, -7, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [] [5])
  have r0 := holds_refl [5, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2321 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-5 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [5, 7, 6, -7] [6, 5] := by
  have h0 := rc22_rule516
  have l0 := holds_refl [-5, 3, 6, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule2284 [-5] [])
  have l2 := holds_trans l1 (holds_context rc22_rule9 [] [6, 5])
  have r0 := holds_refl [5, -7, 6, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule1794 [5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule2322 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-6 : ℤ)) [7, 6, -7] [5, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2321 [-5] [])) (holds_context rc22_rule9 [] [7, 6, -7]))
  have l0 := holds_refl [-5, 6, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule691 [] [])
  have r0 := holds_refl [7, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2327 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 6, 5, 7] [-9, 4, 9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2284 [7] [])) (holds_context rc22_rule648 [] [4]))
  have l0 := holds_refl [7, 5, 6, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule700 [] [])
  have l2 := holds_trans l1 (holds_context rc22_rule1902 [] [])
  have r0 := holds_refl [-5, 7, -5, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule2181 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule2329 : Holds ((normalizedRelatorError .i_r8) ^ (-7 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (14 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-7 : ℤ)) [3, 6, -5, 4] [5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2284 [] [-5])) (holds_context rc22_rule2147 [3, 6] []))
  have l0 := holds_refl [5, 6, 5, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule8 [5, 6] [])
  have r0 := holds_refl [3, 6, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2330 : Holds ((normalizedRelatorError .i_r8) ^ (-7 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (14 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (8 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-7 : ℤ)) [6, -5, 4] [5, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2329 [3] [])) (holds_context rc22_rule198 [] [6, -5, 4]))
  have l0 := holds_refl [3, 5, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule32 [] [6])
  have r0 := holds_refl [6, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2342 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_r3) [5, 5, 7, 4] [7, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2292 [5, 5] [])) (holds_context rc22_rule203 [] [5, 7, 3]))
  have l0 := holds_refl [5, 5, 7, 4]
  have r0 := holds_refl [-5, 5, 7, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule9 [] [7, 3])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule2343 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_r3) [-5, 7, 6, 4] [7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2293 [] [6])) (holds_context rc22_rule35 [-5, 7] []))
  have l0 := holds_refl [5, 7, 3, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule648 [5] [])
  have l2 := holds_trans l1 (holds_context rc22_rule8 [] [7, -5])
  have r0 := holds_refl [-5, 7, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2344 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_r3) [7, 6, 4] [5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2343 [5] [])) (holds_context rc22_rule8 [] [7, 6, 4]))
  have l0 := holds_refl [5, 7, -5]
  have r0 := holds_refl [7, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2347 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-11 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-7 : ℤ)) [8, 5, 7, 3] [-7, 3, 8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2293 [8] [])) (holds_context rc22_rule1357 [] [4]))
  have l0 := holds_refl [8, 5, 7, 3]
  have r0 := holds_refl [-7, 8, 5, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule2150 [-7] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule2354 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_r3) [7, 5, 7, 4] [5, 7, 6, 7] := by
  have h0 := rc22_rule669
  have l0 := holds_refl [7, -5, 7, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule2295 [7] [])
  have r0 := holds_refl [5, 7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2355 : Holds ((normalizedRelatorError .i_r8) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [5, 7, -5, 4] [7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2295 [] [-5])) (holds_context rc22_rule31 [-5, 7] []))
  have l0 := holds_refl [5, 7, 4, -5]
  have l1 := holds_trans l0 (holds_context rc22_rule2147 [5, 7] [])
  have r0 := holds_refl [-5, 7, -5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule645 [-5] [])
  have r2 := holds_trans r1 (holds_context rc22_rule9 [] [7, 6])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule2356 : Holds ((normalizedRelatorError .i_r8) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [7, -5, 4] [-5, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2355 [-5] [])) (holds_context rc22_rule9 [] [7, -5, 4]))
  have l0 := holds_refl [-5, 7, 6]
  have r0 := holds_refl [7, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2360 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (5 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (10 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (7 : ℤ)) [7, -9, 8, 9] [-5, -7, -5, 8] := by
  have h0 := rc22_rule1803
  have l0 := holds_refl [-7, 3, 6, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule2300 [] [8])
  have r0 := holds_refl [7, 7, 8, -7]
  have r1 := holds_trans r0 (holds_context rc22_rule2219 [7] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule2365 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ)) [7, 5, 7, 5] [-5, -7, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2300 [] [-7])) (holds_context rc22_rule636 [-7] []))
  have l0 := holds_refl [-5, -7, -5, -7]
  have r0 := holds_refl [-7, 5, -7, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule2318 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule2368 : Holds ((normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (11 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [8, -5, -7, -5] [7, 3, 8, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2300 [8] [])) (holds_context rc22_rule1296 [] [6]))
  have l0 := holds_refl [8, -5, -7, -5]
  have r0 := holds_refl [6, 7, 8, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule280 [6, 7] [])
  have r2 := holds_trans r1 (holds_context rc22_rule1303 [] [])
  have r3 := holds_trans r2 (holds_context rc22_rule1322 [3] [])
  have r4 := holds_trans r3 (holds_context rc22_rule34 [] [8, 3])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r4)) (by central_nf)

theorem rc22_rule2380 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [3, 8, 5, 6] [7, 8, 7, 5] := by
  have h0 := rc22_rule665
  have l0 := holds_refl [8, -7, -5, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule2313 [8] [])
  have l2 := holds_trans l1 (holds_context rc22_rule2209 [] [])
  have r0 := holds_refl [6, 8, 5, 3]
  have r1 := holds_trans r0 (holds_context rc22_rule1339 [] [])
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule2385 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [5, 7, 6, -5] [4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2316 [] [6])) (holds_context rc22_rule200 [4, 7] []))
  have l0 := holds_refl [-5, 7, 5, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule667 [] [])
  have r0 := holds_refl [4, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2386 : Holds (normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 6, -5] [-5, 4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2385 [-5] [])) (holds_context rc22_rule9 [] [7, 6, -5]))
  have l0 := holds_refl [-5, 4, 7]
  have r0 := holds_refl [7, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2388 : Holds (normalizedRelatorError .i_r8 * normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 5, 6, -7] [5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2317 [] [6, 7])) (holds_context rc22_rule1793 [7, 5] []))
  have l0 := holds_refl [-7, 5, 6, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule571 [] [7])
  have l2 := holds_trans l1 (holds_context rc22_rule13 [5, 4] [])
  have r0 := holds_refl [7, 5, 6, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
