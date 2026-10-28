module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step19

/-! Kernel-checked central word identities, chunk 20.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule2525 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [9, 6, 9, 6] [6, 10, 3, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2524 [6] [])) (holds_context c6_rule172 [] [9, 6, 9, 6]))
  have l0 := holds_refl [6, 10, 3, 10]
  have r0 := holds_refl [9, 6, 9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2526 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 10, 3, 10] [6, 9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2524 [] [6])) (holds_context c6_rule172 [6, 9, 6, 9] []))
  have l0 := holds_refl [10, 3, 10, 6]
  have l1 := holds_trans l0 (holds_context c6_rule224 [10, 3] [])
  have l2 := holds_trans l1 (holds_context c6_rule358 [] [10])
  have r0 := holds_refl [6, 9, 6, 9]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2759 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (11 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ)) [3, -9, 3, -9, 6] [4, 10, 3, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2422 [3, -9] [])) (holds_context c6_rule1008 [] [-9, 3]))
  have l0 := holds_refl [3, -9, 3, -9, 6]
  have r0 := holds_refl [5, 5, -9, -9, 3]
  have r1 := holds_trans r0 (holds_context c6_rule28 [5, 5] [3])
  have r2 := holds_trans r1 (holds_context c6_rule2194 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule2828 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ)) [6, -9, 6, 9, 9] [6, 9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2525 [-9] [])) (holds_context c6_rule17 [] [6, 9, 6]))
  have l0 := holds_refl [-9, 6, 10, 3, 10]
  have l1 := holds_trans l0 (holds_context c6_rule2526 [-9] [])
  have l2 := holds_trans l1 (holds_context c6_rule1356 [] [9])
  have r0 := holds_refl [6, 9, 6]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2830 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ)) [-9, 6, 9, 9] [9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2828 [6] [])) (holds_context c6_rule172 [] [-9, 6, 9, 9]))
  have l0 := holds_refl [6, 6, 9, 6]
  have l1 := holds_trans l0 (holds_context c6_rule172 [] [9, 6])
  have r0 := holds_refl [-9, 6, 9, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2832 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ)) [-9, 6, 9] [9, 6, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2830 [] [-9])) (holds_context c6_rule16 [-9, 6, 9] []))
  have l0 := holds_refl [9, 6, -9]
  have r0 := holds_refl [-9, 6, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2833 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ)) [-9, 6, -9] [9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2830 [] [9])) (holds_context c6_rule177 [-9, 6] []))
  have l0 := holds_refl [9, 6, 9]
  have r0 := holds_refl [-9, 6, -9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2847 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * normalizedRelatorError .v_s5_s4) [9, 6, -9, 7] [3, -7, 6] := by
  have h0 := c6_rule1254
  have l0 := holds_refl [-9, 6, 9, 7]
  have l1 := holds_trans l0 (holds_context c6_rule2832 [] [7])
  have r0 := holds_refl [3, -7, 6]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2856 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-9, 3, -7, 6] [6, -9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2847 [-9] [])) (holds_context c6_rule17 [] [6, -9, 7]))
  have l0 := holds_refl [-9, 3, -7, 6]
  have r0 := holds_refl [6, -9, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2860 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * normalizedRelatorError .v_s5_s4) [6, -9, 7, 6] [-9, 3, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2856 [] [6])) (holds_context c6_rule172 [-9, 3, -7] []))
  have l0 := holds_refl [6, -9, 7, 6]
  have r0 := holds_refl [-9, 3, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2861 : Holds ((normalizedRelatorError .i_s1) ^ (-3 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (10 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -9, 3, -7] [-9, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2860 [6] [])) (holds_context c6_rule172 [] [-9, 7, 6]))
  have l0 := holds_refl [6, -9, 3, -7]
  have r0 := holds_refl [-9, 7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2862 : Holds ((normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * normalizedRelatorError .v_s5_s4) [-9, 7, 6, 7] [6, -9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2861 [] [7])) (holds_context c6_rule13 [6, -9, 3] []))
  have l0 := holds_refl [-9, 7, 6, 7]
  have r0 := holds_refl [6, -9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule2865 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-8 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ)) [-9, 3, -9, 6] [6, -9, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2862 [] [-9])) (holds_context c6_rule1282 [-9] []))
  have l0 := holds_refl [6, -9, 3, -9]
  have r0 := holds_refl [-9, 3, -9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule2869 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [10, 3, 10] [9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2525 [] [6])) (holds_context c6_rule172 [9, 6, 9] []))
  have l0 := holds_refl [6, 10, 3, 10, 6]
  have l1 := holds_trans l0 (holds_context c6_rule2526 [] [6])
  have l2 := holds_trans l1 (holds_context c6_rule2525 [6] [])
  have l3 := holds_trans l2 (holds_context c6_rule172 [] [10, 3, 10])
  have r0 := holds_refl [9, 6, 9]
  exact holds_factor (holds_trans (holds_symm l3) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule3162 : Holds ((normalizedRelatorError .i_s1) ^ (-5 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (24 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, -9, 6, -7, 6] [4, -9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule2856 [6, 4] [])) (holds_context c6_rule2422 [] [-7, 6]))
  have l0 := holds_refl [6, 4, 6, -9, 7]
  have l1 := holds_trans l0 (holds_context c6_rule34 [6] [-9, 7])
  have l2 := holds_trans l1 (holds_context c6_rule172 [] [4, -9, 7])
  have r0 := holds_refl [3, -9, 6, -7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule3163 : Holds ((normalizedRelatorError .i_s1) ^ (-6 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (24 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (16 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-9, 6, -7, 6] [3, 4, -9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule3162 [3] [])) (holds_context c6_rule170 [] [-9, 6, -7, 6]))
  have l0 := holds_refl [3, 4, -9, 7]
  have r0 := holds_refl [-9, 6, -7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule3164 : Holds ((normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-24 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-16 : ℤ) * normalizedRelatorError .iii_s1_s7 * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (10 : ℤ) * normalizedRelatorError .v_s5_s4) [4, -9, 7, 6] [3, -9, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule3162 [] [6])) (holds_context c6_rule172 [3, -9, 6, -7] []))
  have l0 := holds_refl [4, -9, 7, 6]
  have r0 := holds_refl [3, -9, 6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule3525 : Holds ((normalizedRelatorError .i_s1) ^ (-5 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (22 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (14 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-9 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, -9, -5, -7, 5] [-5, 4, -9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule3162 [-5] [])) (holds_context c6_rule1010 [] [-7, 6]))
  have l0 := holds_refl [-5, 4, -9, 7]
  have r0 := holds_refl [5, -9, 4, -7, 6]
  have r1 := holds_trans r0 (holds_context c6_rule215 [5, -9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule3532 : Holds ((normalizedRelatorError .i_s1) ^ (-7 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (16 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ)) [-9, -5, 6, -7, 4] [3, 4, -9, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule3163 [] [-5])) (holds_context c6_rule1416 [-9, 6] []))
  have l0 := holds_refl [3, 4, -9, 7, -5]
  have r0 := holds_refl [-9, 6, -5, 4, -7]
  have r1 := holds_trans r0 (holds_context c6_rule1599 [-9] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule3706 : Holds ((normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-22 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-14 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (9 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [-5, 4, -9, 7, -5] [5, -9, -5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule3525 [] [-5])) (holds_context c6_rule8 [5, -9, -5, -7] []))
  have l0 := holds_refl [-5, 4, -9, 7, -5]
  have r0 := holds_refl [5, -9, -5, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule3791 : Holds ((normalizedRelatorError .i_s1) ^ (-5 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (22 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (14 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-9 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ)) [5, 5, -9, -5, -7] [4, -9, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule3706 [5] [])) (holds_context c6_rule8 [] [4, -9, 7, -5]))
  have l0 := holds_refl [5, 5, -9, -5, -7]
  have r0 := holds_refl [4, -9, 7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule3866 : Holds ((normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-22 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-10 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-14 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (9 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ)) [4, -9, 7, -5, 7] [5, 5, -9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule3791 [] [7])) (holds_context c6_rule13 [5, 5, -9, -5] []))
  have l0 := holds_refl [4, -9, 7, -5, 7]
  have r0 := holds_refl [5, 5, -9, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4025 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3) [-9, 6, -5, 4] [1, -5, 7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule144 [] [7])) (holds_context c6_rule13 [1, -5, 1, 1, 7, 1] []))
  have l0 := holds_refl [-9, -7, 5, 3, 4, 7]
  have l1 := holds_trans l0 (holds_context c6_rule181 [-9] [4, 7])
  have l2 := holds_trans l1 (holds_context c6_rule365 [-9] [4, 7])
  have l3 := holds_trans l2 (holds_context c6_rule3532 [] [7])
  have l4 := holds_trans l3 (holds_context c6_rule3866 [3] [])
  have l5 := holds_trans l4 (holds_context c6_rule31 [] [5, -9, -5])
  have l6 := holds_trans l5 (holds_context c6_rule31 [5] [-9, -5])
  have l7 := holds_trans l6 (holds_context c6_rule995 [] [-5])
  have l8 := holds_trans l7 (holds_context c6_rule1412 [-9, 6] [])
  have r0 := holds_refl [1, -5, 1, 1, 7, 1]
  have r1 := holds_trans r0 (holds_context c6_rule169 [1, -5] [7, 1])
  exact holds_factor (holds_trans (holds_symm l8) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule4032 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ)) [9, 1, -5, 7, 1] [6, -5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4025 [9] [])) (holds_context c6_rule16 [] [6, -5, 4]))
  have l0 := holds_refl [9, 1, -5, 7, 1]
  have r0 := holds_refl [6, -5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4033 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-8 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ) * normalizedRelatorError .vii_s2 * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ)) [9, 1, -5, 7] [6, -5, 1, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4032 [] [1])) (holds_context c6_rule169 [9, 1, -5, 7] []))
  have l0 := holds_refl [6, -5, 4, 1]
  have l1 := holds_trans l0 (holds_context c6_rule37 [6, -5] [])
  have r0 := holds_refl [9, 1, -5, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4046 : Holds ((normalizedRelatorError .i_r1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s1) ^ (8 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-10 : ℤ) * normalizedRelatorError .iii_s1_s7 * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-4 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3) [3, 4, -9, 7, -5] [1, -5, 7, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4025 [] [-7])) (holds_context c6_rule1599 [-9] []))
  have l0 := holds_refl [1, -5, 7, 1, -7]
  have r0 := holds_refl [-9, -5, 6, -7, 4]
  have r1 := holds_trans r0 (holds_context c6_rule3532 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule4055 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3) [6, -5, 1, 10, -7] [9, 1, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4033 [] [-7])) (holds_context c6_rule12 [9, 1, -5] []))
  have l0 := holds_refl [6, -5, 1, 10, -7]
  have r0 := holds_refl [9, 1, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4228 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [5, 5, 3, 1, 10, 9] [-5, 7, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule169 [] [5, 5, 3, 1, 10, 9])) (holds_context c6_rule161 [1] []))
  have l0 := holds_refl [5, 5, 3, 1, 10, 9]
  have r0 := holds_refl [1, -9, -7, 5, 3, 4]
  have r1 := holds_trans r0 (holds_context c6_rule181 [1, -9] [4])
  have r2 := holds_trans r1 (holds_context c6_rule365 [1, -9] [4])
  have r3 := holds_trans r2 (holds_context c6_rule3532 [1] [])
  have r4 := holds_trans r3 (holds_context c6_rule4046 [1] [])
  have r5 := holds_trans r4 (holds_context c6_rule169 [] [-5, 7, 1, -7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r5)) (by central_nf)

theorem c6_rule4231 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [-5, 3, 1, 10, 9] [7, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4228 [5] [])) (holds_context c6_rule175 [] [3, 1, 10, 9]))
  have l0 := holds_refl [5, -5, 7, 1, -7]
  have l1 := holds_trans l0 (holds_context c6_rule8 [] [7, 1, -7])
  have r0 := holds_refl [-5, 3, 1, 10, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4232 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [3, 1, 10, 9] [5, 7, 1, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4231 [5] [])) (holds_context c6_rule8 [] [3, 1, 10, 9]))
  have l0 := holds_refl [5, 7, 1, -7]
  have r0 := holds_refl [3, 1, 10, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4233 : Holds ((normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * normalizedRelatorError .vii_s2 * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [7, 1, -7, -9] [-5, 3, 1, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4231 [] [-9])) (holds_context c6_rule16 [-5, 3, 1, 10] []))
  have l0 := holds_refl [7, 1, -7, -9]
  have r0 := holds_refl [-5, 3, 1, 10]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4235 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (2 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [5, 4, 7, 1, -7] [3, 1, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4232 [4] [])) (holds_context c6_rule29 [] [1, 10, 9]))
  have l0 := holds_refl [4, 5, 7, 1, -7]
  have l1 := holds_trans l0 (holds_context c6_rule1410 [] [7, 1, -7])
  have r0 := holds_refl [3, 4, 1, 10, 9]
  have r1 := holds_trans r0 (holds_context c6_rule37 [3] [10, 9])
  have r2 := holds_trans r1 (holds_context c6_rule174 [3, 1] [9])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem c6_rule4236 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s2) ^ (2 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [4, 7, 1, -7] [-5, 3, 1, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4235 [-5] [])) (holds_context c6_rule9 [] [4, 7, 1, -7]))
  have l0 := holds_refl [-5, 3, 1, 9]
  have r0 := holds_refl [4, 7, 1, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4247 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [5, 6, 4, -7, 1] [1, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4233 [-7] [])) (holds_context c6_rule13 [] [1, -7, -9]))
  have l0 := holds_refl [-7, -5, 3, 1, 10]
  have l1 := holds_trans l0 (holds_context c6_rule180 [] [1, 10])
  have l2 := holds_trans l1 (holds_context c6_rule1316 [3] [])
  have l3 := holds_trans l2 (holds_context c6_rule30 [] [-7, 1, 8])
  have l4 := holds_trans l3 (holds_context c6_rule696 [] [])
  have r0 := holds_refl [1, -7, -9]
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule4248 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-1 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .vii_r3) ^ (-1 : ℤ)) [6, 4, -7, 1] [-5, 1, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4247 [-5] [])) (holds_context c6_rule9 [] [6, 4, -7, 1]))
  have l0 := holds_refl [-5, 1, -7, -9]
  have r0 := holds_refl [6, 4, -7, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4254 : Holds (normalizedRelatorError .i_r1 * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [1, 10, 3, 1, 3] [-5, 1, 9] := by
  have h0 := c6_rule906
  have l0 := holds_refl [3, 4, 7, 1, -7]
  have l1 := holds_trans l0 (holds_context c6_rule4236 [3] [])
  have l2 := holds_trans l1 (holds_context c6_rule30 [] [3, 1, 9])
  have l3 := holds_trans l2 (holds_context c6_rule170 [-5] [1, 9])
  have r0 := holds_refl [1, 10, 3, 1, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4255 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s5) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ) * normalizedRelatorError .vii_s2 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * normalizedRelatorError .vii_r3) [10, 3, 1, 3] [1, -5, 1, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4254 [1] [])) (holds_context c6_rule169 [] [10, 3, 1, 3]))
  have l0 := holds_refl [1, -5, 1, 9]
  have r0 := holds_refl [10, 3, 1, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4259 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [-5, 3, 1, 9, 1] [-5, 1, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4236 [] [1])) (holds_context c6_rule71 [4] []))
  have l0 := holds_refl [-5, 3, 1, 9, 1]
  have r0 := holds_refl [4, 1, 3, 1, 3]
  have r1 := holds_trans r0 (holds_context c6_rule37 [] [3, 1, 3])
  have r2 := holds_trans r1 (holds_context c6_rule4255 [1] [])
  have r3 := holds_trans r2 (holds_context c6_rule169 [] [-5, 1, 9])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem c6_rule4260 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [3, 1, 9, 1] [1, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4259 [5] [])) (holds_context c6_rule8 [] [3, 1, 9, 1]))
  have l0 := holds_refl [5, -5, 1, 9]
  have l1 := holds_trans l0 (holds_context c6_rule8 [] [1, 9])
  have r0 := holds_refl [3, 1, 9, 1]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule4261 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [3, 1, 9] [1, 9, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule4260 [] [1])) (holds_context c6_rule169 [3, 1, 9] []))
  have l0 := holds_refl [1, 9, 1]
  have r0 := holds_refl [3, 1, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
