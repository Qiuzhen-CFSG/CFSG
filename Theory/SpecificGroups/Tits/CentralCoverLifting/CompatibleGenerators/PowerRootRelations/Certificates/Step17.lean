module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step16

/-! Kernel-checked central word identities, chunk 17.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c6_rule845 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [4, 9, 7, 4] [9, -5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule844 [] [4])) (holds_context c6_rule171 [9, -5, -7, -5] []))
  have l0 := holds_refl [4, 9, 7, 4]
  have r0 := holds_refl [9, -5, -7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule864 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [4, 9, -5, -7, -5] [9, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule845 [4] [])) (holds_context c6_rule171 [] [9, 7, 4]))
  have l0 := holds_refl [4, 9, -5, -7, -5]
  have r0 := holds_refl [9, 7, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule865 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [4, 9, -5, -7] [9, 7, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule864 [] [5])) (holds_context c6_rule9 [4, 9, -5, -7] []))
  have l0 := holds_refl [9, 7, 4, 5]
  have r0 := holds_refl [4, 9, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule875 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [9, 7, 4, 5, 7] [4, 9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule865 [] [7])) (holds_context c6_rule13 [4, 9, -5] []))
  have l0 := holds_refl [9, 7, 4, 5, 7]
  have r0 := holds_refl [4, 9, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule876 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [-9, 4, 9, -5] [7, 4, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule875 [-9] [])) (holds_context c6_rule17 [] [7, 4, 5, 7]))
  have l0 := holds_refl [-9, 4, 9, -5]
  have r0 := holds_refl [7, 4, 5, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule878 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [4, 9, -5, 3, -7] [9, 3, 7, 4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule865 [] [3])) (holds_context c6_rule32 [4, 9, -5] []))
  have l0 := holds_refl [9, 7, 4, 5, 3]
  have l1 := holds_trans l0 (holds_context c6_rule179 [9, 7] [])
  have l2 := holds_trans l1 (holds_context c6_rule33 [9] [4, 5])
  have r0 := holds_refl [4, 9, -5, 3, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule885 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s3_s5) [-9, 4, 9, 5, 5] [7, 4, 5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule876 [] [-5])) (holds_context c6_rule26 [-9, 4, 9] []))
  have l0 := holds_refl [7, 4, 5, 7, -5]
  have r0 := holds_refl [-9, 4, 9, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule902 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s5) [3, 7, 1, -7] [1, 3, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule70 [3, 1] [])) (holds_context c6_rule70 [] [3, 1]))
  have l0 := holds_refl [3, 1, 1, 7, 1, -7]
  have l1 := holds_trans l0 (holds_context c6_rule169 [3] [7, 1, -7])
  have r0 := holds_refl [1, 7, 1, -7, 3, 1]
  have r1 := holds_trans r0 (holds_context c6_rule32 [1, 7, 1] [1])
  have r2 := holds_trans r1 (holds_context c6_rule128 [] [1])
  have r3 := holds_trans r2 (holds_context c6_rule169 [] [7, 1, -7, 1])
  have r4 := holds_trans r3 (holds_context c6_rule71 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r4)) (by central_nf)

theorem c6_rule906 : Holds ((normalizedRelatorError .i_r1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .vi_s1_r1 * normalizedRelatorError .vii_s2 * normalizedRelatorError .vii_s5) [3, 4, 7, 1, -7] [1, 10, 3, 1, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule902 [4] [])) (holds_context c6_rule29 [] [7, 1, -7]))
  have l0 := holds_refl [4, 1, 3, 1, 3]
  have l1 := holds_trans l0 (holds_context c6_rule37 [] [3, 1, 3])
  have r0 := holds_refl [3, 4, 7, 1, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule907 : Holds ((normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .vi_s1_r1) [3, 1, -7] [1, -7, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule902 [-7] [])) (holds_context c6_rule32 [] [7, 1, -7]))
  have l0 := holds_refl [-7, 1, 3, 1, 3]
  have l1 := holds_trans l0 (holds_context c6_rule72 [] [3])
  have l2 := holds_trans l1 (holds_context c6_rule170 [1, -7, 1] [])
  have r0 := holds_refl [3, -7, 7, 1, -7]
  have r1 := holds_trans r0 (holds_context c6_rule13 [3] [1, -7])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule908 : Holds ((normalizedRelatorError .i_r1) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [1, -7, 1, 7] [3, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule907 [] [7])) (holds_context c6_rule13 [3, 1] []))
  have l0 := holds_refl [1, -7, 1, 7]
  have r0 := holds_refl [3, 1]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule909 : Holds ((normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (-1 : ℤ)) [-7, 1, 7] [1, 3, 1] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule908 [1] [])) (holds_context c6_rule169 [] [-7, 1, 7]))
  have l0 := holds_refl [1, 3, 1]
  have r0 := holds_refl [-7, 1, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule990 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [9, 5, 5, 3, 4] [6, 4, 9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule74 [-9] [])) (holds_context c6_rule17 [] [9, 3, 8, 3, 8]))
  have l0 := holds_refl [-9, 3, 10, 3, 10, 3]
  have l1 := holds_trans l0 (holds_context c6_rule97 [] [3])
  have l2 := holds_trans l1 (holds_context c6_rule33 [6, 9, 6, 7] [])
  have l3 := holds_trans l2 (holds_context c6_rule33 [6, 9, 6] [7])
  have l4 := holds_trans l3 (holds_context c6_rule355 [6, 9] [7, 7])
  have l5 := holds_trans l4 (holds_context c6_rule370 [6, 9] [])
  have l6 := holds_trans l5 (holds_context c6_rule539 [6] [])
  have r0 := holds_refl [9, 3, 8, 3, 8]
  have r1 := holds_trans r0 (holds_context c6_rule208 [9, 3] [])
  have r2 := holds_trans r1 (holds_context c6_rule31 [9] [5, 4])
  have r3 := holds_trans r2 (holds_context c6_rule31 [9, 5] [4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l6) (holds_trans h0 r3))) (by central_nf)

theorem c6_rule992 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [9, 5, 5, 3] [6, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule990 [] [4])) (holds_context c6_rule171 [9, 5, 5, 3] []))
  have l0 := holds_refl [6, 4, 9, 4, 4]
  have l1 := holds_trans l0 (holds_context c6_rule171 [6, 4, 9] [])
  have r0 := holds_refl [9, 5, 5, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule993 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [-9, 6, 4, 9] [5, 5, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule992 [-9] [])) (holds_context c6_rule17 [] [5, 5, 3]))
  have l0 := holds_refl [-9, 6, 4, 9]
  have r0 := holds_refl [5, 5, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule994 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [6, 4, 9, 3] [9, 5, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule992 [] [3])) (holds_context c6_rule170 [9, 5, 5] []))
  have l0 := holds_refl [6, 4, 9, 3]
  have r0 := holds_refl [9, 5, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule995 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [5, 5, 3, -9] [-9, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule993 [] [-9])) (holds_context c6_rule16 [-9, 6, 4] []))
  have l0 := holds_refl [5, 5, 3, -9]
  have r0 := holds_refl [-9, 6, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule996 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [6, 9, 5, 5] [4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule994 [6] [])) (holds_context c6_rule172 [] [4, 9, 3]))
  have l0 := holds_refl [6, 9, 5, 5]
  have r0 := holds_refl [4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule997 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [-5, -9, 6, 4] [5, 3, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule995 [-5] [])) (holds_context c6_rule9 [] [5, 3, -9]))
  have l0 := holds_refl [-5, -9, 6, 4]
  have r0 := holds_refl [5, 3, -9]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule999 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [4, 9, -5, 3] [6, 9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule996 [] [-5])) (holds_context c6_rule8 [6, 9, 5] []))
  have l0 := holds_refl [4, 9, 3, -5]
  have l1 := holds_trans l0 (holds_context c6_rule30 [4, 9] [])
  have r0 := holds_refl [6, 9, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1000 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [4, 9, 5, 3] [6, 9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule996 [] [5])) (holds_context c6_rule175 [6, 9] []))
  have l0 := holds_refl [4, 9, 3, 5]
  have l1 := holds_trans l0 (holds_context c6_rule31 [4, 9] [])
  have r0 := holds_refl [6, 9, -5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1001 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [5, 3, -9, 4] [-5, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule997 [] [4])) (holds_context c6_rule171 [-5, -9, 6] []))
  have l0 := holds_refl [5, 3, -9, 4]
  have r0 := holds_refl [-5, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1007 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [5, 5, -9, 6] [3, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1001 [-5] [])) (holds_context c6_rule9 [] [3, -9, 4]))
  have l0 := holds_refl [-5, -5, -9, 6]
  have l1 := holds_trans l0 (holds_context c6_rule26 [] [-9, 6])
  have r0 := holds_refl [3, -9, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1008 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [3, -9, 6, 4] [5, 5, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1007 [] [6])) (holds_context c6_rule172 [5, 5, -9] []))
  have l0 := holds_refl [3, -9, 4, 6]
  have l1 := holds_trans l0 (holds_context c6_rule34 [3, -9] [])
  have r0 := holds_refl [5, 5, -9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1009 : Holds (normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [5, 5, -9, 4] [3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1008 [] [4])) (holds_context c6_rule171 [3, -9, 6] []))
  have l0 := holds_refl [5, 5, -9, 4]
  have r0 := holds_refl [3, -9, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1010 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [-5, 3, -9, 6] [5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1009 [-5] [])) (holds_context c6_rule9 [] [5, -9, 4]))
  have l0 := holds_refl [-5, 3, -9, 6]
  have r0 := holds_refl [5, -9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1011 : Holds (normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [5, 3, -9, 6] [-5, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1009 [5] [])) (holds_context c6_rule175 [] [-9, 4]))
  have l0 := holds_refl [5, 3, -9, 6]
  have r0 := holds_refl [-5, -9, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1014 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s5_s4) [6, 9, 3, 6, 7] [9, 6, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule990 [] [-7])) (holds_context c6_rule407 [9] []))
  have l0 := holds_refl [6, 4, 9, 4, -7]
  have l1 := holds_trans l0 (holds_context c6_rule55 [6] [])
  have l2 := holds_trans l1 (holds_context c6_rule355 [6, 9] [7])
  have r0 := holds_refl [9, 6, -7, 6]
  exact holds_factor (holds_trans (holds_symm l2) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1026 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [4, 9, 5, 5] [6, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule994 [4] [])) (holds_context c6_rule34 [] [4, 9, 3]))
  have l0 := holds_refl [4, 9, 5, 5]
  have r0 := holds_refl [6, 4, 4, 9, 3]
  have r1 := holds_trans r0 (holds_context c6_rule171 [6] [9, 3])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem c6_rule1029 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4) [6, 9, 6, 7, 7] [9, 5, 5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule994 [] [4])) (holds_context c6_rule296 [6] []))
  have l0 := holds_refl [9, 5, 5, 4]
  have r0 := holds_refl [6, 9, 6, 7, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1053 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [9, 3, 7, 4, 5] [6, 9, 5, -7] := by
  have h0 := c6_rule878
  have l0 := holds_refl [4, 9, -5, 3, -7]
  have l1 := holds_trans l0 (holds_context c6_rule999 [] [-7])
  have r0 := holds_refl [9, 3, 7, 4, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1055 : Holds (normalizedRelatorError .i_s1 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4) [3, -9, 4, 9, 5] [-9, 6, 9, -5] := by
  have h0 := c6_rule546
  have l0 := holds_refl [-9, 4, 9, 5, 3]
  have l1 := holds_trans l0 (holds_context c6_rule1000 [-9] [])
  have r0 := holds_refl [6, 7, 7, 4, 5]
  have r1 := holds_trans r0 (holds_context c6_rule658 [] [5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule1108 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [5, 7, 6, -9, 6] [-5, 4, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1010 [7] [])) (holds_context c6_rule182 [] [-9, 6]))
  have l0 := holds_refl [7, 5, -9, 4]
  have l1 := holds_trans l0 (holds_context c6_rule840 [] [])
  have r0 := holds_refl [3, 7, -5, -9, 6]
  have r1 := holds_trans r0 (holds_context c6_rule326 [] [-9, 6])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c6_rule1114 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [3, 7, 5, -9, 6] [5, -7, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1011 [7] [])) (holds_context c6_rule183 [] [-9, 6]))
  have l0 := holds_refl [7, -5, -9, 4]
  have l1 := holds_trans l0 (holds_context c6_rule424 [] [])
  have r0 := holds_refl [3, 7, 5, -9, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1120 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, 9, 6, -7, 6] [9, 3, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1014 [6] [])) (holds_context c6_rule172 [] [9, 3, 6, 7]))
  have l0 := holds_refl [6, 9, 6, -7, 6]
  have r0 := holds_refl [9, 3, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1130 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, 4, 5, 7, -5] [-9, 6, 9, 3] := by
  have h0 := c6_rule885
  have l0 := holds_refl [-9, 4, 9, 5, 5]
  have l1 := holds_trans l0 (holds_context c6_rule1026 [-9] [])
  have r0 := holds_refl [7, 4, 5, 7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1132 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ)) [9, 5, 5, 4, 7] [6, 9, 6, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1029 [] [7])) (holds_context c6_rule176 [6, 9, 6] []))
  have l0 := holds_refl [9, 5, 5, 4, 7]
  have r0 := holds_refl [6, 9, 6, -7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1155 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 9, 5, -7, -5] [9, 3, 7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1053 [] [-5])) (holds_context c6_rule8 [9, 3, 7, 4] []))
  have l0 := holds_refl [6, 9, 5, -7, -5]
  have r0 := holds_refl [9, 3, 7, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c6_rule1161 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ)) [3, -9, 6, 9, 3] [-9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1055 [] [5])) (holds_context c6_rule1026 [3, -9] []))
  have l0 := holds_refl [-9, 6, 9, -5, 5]
  have l1 := holds_trans l0 (holds_context c6_rule9 [-9, 6, 9] [])
  have r0 := holds_refl [3, -9, 6, 9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem c6_rule1162 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ)) [-9, 6, 9, 3] [3, -9, 6, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context c6_rule1161 [3] [])) (holds_context c6_rule170 [] [-9, 6, 9, 3]))
  have l0 := holds_refl [3, -9, 6, 9]
  have r0 := holds_refl [-9, 6, 9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
