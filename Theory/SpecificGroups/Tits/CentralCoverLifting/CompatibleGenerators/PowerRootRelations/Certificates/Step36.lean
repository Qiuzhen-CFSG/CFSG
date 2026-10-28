module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.Certificates.Step35

/-! Kernel-checked central word identities, chunk 36.
Generated from the signed-word trace in `source/certificate.json`.
Every step uses a literal source word or a proved earlier identity. -/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem c12_rule23 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ)) [-6] [6] := by
  have h0 := (split [6] [6] (rotate [] [6, 6] source4))
  have l0 := holds_refl [6]
  have r0 := holds_refl [-6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c12_rule24 : Holds ((normalizedRelatorError .i_s6) ^ (-1 : ℤ)) [-8] [8] := by
  have h0 := (split [8] [8] (rotate [] [8, 8] source5))
  have l0 := holds_refl [8]
  have r0 := holds_refl [-8]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c12_rule26 : Holds ((normalizedRelatorError .i_s3) ^ (-1 : ℤ)) [-5, -5] [5, 5] := by
  have h0 := (split [5, 5] [5, 5] (rotate [] [5, 5, 5, 5] source7))
  have l0 := holds_refl [5, 5]
  have r0 := holds_refl [-5, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c12_rule27 : Holds ((normalizedRelatorError .i_s5) ^ (-1 : ℤ)) [-7, -7] [7, 7] := by
  have h0 := (split [7, 7] [7, 7] (rotate [] [7, 7, 7, 7] source8))
  have l0 := holds_refl [7, 7]
  have r0 := holds_refl [-7, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem c12_rule29 : Holds ((normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ)) [4, 3] [3, 4] := by
  have h0 := (split [-3, -4] [3, 4] (rotate [] [-3, -4, 3, 4] source10))
  have l0 := holds_refl [-3, -4]
  have l1 := holds_trans l0 (holds_context c12_rule21 [] [-4])
  have l2 := holds_trans l1 (holds_context c12_rule22 [3] [])
  have r0 := holds_refl [-4, -3]
  have r1 := holds_trans r0 (holds_context c12_rule22 [] [-3])
  have r2 := holds_trans r1 (holds_context c12_rule21 [4] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r2))) (by central_nf)

theorem c12_rule33 : Holds (normalizedRelatorError .ii_s1_s5) [3, 7] [7, 3] := by
  have h0 := (split [3, 7] [-3, -7] (rotate [-3, -7] [3, 7] source12))
  have l0 := holds_refl [3, 7]
  have r0 := holds_refl [7, 3]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem c12_rule58 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [3, 4, 5, 5] [3, 8, 3, 8] := by
  have h0 := (split [-3, -8, 3, 8] [-5, -5, -4, -3] (rotate [] [-3, -8, 3, 8, -5, -5, -4, -3] source13))
  have l0 := holds_refl [-3, -8, 3, 8]
  have l1 := holds_trans l0 (holds_context c12_rule21 [] [-8, 3, 8])
  have l2 := holds_trans l1 (holds_context c12_rule24 [3] [3, 8])
  have r0 := holds_refl [3, 4, 5, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem c12_rule62 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .iii_s1_s6) [5, 5, 3, 4] [8, 3, 8, 3] := by
  have h0 := (split [-5, -5, -4, -3] [-3, -8, 3, 8] (rotate [-3, -8, 3, 8] [-5, -5, -4, -3] source13))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c12_rule26 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c12_rule22 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c12_rule21 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c12_rule29 [5, 5] [])
  have r0 := holds_refl [-8, -3, 8, 3]
  have r1 := holds_trans r0 (holds_context c12_rule24 [] [-3, 8, 3])
  have r2 := holds_trans r1 (holds_context c12_rule21 [8] [8, 3])
  exact holds_factor (holds_trans (holds_symm l4) (holds_trans h0 r2)) (by central_nf)

theorem c12_rule65 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ)) [4, 5, 5, 8] [3, 3, 8, 3] := by
  have h0 := (split [-3, -3, -8, 3] [8, -5, -5, -4] (rotate [-3, -8, 3, 8, -5, -5, -4] [-3] source13))
  have l0 := holds_refl [-3, -3, -8, 3]
  have l1 := holds_trans l0 (holds_context c12_rule21 [] [-3, -8, 3])
  have l2 := holds_trans l1 (holds_context c12_rule21 [3] [-8, 3])
  have l3 := holds_trans l2 (holds_context c12_rule24 [3, 3] [3])
  have r0 := holds_refl [4, 5, 5, -8]
  have r1 := holds_trans r0 (holds_context c12_rule24 [4, 5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

theorem c12_rule74 : Holds (normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * normalizedRelatorError .i_s6 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [3, 8, 3, 8] [-7, 6, 7, 6] := by
  have h0 := (split [-7, -6, 7, 6] [-5, -5, -4, -3] (rotate [] [-7, -6, 7, 6, -5, -5, -4, -3] source22))
  have l0 := holds_refl [-7, -6, 7, 6]
  have l1 := holds_trans l0 (holds_context c12_rule23 [-7] [7, 6])
  have r0 := holds_refl [3, 4, 5, 5]
  have r1 := holds_trans r0 (holds_context c12_rule58 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem c12_rule83 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [2, 7, 7, 3, 2] [-7, 6, 7, 6] := by
  have h0 := (split [3, 4, 5, 5] [2, -7, -7, -3, 2] (rotate [2] [3, 4, 5, 5, 2, -7, -7, -3] source36))
  have l0 := holds_refl [3, 4, 5, 5]
  have l1 := holds_trans l0 (holds_context c12_rule58 [] [])
  have l2 := holds_trans l1 (holds_context c12_rule74 [] [])
  have r0 := holds_refl [-2, 3, 7, 7, -2]
  have r1 := holds_trans r0 (holds_context c12_rule20 [] [3, 7, 7, -2])
  have r2 := holds_trans r1 (holds_context c12_rule33 [2] [7, -2])
  have r3 := holds_trans r2 (holds_context c12_rule33 [2, 7] [-2])
  have r4 := holds_trans r3 (holds_context c12_rule20 [2, 7, 7, 3] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r4))) (by central_nf)

theorem c12_rule94 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_r3) ^ (2 : ℤ)) [-7, 6, 7, 6] [8, 3, 8, 3] := by
  have h0 := (split [-5, -5, -4, -3] [-2, 3, 7, 7, -2] (rotate [3, 7, 7, -2] [-5, -5, -4, -3, -2] (inverted source36)))
  have l0 := holds_refl [-5, -5, -4, -3]
  have l1 := holds_trans l0 (holds_context c12_rule26 [] [-4, -3])
  have l2 := holds_trans l1 (holds_context c12_rule22 [5, 5] [-3])
  have l3 := holds_trans l2 (holds_context c12_rule21 [5, 5, 4] [])
  have l4 := holds_trans l3 (holds_context c12_rule29 [5, 5] [])
  have l5 := holds_trans l4 (holds_context c12_rule62 [] [])
  have r0 := holds_refl [2, -7, -7, -3, 2]
  have r1 := holds_trans r0 (holds_context c12_rule27 [2] [-3, 2])
  have r2 := holds_trans r1 (holds_context c12_rule21 [2, 7, 7] [2])
  have r3 := holds_trans r2 (holds_context c12_rule83 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l5) (holds_trans h0 r3))) (by central_nf)

theorem c12_rule183 : Holds (normalizedRelatorError .i_s1) [3, 3] [] := by
  have h0 := c12_rule4
  have l0 := holds_refl [3, -3]
  have l1 := holds_trans l0 (holds_context c12_rule21 [3] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem c12_rule186 : Holds (normalizedRelatorError .i_s6) [8, 8] [] := by
  have h0 := c12_rule14
  have l0 := holds_refl [8, -8]
  have l1 := holds_trans l0 (holds_context c12_rule24 [8] [])
  have r0 := holds_refl []
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem equation_r12_229 : (normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ) = 1 := by
  have h0 := (holds_trans (holds_symm (holds_context c12_rule65 [3] [])) (holds_context c12_rule58 [] [8]))
  have l0 := holds_refl [3, 3, 3, 8, 3]
  have l1 := holds_trans l0 (holds_context c12_rule183 [] [3, 8, 3])
  have r0 := holds_refl [3, 8, 3, 8, 8]
  have r1 := holds_trans r0 (holds_context c12_rule74 [] [8])
  have r2 := holds_trans r1 (holds_context c12_rule94 [] [8])
  have r3 := holds_trans r2 (holds_context c12_rule74 [8] [])
  have r4 := holds_trans r3 (holds_context c12_rule94 [8] [])
  have r5 := holds_trans r4 (holds_context c12_rule186 [] [3, 8, 3])
  have hh : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [3, 8, 3] [3, 8, 3] := holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r5)) (by central_nf)
  exact holds_cancel hh

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
