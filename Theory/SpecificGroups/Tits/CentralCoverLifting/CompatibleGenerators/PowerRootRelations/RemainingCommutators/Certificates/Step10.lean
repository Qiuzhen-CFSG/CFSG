module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step09

/-! Central word identities for the remaining normalized commutators, chunk 10.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule1834 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 8, -7, 5] [10, 4, 10, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1832 [-7] [])) (holds_context rc22_rule13 [] [10, 4, 10, -5]))
  have l0 := holds_refl [-7, 8, -7, 5]
  have r0 := holds_refl [10, 4, 10, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1837 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * normalizedRelatorError .ii_s1_s2 * normalizedRelatorError .ii_s1_s3 * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s8 * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [7, 10, 4, 10, 5] [8, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule676 [7] [])) (holds_context rc22_rule648 [] [8, -5]))
  have l0 := holds_refl [7, 10, 4, 10, 5]
  have r0 := holds_refl [-5, 7, -5, 8, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule1301 [-5] [-5])
  have r2 := holds_trans r1 (holds_context rc22_rule9 [] [8, -7, -5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule1838 : Holds ((normalizedRelatorError .i_r8) ^ (-2 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-2 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-2 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (5 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [-7, 8, -7, -5] [10, 4, 10, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1837 [-7] [])) (holds_context rc22_rule13 [] [10, 4, 10, 5]))
  have l0 := holds_refl [-7, 8, -7, -5]
  have r0 := holds_refl [10, 4, 10, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1839 : Holds ((normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, 4, 5] [7, 5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule676 [8] [])) (holds_context rc22_rule658 [] [8, -5]))
  have l0 := holds_refl [8, 10, 4, 10, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule327 [] [4, 10, 5])
  have l2 := holds_trans l1 (holds_context rc22_rule36 [10] [10, 5])
  have l3 := holds_trans l2 (holds_context rc22_rule327 [10, 4] [5])
  have l4 := holds_trans l3 (holds_context rc22_rule58 [10] [5])
  have l5 := holds_trans l4 (holds_context rc22_rule202 [] [6, 4, 5])
  have r0 := holds_refl [6, 8, 3, 8, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule1319 [] [8, -5])
  have r2 := holds_trans r1 (holds_context rc22_rule1310 [7] [-5])
  have r3 := holds_trans r2 (holds_context rc22_rule673 [] [-5])
  have r4 := holds_trans r3 (holds_context rc22_rule1346 [] [-5])
  have r5 := holds_trans r4 (holds_context rc22_rule1697 [] [])
  exact holds_factor (holds_trans (holds_symm l5) (holds_trans h0 r5)) (by central_nf)

theorem rc22_rule1841 : Holds ((normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [7, 5, -7, -5] [6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1839 [] [-5])) (holds_context rc22_rule8 [6, 4] []))
  have l0 := holds_refl [7, 5, -7, -5]
  have r0 := holds_refl [6, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1842 : Holds ((normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [-7, 6, 4] [5, -7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1841 [-7] [])) (holds_context rc22_rule13 [] [5, -7, -5]))
  have l0 := holds_refl [-7, 6, 4]
  have r0 := holds_refl [5, -7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1843 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [4, 7, 5, -7] [6, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1839 [4] [])) (holds_context rc22_rule35 [] [4, 5]))
  have l0 := holds_refl [4, 7, 5, -7]
  have r0 := holds_refl [6, 4, 4, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule199 [6] [5])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1844 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [4, 7, 5] [6, 5, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1843 [] [7])) (holds_context rc22_rule13 [4, 7, 5] []))
  have l0 := holds_refl [6, 5, 7]
  have r0 := holds_refl [4, 7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1845 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 7, 5, -7] [4, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1839 [6] [])) (holds_context rc22_rule200 [] [4, 5]))
  have l0 := holds_refl [6, 7, 5, -7]
  have r0 := holds_refl [4, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1846 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [4, 5, 7] [6, 7, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1845 [] [7])) (holds_context rc22_rule13 [6, 7, 5] []))
  have l0 := holds_refl [4, 5, 7]
  have r0 := holds_refl [6, 7, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1848 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s3_s5 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-7, 5, -7, -5] [-9, 4, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1841 [7, 7] [])) (holds_context rc22_rule204 [] [5, -7, -5]))
  have l0 := holds_refl [7, 7, 6, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule1799 [] [])
  have r0 := holds_refl [-7, 5, -7, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1852 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, -5, 6] [-7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1842 [] [6])) (holds_context rc22_rule35 [-7, 6] []))
  have l0 := holds_refl [5, -7, -5, 6]
  have r0 := holds_refl [-7, 6, 6, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule200 [-7] [4])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1853 : Holds ((normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, -5, 6] [-5, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1852 [-5] [])) (holds_context rc22_rule9 [] [-7, -5, 6]))
  have l0 := holds_refl [-5, -7, 4]
  have r0 := holds_refl [-7, -5, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1857 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [5, -7, -5, 4] [-7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1842 [] [4])) (holds_context rc22_rule199 [-7, 6] []))
  have l0 := holds_refl [5, -7, -5, 4]
  have r0 := holds_refl [-7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1858 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [-7, -5, 4] [-5, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1857 [-5] [])) (holds_context rc22_rule9 [] [-7, -5, 4]))
  have l0 := holds_refl [-5, -7, 6]
  have r0 := holds_refl [-7, -5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1861 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [6, 5, 7, -5] [4, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1844 [] [-5])) (holds_context rc22_rule8 [4, 7] []))
  have l0 := holds_refl [6, 5, 7, -5]
  have r0 := holds_refl [4, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1862 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5) [6, 4, 7] [5, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1861 [6] [])) (holds_context rc22_rule200 [] [5, 7, -5]))
  have l0 := holds_refl [6, 4, 7]
  have r0 := holds_refl [5, 7, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1871 : Holds (normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, -7, 4] [-5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1853 [7] [])) (holds_context rc22_rule12 [] [-5, 6]))
  have l0 := holds_refl [7, -5, -7, 4]
  have r0 := holds_refl [-5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1872 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [7, -5, -7] [-5, 6, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1871 [] [4])) (holds_context rc22_rule199 [7, -5, -7] []))
  have l0 := holds_refl [-5, 6, 4]
  have r0 := holds_refl [7, -5, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1877 : Holds ((normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * normalizedRelatorError .ii_s1_s5 * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ)) [6, -5, -7, 4] [5, -7, 3, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1853 [6] [])) (holds_context rc22_rule618 [] [6]))
  have l0 := holds_refl [6, -5, -7, 4]
  have r0 := holds_refl [5, -7, 3, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1887 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 7, -5, 7] [-9, 4, 9, 3] := by
  have h0 := rc22_rule1800
  have l0 := holds_refl [6, 4, 7, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule1862 [] [7])
  have r0 := holds_refl [-9, 4, 9, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1889 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s8) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ)) [8, 5, 7, -5] [10, 4, 10, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1862 [8] [])) (holds_context rc22_rule280 [] [4, 7]))
  have l0 := holds_refl [8, 5, 7, -5]
  have r0 := holds_refl [6, 8, 4, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule36 [6] [7])
  have r2 := holds_trans r1 (holds_context rc22_rule57 [] [7])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule1890 : Holds (normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [6, -5, 6, 4] [-5, -7, 4, 7] := by
  have h0 := rc22_rule1810
  have l0 := holds_refl [6, 7, -5, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule1872 [6] [])
  have r0 := holds_refl [-7, -5, 6, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule1853 [] [7])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule1900 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 5, 7, 6, 7] [-9, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule680 [4] [])) (holds_context rc22_rule661 [] [-7]))
  have l0 := holds_refl [4, -9, 4, 9, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule75 [] [4])
  have l2 := holds_trans l1 (holds_context rc22_rule648 [7] [4])
  have l3 := holds_trans l2 (holds_context rc22_rule1798 [] [4])
  have l4 := holds_trans l3 (holds_context rc22_rule199 [-9, 4, 9] [])
  have r0 := holds_refl [3, 6, 4, -7, -7]
  have r1 := holds_trans r0 (holds_context rc22_rule1266 [] [-7])
  have r2 := holds_trans r1 (holds_context rc22_rule1791 [5, 5] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l4) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule1901 : Holds ((normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s5 * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ)) [-5, -9, 4, 9] [5, 7, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1900 [-5] [])) (holds_context rc22_rule9 [] [5, 7, 6, 7]))
  have l0 := holds_refl [-5, -9, 4, 9]
  have r0 := holds_refl [5, 7, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1902 : Holds ((normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * normalizedRelatorError .ii_s1_s2 * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * normalizedRelatorError .v_s5_s4) [5, 5, 7, 6] [-9, 4, 9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1900 [] [-7])) (holds_context rc22_rule12 [5, 5, 7, 6] []))
  have l0 := holds_refl [-9, 4, 9, -7]
  have r0 := holds_refl [5, 5, 7, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule1918 : Holds (normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ)) [5, 5, 4, 7, 6] [3, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule684 [] [6])) (holds_context rc22_rule200 [3, 6, 7] []))
  have l0 := holds_refl [7, 5, 5, 4, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule1745 [] [6])
  have r0 := holds_refl [3, 6, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule1919 : Holds ((normalizedRelatorError .i_s2) ^ (-1 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * normalizedRelatorError .ii_s1_s5 * (normalizedRelatorError .iii_s1_s6) ^ (-5 : ℤ) * normalizedRelatorError .iv_s2_s4 * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (4 : ℤ)) [-5, 3, 6, 7] [5, 4, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule1918 [-5] [])) (holds_context rc22_rule9 [] [5, 4, 7, 6]))
  have l0 := holds_refl [-5, 3, 6, 7]
  have r0 := holds_refl [5, 4, 7, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2071 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-2 : ℤ)) [10, 3, 10, 3, 9] [5, 5, 4, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule725 [4] [])) (holds_context rc22_rule30 [] [-9, 6, 4]))
  have l0 := holds_refl [4, 5, 5, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule377 [] [-9])
  have r0 := holds_refl [3, 4, -9, 6, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule1238 [] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule2083 : Holds ((normalizedRelatorError .i_r8) ^ (-6 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-3 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (12 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (3 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (4 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (8 : ℤ)) [7, 7, 6, 8, -9] [8, 3, -9, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule726 [8] [])) (holds_context rc22_rule293 [] [-9, 4]))
  have l0 := holds_refl [8, 3, -9, 6]
  have r0 := holds_refl [3, 4, 8, -9, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule1682 [3] [])
  have r2 := holds_trans r1 (holds_context rc22_rule34 [] [8, -7, -9])
  have r3 := holds_trans r2 (holds_context rc22_rule1291 [7] [-9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r3))) (by central_nf)

theorem rc22_rule2094 : Holds ((normalizedRelatorError .i_r8) ^ (2 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * normalizedRelatorError .i_s2 * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (3 : ℤ) * normalizedRelatorError .iv_s2_s4 * normalizedRelatorError .iv_s7_s2 * normalizedRelatorError .v_s7_s4 * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [4, -5, -9, 4] [-7, 5, -7, -9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule728 [4] [])) (holds_context rc22_rule207 [] [-9, 6]))
  have l0 := holds_refl [4, -5, -9, 4]
  have r0 := holds_refl [3, 4, 5, -9, 6]
  have r1 := holds_trans r0 (holds_context rc22_rule532 [] [6])
  have r2 := holds_trans r1 (holds_context rc22_rule670 [2] [])
  have r3 := holds_trans r2 (holds_context rc22_rule758 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule2134 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [4, -7, 5] [5, -7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule867 [-5] [])) (holds_context rc22_rule48 [] [8, 5, 2]))
  have l0 := holds_refl [-5, -9, 4, 9, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule1901 [] [7])
  have l2 := holds_trans l1 (holds_context rc22_rule1792 [5, 7] [])
  have l3 := holds_trans l2 (holds_context rc22_rule204 [5] [6])
  have r0 := holds_refl [2, -7, 8, 5, 2]
  have r1 := holds_trans r0 (holds_context rc22_rule1376 [2] [])
  have r2 := holds_trans r1 (holds_context rc22_rule197 [] [4, -7, 5])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule2143 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [4, 5, 4, -7] [5, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2134 [] [6])) (holds_context rc22_rule571 [4] []))
  have l0 := holds_refl [5, -7, 6, 6]
  have l1 := holds_trans l0 (holds_context rc22_rule200 [5, -7] [])
  have r0 := holds_refl [4, 5, 4, -7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2144 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [4, 5, 4] [5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2143 [] [7])) (holds_context rc22_rule13 [4, 5, 4] []))
  have l0 := holds_refl [5, -7, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule13 [5] [])
  have r0 := holds_refl [4, 5, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2145 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [4, 5] [5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2144 [4] [])) (holds_context rc22_rule199 [] [5, 4]))
  have l0 := holds_refl [4, 5]
  have r0 := holds_refl [5, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2146 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [5, 4, -5] [4] := by
  have h0 := rc22_rule379
  have l0 := holds_refl [-5, 4, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule2145 [-5] [])
  have l2 := holds_trans l1 (holds_context rc22_rule9 [] [4])
  have r0 := holds_refl [5, 4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2147 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (-1 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [4, -5] [-5, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2146 [-5] [])) (holds_context rc22_rule9 [] [4, -5]))
  have l0 := holds_refl [-5, 4]
  have r0 := holds_refl [4, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2148 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s4 * normalizedRelatorError .i_s6 * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [6, 5, 4] [7, 5, -7] := by
  have h0 := rc22_rule1839
  have l0 := holds_refl [6, 4, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule2145 [6] [])
  have r0 := holds_refl [7, 5, -7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule2149 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-2 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (3 : ℤ)) [6, 7, 5] [5, 4, 7] := by
  have h0 := rc22_rule1846
  have l0 := holds_refl [4, 5, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule2145 [] [7])
  have r0 := holds_refl [6, 7, 5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule2150 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * normalizedRelatorError .i_s2 * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-1 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (3 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (4 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-2 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [8, 5, 4] [3, 8, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2145 [8] [])) (holds_context rc22_rule36 [] [5]))
  have l0 := holds_refl [8, 5, 4]
  have r0 := holds_refl [4, 8, 5]
  have r1 := holds_trans r0 (holds_context rc22_rule383 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
