module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators.Certificates.Step21

/-! Central word identities for the remaining normalized commutators, chunk 22.
Each equation is checked from the literal Parrott words by `WordCalculus`.
The replay input is `../source/certificate.json`; no relator vanishing is assumed.
Source: Parrott (1972), §5, p.683. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem rc22_rule3838 : Holds ((normalizedRelatorError .i_r8) ^ (-83 : ℤ) * (normalizedRelatorError .i_s1) ^ (-5 : ℤ) * (normalizedRelatorError .i_s2) ^ (-60 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (18 : ℤ) * (normalizedRelatorError .i_s3) ^ (-57 : ℤ) * (normalizedRelatorError .i_s5) ^ (31 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-140 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (63 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (120 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-21 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (28 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (26 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (20 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-40 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (24 : ℤ) * (normalizedRelatorError .viii_s2) ^ (10 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-22 : ℤ) * (normalizedRelatorError .viii_s7) ^ (12 : ℤ) * (normalizedRelatorError .viii_s3) ^ (68 : ℤ) * (normalizedRelatorError .viii_r3) ^ (15 : ℤ)) [9, 5, 8, 5] [8, 3, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3770 [3] [])) (holds_context rc22_rule198 [] [8, 3, 9]))
  have l0 := holds_refl [3, 6, 9, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule3279 [] [])
  have r0 := holds_refl [8, 3, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3841 : Holds ((normalizedRelatorError .i_r8) ^ (34 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (21 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * normalizedRelatorError .i_s6 * (normalizedRelatorError .i_s3) ^ (20 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (71 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-25 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-59 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-13 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (20 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (10 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-34 : ℤ) * (normalizedRelatorError .viii_r3) ^ (5 : ℤ)) [8, 9, 6, -9] [-7, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3770 [-9] [])) (holds_context rc22_rule3722 [] [9]))
  have l0 := holds_refl [-9, 6, 9, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule3756 [] [8])
  have l2 := holds_trans l1 (holds_context rc22_rule3723 [] [])
  have r0 := holds_refl [8, -9, 6, 9]
  have r1 := holds_trans r0 (holds_context rc22_rule3756 [8] [])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule3842 : Holds ((normalizedRelatorError .i_r8) ^ (98 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (81 : ℤ) * (normalizedRelatorError .i_s4) ^ (-9 : ℤ) * (normalizedRelatorError .i_s6) ^ (-25 : ℤ) * (normalizedRelatorError .i_s3) ^ (75 : ℤ) * (normalizedRelatorError .i_s5) ^ (-51 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (175 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-71 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-167 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (41 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-39 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-34 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-23 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-14 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (39 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-31 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-17 : ℤ) * (normalizedRelatorError .viii_s4) ^ (8 : ℤ) * (normalizedRelatorError .viii_s1) ^ (25 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-62 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-46 : ℤ)) [5, 9, 3, 8] [3, 9, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3771 [-5] [])) (holds_context rc22_rule9 [] [3, 9, 7]))
  have l0 := holds_refl [-5, 9, 6, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule3581 [] [8])
  have r0 := holds_refl [3, 9, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3857 : Holds ((normalizedRelatorError .i_r8) ^ (44 : ℤ) * (normalizedRelatorError .i_s1) ^ (-12 : ℤ) * (normalizedRelatorError .i_s2) ^ (36 : ℤ) * (normalizedRelatorError .i_s4) ^ (-11 : ℤ) * (normalizedRelatorError .i_s6) ^ (-11 : ℤ) * (normalizedRelatorError .i_s3) ^ (33 : ℤ) * (normalizedRelatorError .i_s5) ^ (-39 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (57 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-18 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-89 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (20 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-18 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-15 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-9 : ℤ) * (normalizedRelatorError .viii_s4) ^ (13 : ℤ) * (normalizedRelatorError .viii_s1) ^ (7 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-10 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-47 : ℤ)) [3, -9, -5, 3] [-7, -9, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3778 [6] [])) (holds_context rc22_rule1321 [] [-9]))
  have l0 := holds_refl [6, -9, 5, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule3648 [] [3])
  have r0 := holds_refl [8, -7, -9]
  have r1 := holds_trans r0 (holds_context rc22_rule2175 [] [])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule3858 : Holds ((normalizedRelatorError .i_r8) ^ (-4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-6 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-13 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-23 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-13 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-9 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-11 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (8 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (19 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-25 : ℤ)) [-9, 5, 3, 6] [2, 5, 3, 2] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3778 [] [6])) (holds_context rc22_rule2836 [7] []))
  have l0 := holds_refl [-9, 5, 3, 6]
  have r0 := holds_refl [7, 3, -9, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule2955 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule3860 : Holds ((normalizedRelatorError .i_r8) ^ (28 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (21 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (21 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (58 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-21 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-41 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-5 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (14 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-12 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-3 : ℤ)) [5, 8, 5, 10] [3, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3782 [5] [])) (holds_context rc22_rule8 [] [3, 10, 4]))
  have l0 := holds_refl [5, 8, 5, 10]
  have r0 := holds_refl [3, 10, 4]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3863 : Holds ((normalizedRelatorError .i_r8) ^ (-67 : ℤ) * (normalizedRelatorError .i_s1) ^ (-3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-51 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (10 : ℤ) * (normalizedRelatorError .i_s3) ^ (-49 : ℤ) * (normalizedRelatorError .i_s5) ^ (27 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-128 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (44 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (107 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-27 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-28 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (25 : ℤ) * (normalizedRelatorError .viii_s2) ^ (10 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-18 : ℤ) * (normalizedRelatorError .viii_s7) ^ (7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (50 : ℤ) * (normalizedRelatorError .viii_r3) ^ (20 : ℤ)) [3, 9, 9, 6] [9, 9, 7, 7] := by
  have h0 := rc22_rule3666
  have l0 := holds_refl [3, 6, 9, 9]
  have l1 := holds_trans l0 (holds_context rc22_rule3787 [3] [])
  have r0 := holds_refl [9, 9, 7, 7]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3874 : Holds ((normalizedRelatorError .i_r8) ^ (-19 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-3 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-33 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (24 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (15 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-21 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (16 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-15 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (9 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (12 : ℤ) * (normalizedRelatorError .viii_s3) ^ (30 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-26 : ℤ)) [6, 7, -9, 5] [-9, 3, 8] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3793 [] [5])) (holds_context rc22_rule9 [-9, 3, 8] []))
  have l0 := holds_refl [6, 7, -9, 5]
  have r0 := holds_refl [-9, 3, 8]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3882 : Holds ((normalizedRelatorError .i_r8) ^ (6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-7 : ℤ) * (normalizedRelatorError .i_s4) ^ (6 : ℤ) * (normalizedRelatorError .i_s6) ^ (9 : ℤ) * (normalizedRelatorError .i_s3) ^ (-4 : ℤ) * (normalizedRelatorError .i_s5) ^ (5 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (2 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (16 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (14 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (5 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-6 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-14 : ℤ) * (normalizedRelatorError .viii_r3) ^ (16 : ℤ)) [6, -9, 3, 8] [-7, -9, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3796 [6] [])) (holds_context rc22_rule3715 [] [6]))
  have l0 := holds_refl [6, -9, 3, 8]
  have r0 := holds_refl [-7, -9, -5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3887 : Holds ((normalizedRelatorError .i_r8) ^ (-37 : ℤ) * (normalizedRelatorError .i_s1) ^ (3 : ℤ) * (normalizedRelatorError .i_s2) ^ (-30 : ℤ) * (normalizedRelatorError .i_s4) ^ (10 : ℤ) * (normalizedRelatorError .i_s6) ^ (16 : ℤ) * (normalizedRelatorError .i_s3) ^ (-28 : ℤ) * (normalizedRelatorError .i_s5) ^ (22 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-52 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (30 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (56 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (24 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (24 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-13 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (7 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-9 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (20 : ℤ) * (normalizedRelatorError .viii_r3) ^ (22 : ℤ)) [9, -7, 4, 8] [5, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3803 [] [4])) (holds_context rc22_rule199 [5, 9, 3] []))
  have l0 := holds_refl [9, -7, 8, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule36 [9, -7] [])
  have r0 := holds_refl [5, 9, 3]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3890 : Holds ((normalizedRelatorError .i_r8) ^ (44 : ℤ) * (normalizedRelatorError .i_s1) ^ (-11 : ℤ) * (normalizedRelatorError .i_s2) ^ (25 : ℤ) * (normalizedRelatorError .i_s4) ^ (-6 : ℤ) * (normalizedRelatorError .i_s6) ^ (-4 : ℤ) * (normalizedRelatorError .i_s3) ^ (25 : ℤ) * (normalizedRelatorError .i_s5) ^ (-31 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (44 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-67 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-10 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (7 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s4) ^ (8 : ℤ) * (normalizedRelatorError .viii_s1) ^ (5 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-18 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-30 : ℤ)) [-7, -9, 8, 3] [3, -9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3810 [-7] [])) (holds_context rc22_rule13 [] [3, -9, -5]))
  have l0 := holds_refl [-7, -9, 8, 3]
  have r0 := holds_refl [3, -9, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3903 : Holds ((normalizedRelatorError .i_r8) ^ (26 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (19 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (18 : ℤ) * (normalizedRelatorError .i_s5) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (55 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-21 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-36 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-4 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (13 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-12 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-24 : ℤ)) [8, -7, -5, 8] [5, 6, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3831 [] [8])) (holds_context rc22_rule201 [5, 6, 7] []))
  have l0 := holds_refl [8, -7, -5, 8]
  have r0 := holds_refl [5, 6, 7]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3906 : Holds ((normalizedRelatorError .i_r8) ^ (83 : ℤ) * (normalizedRelatorError .i_s1) ^ (5 : ℤ) * (normalizedRelatorError .i_s2) ^ (60 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-18 : ℤ) * (normalizedRelatorError .i_s3) ^ (57 : ℤ) * (normalizedRelatorError .i_s5) ^ (-31 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (140 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-63 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-120 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (21 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-28 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-26 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-20 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (40 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-24 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s1) ^ (22 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-12 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-68 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-15 : ℤ)) [-9, 8, 3, 9] [5, 8, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3838 [-9] [])) (holds_context rc22_rule17 [] [5, 8, 5]))
  have l0 := holds_refl [-9, 8, 3, 9]
  have r0 := holds_refl [5, 8, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3925 : Holds ((normalizedRelatorError .i_r8) ^ (111 : ℤ) * (normalizedRelatorError .i_s1) ^ (9 : ℤ) * (normalizedRelatorError .i_s2) ^ (81 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-22 : ℤ) * (normalizedRelatorError .i_s3) ^ (78 : ℤ) * (normalizedRelatorError .i_s5) ^ (-39 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (198 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-84 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-161 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (33 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-34 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-31 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-25 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (54 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-36 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-14 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (30 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-16 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-92 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-18 : ℤ)) [8, 3, 9, 10] [9, 3, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3860 [9] [])) (holds_context rc22_rule3838 [] [10]))
  have l0 := holds_refl [9, 3, 10, 4]
  have r0 := holds_refl [8, 3, 9, 10]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3926 : Holds ((normalizedRelatorError .i_r8) ^ (13 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (29 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-26 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (10 : ℤ)) [-7, -9, -5, 6] [7, -9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3874 [6] [])) (holds_context rc22_rule200 [] [7, -9, 5]))
  have l0 := holds_refl [6, -9, 3, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule3882 [] [])
  have r0 := holds_refl [7, -9, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3941 : Holds ((normalizedRelatorError .i_r8) ^ (-61 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (-51 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (10 : ℤ) * (normalizedRelatorError .i_s3) ^ (-47 : ℤ) * (normalizedRelatorError .i_s5) ^ (29 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-123 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (41 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (111 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-30 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (15 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (14 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (25 : ℤ) * (normalizedRelatorError .viii_s2) ^ (10 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (42 : ℤ) * (normalizedRelatorError .viii_r3) ^ (24 : ℤ)) [3, 9, 7] [9, -7, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3887 [] [8])) (holds_context rc22_rule201 [9, -7, 4] []))
  have l0 := holds_refl [5, 9, 3, 8]
  have l1 := holds_trans l0 (holds_context rc22_rule3842 [] [])
  have r0 := holds_refl [9, -7, 4]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3957 : Holds ((normalizedRelatorError .i_r8) ^ (8 : ℤ) * (normalizedRelatorError .i_s1) ^ (13 : ℤ) * (normalizedRelatorError .i_s2) ^ (13 : ℤ) * (normalizedRelatorError .i_s6) ^ (-11 : ℤ) * (normalizedRelatorError .i_s3) ^ (11 : ℤ) * (normalizedRelatorError .i_s5) ^ (10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (44 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-34 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-16 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (21 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (21 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s1) ^ (9 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-26 : ℤ) * (normalizedRelatorError .viii_r3) ^ (22 : ℤ)) [3, -9, -5, 9] [4, 8, 7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3906 [-7] [])) (holds_context rc22_rule3890 [] [9]))
  have l0 := holds_refl [-7, 5, 8, 5]
  have l1 := holds_trans l0 (holds_context rc22_rule1294 [] [5])
  have l2 := holds_trans l1 (holds_context rc22_rule2859 [] [])
  have l3 := holds_trans l2 (holds_context rc22_rule3682 [] [])
  have r0 := holds_refl [3, -9, -5, 9]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3961 : Holds ((normalizedRelatorError .i_r8) ^ (-13 : ℤ) * (normalizedRelatorError .i_s2) ^ (-4 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (3 : ℤ) * (normalizedRelatorError .i_s3) ^ (-3 : ℤ) * (normalizedRelatorError .i_s5) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-29 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (14 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (26 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-10 : ℤ)) [7, 7, -9, 5] [-9, -5, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3926 [7] [])) (holds_context rc22_rule12 [] [-9, -5, 6]))
  have l0 := holds_refl [7, 7, -9, 5]
  have r0 := holds_refl [-9, -5, 6]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3976 : Holds ((normalizedRelatorError .i_r8) ^ (-74 : ℤ) * (normalizedRelatorError .i_s1) ^ (6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-51 : ℤ) * (normalizedRelatorError .i_s4) ^ (7 : ℤ) * (normalizedRelatorError .i_s6) ^ (16 : ℤ) * (normalizedRelatorError .i_s3) ^ (-48 : ℤ) * (normalizedRelatorError .i_s5) ^ (38 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-121 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (46 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (126 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-22 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (25 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (21 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (9 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (20 : ℤ) * (normalizedRelatorError .viii_s2) ^ (12 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (46 : ℤ) * (normalizedRelatorError .viii_r3) ^ (30 : ℤ)) [3, 4, 9, 7] [6, 9, -7] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3941 [4] [])) (holds_context rc22_rule30 [] [9, 7]))
  have l0 := holds_refl [4, 9, -7, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule2653 [] [])
  have r0 := holds_refl [3, 4, 9, 7]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule3977 : Holds ((normalizedRelatorError .i_r8) ^ (63 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (51 : ℤ) * normalizedRelatorError .i_s4 * (normalizedRelatorError .i_s6) ^ (-10 : ℤ) * (normalizedRelatorError .i_s3) ^ (47 : ℤ) * (normalizedRelatorError .i_s5) ^ (-29 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (123 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-41 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-111 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (30 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-15 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-14 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-25 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s1) ^ (16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-43 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-24 : ℤ)) [9, -7, 2, 8] [3, 2, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3941 [] [2])) (holds_context rc22_rule46 [3] []))
  have l0 := holds_refl [9, -7, 4, 2]
  have l1 := holds_trans l0 (holds_context rc22_rule42 [9, -7] [])
  have r0 := holds_refl [3, 2, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule3992 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s1) ^ (-13 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s5) ^ (-16 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (20 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-17 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (9 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-15 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (11 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-5 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-8 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-12 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (8 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s7) ^ (4 : ℤ) * (normalizedRelatorError .viii_s3) ^ (16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-26 : ℤ)) [4, 8, 7, 10] [-7, 3, 10, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3957 [] [10])) (holds_context rc22_rule3552 [3] []))
  have l0 := holds_refl [4, 8, 7, 10]
  have r0 := holds_refl [3, -7, 10, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule33 [] [10, 4])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule3995 : Holds ((normalizedRelatorError .i_r8) ^ (13 : ℤ) * (normalizedRelatorError .i_s2) ^ (4 : ℤ) * (normalizedRelatorError .i_s4) ^ (-2 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (3 : ℤ) * (normalizedRelatorError .i_s5) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (29 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-14 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-26 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-4 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (12 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-6 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-9 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (10 : ℤ)) [7, -9, -5, 6] [-7, -9, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3961 [7] [])) (holds_context rc22_rule204 [] [-9, 5]))
  have l0 := holds_refl [7, -9, -5, 6]
  have r0 := holds_refl [-7, -9, 5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule4023 : Holds ((normalizedRelatorError .i_r8) ^ (74 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (51 : ℤ) * (normalizedRelatorError .i_s4) ^ (-7 : ℤ) * (normalizedRelatorError .i_s6) ^ (-16 : ℤ) * (normalizedRelatorError .i_s3) ^ (48 : ℤ) * (normalizedRelatorError .i_s5) ^ (-37 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (121 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-46 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-126 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (22 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-25 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-21 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-9 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-20 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-12 : ℤ) * (normalizedRelatorError .viii_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_s1) ^ (16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-46 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-30 : ℤ)) [6, 9, 7, 7] [3, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3976 [] [-7])) (holds_context rc22_rule12 [3, 4, 9] []))
  have l0 := holds_refl [6, 9, -7, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [6, 9] [])
  have r0 := holds_refl [3, 4, 9]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule4027 : Holds ((normalizedRelatorError .i_r8) ^ (62 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (50 : ℤ) * (normalizedRelatorError .i_s6) ^ (-11 : ℤ) * (normalizedRelatorError .i_s3) ^ (46 : ℤ) * (normalizedRelatorError .i_s5) ^ (-29 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (116 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-39 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-106 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (31 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-17 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-9 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-12 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (24 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-24 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_s1) ^ (15 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-40 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-26 : ℤ)) [9, 9, -7, 8] [2, 3, 2, 5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3977 [2] [])) (holds_context rc22_rule365 [] [8]))
  have l0 := holds_refl [2, 3, 2, 5]
  have r0 := holds_refl [-9, -5, -9, 8]
  have r1 := holds_trans r0 (holds_context rc22_rule3028 [-9] [8])
  have r2 := holds_trans r1 (holds_context rc22_rule29 [] [-7, 8])
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r2))) (by central_nf)

theorem rc22_rule4044 : Holds ((normalizedRelatorError .i_r8) ^ (-20 : ℤ) * (normalizedRelatorError .i_s2) ^ (-11 : ℤ) * (normalizedRelatorError .i_s4) ^ (5 : ℤ) * (normalizedRelatorError .i_s6) ^ (7 : ℤ) * (normalizedRelatorError .i_s3) ^ (-9 : ℤ) * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-28 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (19 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (32 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (13 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (12 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (8 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s3_s5) ^ (-10 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s7) ^ (6 : ℤ) * (normalizedRelatorError .viii_s3) ^ (16 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [-7, -9, 5, 4] [7, 4, -9, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3995 [] [4])) (holds_context rc22_rule3211 [7] []))
  have l0 := holds_refl [-7, -9, 5, 4]
  have r0 := holds_refl [7, 4, -9, -5]
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule4351 : Holds ((normalizedRelatorError .i_r8) ^ (46 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (38 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-8 : ℤ) * normalizedRelatorError .i_s8 * (normalizedRelatorError .i_s3) ^ (36 : ℤ) * (normalizedRelatorError .i_s5) ^ (-30 : ℤ) * (normalizedRelatorError .i_s7) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (80 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-22 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-90 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (15 : ℤ) * (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-7 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (14 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-11 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s4) ^ (6 : ℤ) * (normalizedRelatorError .viii_s1) ^ (12 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-24 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-32 : ℤ)) [10, 3, 10, 3] [9, 6, 9, 3] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2071 [] [-9])) (holds_context rc22_rule16 [10, 3, 10, 3] []))
  have l0 := holds_refl [5, 5, 4, -9, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule29 [5, 5, 4] [])
  have l2 := holds_trans l1 (holds_context rc22_rule3590 [] [9])
  have l3 := holds_trans l2 (holds_context rc22_rule3123 [9] [])
  have r0 := holds_refl [10, 3, 10, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule4709 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * (normalizedRelatorError .i_s3) ^ (2 : ℤ) * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-5 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [5, 5, 7, 10, 4] [8, -7, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2294 [] [10, 4])) (holds_context rc22_rule56 [7, 3] []))
  have l0 := holds_refl [5, 5, 7, 10, 4]
  have r0 := holds_refl [7, 3, 6, 8, 10]
  have r1 := holds_trans r0 (holds_context rc22_rule648 [] [8, 10])
  have r2 := holds_trans r1 (holds_context rc22_rule1301 [-5] [10])
  have r3 := holds_trans r2 (holds_context rc22_rule9 [] [8, -7, 10])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule4711 : Holds ((normalizedRelatorError .i_r8) ^ (3 : ℤ) * (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * (normalizedRelatorError .i_s2) ^ (3 : ℤ) * (normalizedRelatorError .i_s4) ^ (-1 : ℤ) * (normalizedRelatorError .i_s6) ^ (-3 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .i_s5) ^ (-2 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-6 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-5 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (-2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_r3) ^ (-4 : ℤ)) [-5, 7, 10, 4] [5, 8, -7, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule4709 [5] [])) (holds_context rc22_rule203 [] [7, 10, 4]))
  have l0 := holds_refl [5, 8, -7, 10]
  have r0 := holds_refl [-5, 7, 10, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule4730 : Holds ((normalizedRelatorError .i_r1) ^ (-5 : ℤ) * normalizedRelatorError .i_r8 * (normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (2 : ℤ) * (normalizedRelatorError .i_s4) ^ (-3 : ℤ) * (normalizedRelatorError .i_s6) ^ (-5 : ℤ) * normalizedRelatorError .i_s3 * (normalizedRelatorError .ii_s1_s2) ^ (-5 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * normalizedRelatorError .iii_s1_s6 * (normalizedRelatorError .iv_s2_s4) ^ (-9 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (2 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .vi_s1_r1) ^ (2 : ℤ) * normalizedRelatorError .vii_s5 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-1 : ℤ)) [7, 1, 5, 5, -7] [5, 1, -9, -7, 5] := by
  have h0 := rc22_rule1464
  have l0 := holds_refl [7, 1, -7, 3, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule2302 [7, 1] [])
  have r0 := holds_refl [5, 1, -9, -7, 5]
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r0)) (by central_nf)

theorem rc22_rule4814 : Holds ((normalizedRelatorError .i_r8) ^ (35 : ℤ) * (normalizedRelatorError .i_s1) ^ (2 : ℤ) * (normalizedRelatorError .i_s2) ^ (19 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-2 : ℤ) * (normalizedRelatorError .i_s3) ^ (18 : ℤ) * (normalizedRelatorError .i_s5) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (67 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-25 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-55 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (9 : ℤ) * normalizedRelatorError .iv_s2_s8 * (normalizedRelatorError .iv_s7_s2) ^ (-11 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (18 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-12 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (8 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-8 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-32 : ℤ) * (normalizedRelatorError .viii_r3) ^ (4 : ℤ)) [5, 3, 10, 6, 4] [6, 8, -5, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2330 [] [10, 4])) (holds_context rc22_rule56 [6, -5] []))
  have l0 := holds_refl [5, 3, 6, 10, 4]
  have l1 := holds_trans l0 (holds_context rc22_rule331 [5, 3] [4])
  have r0 := holds_refl [6, -5, 6, 8, 10]
  have r1 := holds_trans r0 (holds_context rc22_rule2273 [] [8, 10])
  have r2 := holds_trans r1 (holds_context rc22_rule3505 [] [10])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r2)) (by central_nf)

theorem rc22_rule5016 : Holds ((normalizedRelatorError .i_r8) ^ (66 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (47 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-15 : ℤ) * (normalizedRelatorError .i_s3) ^ (45 : ℤ) * (normalizedRelatorError .i_s5) ^ (-30 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (116 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-44 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-110 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (22 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-24 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-22 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-46 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-22 : ℤ)) [9, 5, 5, 6, 4] [3, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2486 [] [-7])) (holds_context rc22_rule1872 [9, -5] []))
  have l0 := holds_refl [6, 9, -7, -7]
  have l1 := holds_trans l0 (holds_context rc22_rule28 [6, 9] [])
  have l2 := holds_trans l1 (holds_context rc22_rule4023 [] [])
  have r0 := holds_refl [9, -5, -5, 6, 4]
  have r1 := holds_trans r0 (holds_context rc22_rule27 [9] [6, 4])
  exact holds_factor (holds_symm (holds_trans (holds_symm l2) (holds_trans h0 r1))) (by central_nf)

theorem rc22_rule5017 : Holds ((normalizedRelatorError .i_r8) ^ (66 : ℤ) * (normalizedRelatorError .i_s1) ^ (-2 : ℤ) * (normalizedRelatorError .i_s2) ^ (47 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (-15 : ℤ) * (normalizedRelatorError .i_s3) ^ (45 : ℤ) * (normalizedRelatorError .i_s5) ^ (-30 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (116 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-44 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-110 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (22 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-24 : ℤ) * normalizedRelatorError .iv_s2_s6 * (normalizedRelatorError .iv_s2_s8) ^ (-20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-6 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-22 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-10 : ℤ) * (normalizedRelatorError .viii_s4) ^ (3 : ℤ) * (normalizedRelatorError .viii_s1) ^ (16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-46 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-22 : ℤ)) [5, 5, 6, 4] [-9, 3, 4, 9] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule5016 [-9] [])) (holds_context rc22_rule17 [] [5, 5, 6, 4]))
  have l0 := holds_refl [-9, 3, 4, 9]
  have r0 := holds_refl [5, 5, 6, 4]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule5027 : Holds ((normalizedRelatorError .i_r8) ^ (-11 : ℤ) * (normalizedRelatorError .i_s1) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-6 : ℤ) * (normalizedRelatorError .i_s4) ^ (3 : ℤ) * (normalizedRelatorError .i_s6) ^ (2 : ℤ) * (normalizedRelatorError .i_s3) ^ (-5 : ℤ) * (normalizedRelatorError .i_s5) ^ (8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-12 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (6 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (21 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (6 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (2 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-3 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * normalizedRelatorError .viii_s7 * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [-5, 7, -9, 10, 6] [-7, -9, 7, 10] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2492 [] [10])) (holds_context rc22_rule331 [-5, 7, -9] []))
  have l0 := holds_refl [-7, 5, -9, 10]
  have l1 := holds_trans l0 (holds_context rc22_rule3023 [-7] [10])
  have r0 := holds_refl [-5, 7, -9, 10, 6]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule5168 : Holds ((normalizedRelatorError .i_r8) ^ (-51 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s2) ^ (-43 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-42 : ℤ) * (normalizedRelatorError .i_s5) ^ (18 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-125 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (36 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (102 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (20 : ℤ) * (normalizedRelatorError .viii_s2) ^ (8 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (46 : ℤ) * (normalizedRelatorError .viii_r3) ^ (7 : ℤ)) [-9, 3, 4, 9, 3] [5, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule2657 [6, 4] [])) (holds_context rc22_rule2430 [] [4, 7]))
  have l0 := holds_refl [6, 4, 5, 5, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule2145 [6] [5, 3])
  have l2 := holds_trans l1 (holds_context rc22_rule2148 [] [5, 3])
  have l3 := holds_trans l2 (holds_context rc22_rule2282 [] [5, 3])
  have l4 := holds_trans l3 (holds_context rc22_rule655 [-5] [3])
  have l5 := holds_trans l4 (holds_context rc22_rule2313 [-5] [3])
  have l6 := holds_trans l5 (holds_context rc22_rule27 [] [6, 4, 3])
  have l7 := holds_trans l6 (holds_context rc22_rule5017 [] [3])
  have r0 := holds_refl [5, -7, -5, 4, 7]
  have r1 := holds_trans r0 (holds_context rc22_rule1858 [5] [7])
  have r2 := holds_trans r1 (holds_context rc22_rule8 [] [-7, 6, 7])
  have r3 := holds_trans r2 (holds_context rc22_rule1794 [] [])
  have r4 := holds_trans r3 (holds_context rc22_rule2322 [] [])
  exact holds_factor (holds_trans (holds_symm l7) (holds_trans h0 r4)) (by central_nf)

theorem rc22_rule5169 : Holds ((normalizedRelatorError .i_r8) ^ (-51 : ℤ) * (normalizedRelatorError .i_s1) ^ (-7 : ℤ) * (normalizedRelatorError .i_s2) ^ (-43 : ℤ) * (normalizedRelatorError .i_s4) ^ (-5 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-42 : ℤ) * (normalizedRelatorError .i_s5) ^ (18 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-125 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (36 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (102 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-23 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (2 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (2 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (15 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-26 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (20 : ℤ) * (normalizedRelatorError .viii_s2) ^ (8 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-16 : ℤ) * (normalizedRelatorError .viii_s7) ^ (7 : ℤ) * (normalizedRelatorError .viii_s3) ^ (46 : ℤ) * (normalizedRelatorError .viii_r3) ^ (7 : ℤ)) [3, 4, 9, 3] [9, 5, 6, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule5168 [9] [])) (holds_context rc22_rule16 [] [3, 4, 9, 3]))
  have l0 := holds_refl [9, 5, 6, -5]
  have r0 := holds_refl [3, 4, 9, 3]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule5705 : Holds ((normalizedRelatorError .i_s1) ^ (-4 : ℤ) * (normalizedRelatorError .i_s2) ^ (-8 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (6 : ℤ) * (normalizedRelatorError .i_s3) ^ (-8 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (9 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-1 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-11 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (11 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (7 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (10 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-7 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (3 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_r3) ^ (6 : ℤ)) [3, 2, 3, 2] [-9, -5, 7, -9] := by
  have h0 := rc22_rule2968
  have l0 := holds_refl [5, 4, -9, -5, -9]
  have l1 := holds_trans l0 (holds_context rc22_rule3326 [] [-9])
  have r0 := holds_refl [3, 2, 3, 2]
  exact holds_factor (holds_symm (holds_trans (holds_symm l1) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule6001 : Holds ((normalizedRelatorError .i_r8) ^ (-9 : ℤ) * (normalizedRelatorError .i_s2) ^ (10 : ℤ) * (normalizedRelatorError .i_s4) ^ (-15 : ℤ) * (normalizedRelatorError .i_s6) ^ (-18 : ℤ) * (normalizedRelatorError .i_s3) ^ (6 : ℤ) * (normalizedRelatorError .i_s5) ^ (-10 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-50 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (2 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (28 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (20 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-34 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-17 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-34 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (17 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-15 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-12 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (5 : ℤ) * (normalizedRelatorError .viii_s2) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (11 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-4 : ℤ) * (normalizedRelatorError .viii_s7) ^ (10 : ℤ) * (normalizedRelatorError .viii_s3) ^ (28 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-34 : ℤ)) [4, -9, 4, 7] [-9, 7, 6] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3161 [4] [])) (holds_context rc22_rule30 [] [-9, 6, -7]))
  have l0 := holds_refl [4, -9, 4, 7]
  have r0 := holds_refl [3, 4, -9, 6, -7]
  have r1 := holds_trans r0 (holds_context rc22_rule3757 [] [-7])
  have r2 := holds_trans r1 (holds_context rc22_rule33 [6, -9] [])
  have r3 := holds_trans r2 (holds_context rc22_rule3752 [] [])
  exact holds_factor (holds_trans (holds_symm l0) (holds_trans h0 r3)) (by central_nf)

theorem rc22_rule6062 : Holds ((normalizedRelatorError .i_r8) ^ (-5 : ℤ) * normalizedRelatorError .i_s1 * (normalizedRelatorError .i_s2) ^ (-8 : ℤ) * (normalizedRelatorError .i_s4) ^ (4 : ℤ) * (normalizedRelatorError .i_s6) ^ (5 : ℤ) * (normalizedRelatorError .i_s3) ^ (-6 : ℤ) * (normalizedRelatorError .i_s5) ^ (7 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (4 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-7 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (8 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (6 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (8 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (-3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (5 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (2 : ℤ) * (normalizedRelatorError .viii_s2) ^ (2 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-5 : ℤ) * (normalizedRelatorError .viii_s7) ^ (-2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (14 : ℤ)) [9, 9, 5, 6, -5] [-9, 4, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3186 [-9] [])) (holds_context rc22_rule29 [] [5, 6, -5]))
  have l0 := holds_refl [-9, 4, -9, 4]
  have r0 := holds_refl [9, 9, 5, 6, -5]
  exact holds_factor (holds_symm (holds_trans (holds_symm l0) (holds_trans h0 r0))) (by central_nf)

theorem rc22_rule6131 : Holds ((normalizedRelatorError .i_r8) ^ (4 : ℤ) * (normalizedRelatorError .i_s2) ^ (9 : ℤ) * (normalizedRelatorError .i_s4) ^ (-4 : ℤ) * (normalizedRelatorError .i_s6) ^ (-6 : ℤ) * (normalizedRelatorError .i_s3) ^ (6 : ℤ) * (normalizedRelatorError .i_s5) ^ (-6 : ℤ) * (normalizedRelatorError .ii_s1_s2) ^ (-1 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (-7 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (-6 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (5 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (-10 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (-3 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (-10 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (-4 : ℤ) * normalizedRelatorError .v_s3_s5 * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .viii_s2) ^ (-3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (4 : ℤ) * (normalizedRelatorError .viii_s7) ^ (2 : ℤ) * (normalizedRelatorError .viii_s3) ^ (4 : ℤ) * (normalizedRelatorError .viii_r3) ^ (-11 : ℤ)) [-5, 7, -9, 8] [-9, 7, -5] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3211 [] [7])) (holds_context rc22_rule1862 [-9, -5] []))
  have l0 := holds_refl [4, -9, -5, 7]
  have l1 := holds_trans l0 (holds_context rc22_rule2970 [] [])
  have r0 := holds_refl [-9, -5, 5, 7, -5]
  have r1 := holds_trans r0 (holds_context rc22_rule9 [-9] [7, -5])
  exact holds_factor (holds_trans (holds_symm l1) (holds_trans h0 r1)) (by central_nf)

theorem rc22_rule6214 : Holds ((normalizedRelatorError .i_r8) ^ (-70 : ℤ) * (normalizedRelatorError .i_s1) ^ (-6 : ℤ) * (normalizedRelatorError .i_s2) ^ (-65 : ℤ) * (normalizedRelatorError .i_s4) ^ (2 : ℤ) * (normalizedRelatorError .i_s6) ^ (17 : ℤ) * (normalizedRelatorError .i_s3) ^ (-61 : ℤ) * (normalizedRelatorError .i_s5) ^ (37 : ℤ) * normalizedRelatorError .i_s7 * (normalizedRelatorError .ii_s1_s2) ^ (-123 : ℤ) * (normalizedRelatorError .ii_s1_s3) ^ (50 : ℤ) * (normalizedRelatorError .ii_s1_s5) ^ (122 : ℤ) * (normalizedRelatorError .iii_s1_s6) ^ (-40 : ℤ) * (normalizedRelatorError .iv_s2_s4) ^ (17 : ℤ) * (normalizedRelatorError .iv_s2_s6) ^ (17 : ℤ) * (normalizedRelatorError .iv_s2_s8) ^ (20 : ℤ) * (normalizedRelatorError .iv_s7_s2) ^ (8 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (11 : ℤ) * (normalizedRelatorError .v_s3_s5) ^ (-24 : ℤ) * (normalizedRelatorError .v_s5_s4) ^ (22 : ℤ) * (normalizedRelatorError .viii_s2) ^ (14 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-14 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-18 : ℤ) * (normalizedRelatorError .viii_s7) ^ (3 : ℤ) * (normalizedRelatorError .viii_s3) ^ (42 : ℤ) * (normalizedRelatorError .viii_r3) ^ (43 : ℤ)) [4, 9, 4, 9] [-9, 4, -9, 4] := by
  have h0 := (holds_trans (holds_symm (holds_context rc22_rule3235 [9, 4] [])) (holds_context rc22_rule3195 [] [9, 9]))
  have l0 := holds_refl [9, 4, 3, 9, 3]
  have l1 := holds_trans l0 (holds_context rc22_rule30 [9] [9, 3])
  have l2 := holds_trans l1 (holds_context rc22_rule5169 [9] [])
  have l3 := holds_trans l2 (holds_context rc22_rule6062 [] [])
  have r0 := holds_refl [5, 6, -5, 9, 9]
  have r1 := holds_trans r0 (holds_context rc22_rule3287 [] [9])
  exact holds_factor (holds_symm (holds_trans (holds_symm l3) (holds_trans h0 r1))) (by central_nf)

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
