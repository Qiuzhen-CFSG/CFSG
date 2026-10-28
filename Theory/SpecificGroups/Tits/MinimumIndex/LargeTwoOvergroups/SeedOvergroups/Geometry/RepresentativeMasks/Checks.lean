module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks.Evaluation
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Reduction
import Mathlib.Tactic.FinCases

/-!
# The representative membership-mask certificates

Every support bit used by the seventeen requested patterns is checked against
the actual representative action. The common point actions are certified in
PointCertificates and identified with Evaluation's original tests. We check
64 rows at a time and combine the checks without re-evaluating them. Checks
are sequential to bound memory. No leaf-support implication is rechecked.
Source: Parrott (1972), p.683, and Geometry/source/emit_data.py.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks
set_option Elab.async false

set_option maxRecDepth 10000 in
private theorem batch_0_0 :
    (((rows 0).drop (64 * 0)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_1 :
    (((rows 0).drop (64 * 1)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_2 :
    (((rows 0).drop (64 * 2)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_3 :
    (((rows 0).drop (64 * 3)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_4 :
    (((rows 0).drop (64 * 4)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_5 :
    (((rows 0).drop (64 * 5)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_6 :
    (((rows 0).drop (64 * 6)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_7 :
    (((rows 0).drop (64 * 7)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_8 :
    (((rows 0).drop (64 * 8)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_9 :
    (((rows 0).drop (64 * 9)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_10 :
    (((rows 0).drop (64 * 10)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_11 :
    (((rows 0).drop (64 * 11)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_12 :
    (((rows 0).drop (64 * 12)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_13 :
    (((rows 0).drop (64 * 13)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_14 :
    (((rows 0).drop (64 * 14)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_15 :
    (((rows 0).drop (64 * 15)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_16 :
    (((rows 0).drop (64 * 16)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_17 :
    (((rows 0).drop (64 * 17)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_18 :
    (((rows 0).drop (64 * 18)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_0_19 :
    (((rows 0).drop (64 * 19)).take 64).all (check 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_0 : (rows 0).all (check 0) = true := by
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_0_0
  · exact batch_0_1
  · exact batch_0_2
  · exact batch_0_3
  · exact batch_0_4
  · exact batch_0_5
  · exact batch_0_6
  · exact batch_0_7
  · exact batch_0_8
  · exact batch_0_9
  · exact batch_0_10
  · exact batch_0_11
  · exact batch_0_12
  · exact batch_0_13
  · exact batch_0_14
  · exact batch_0_15
  · exact batch_0_16
  · exact batch_0_17
  · exact batch_0_18
  · exact batch_0_19

set_option maxRecDepth 10000 in
private theorem batch_1_0 :
    (((rows 1).drop (64 * 0)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_1 :
    (((rows 1).drop (64 * 1)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_2 :
    (((rows 1).drop (64 * 2)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_3 :
    (((rows 1).drop (64 * 3)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_4 :
    (((rows 1).drop (64 * 4)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_5 :
    (((rows 1).drop (64 * 5)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_6 :
    (((rows 1).drop (64 * 6)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_7 :
    (((rows 1).drop (64 * 7)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_8 :
    (((rows 1).drop (64 * 8)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_9 :
    (((rows 1).drop (64 * 9)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_10 :
    (((rows 1).drop (64 * 10)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_11 :
    (((rows 1).drop (64 * 11)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_12 :
    (((rows 1).drop (64 * 12)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_13 :
    (((rows 1).drop (64 * 13)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_14 :
    (((rows 1).drop (64 * 14)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_1_15 :
    (((rows 1).drop (64 * 15)).take 64).all (check 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_1 : (rows 1).all (check 1) = true := by
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_1_0
  · exact batch_1_1
  · exact batch_1_2
  · exact batch_1_3
  · exact batch_1_4
  · exact batch_1_5
  · exact batch_1_6
  · exact batch_1_7
  · exact batch_1_8
  · exact batch_1_9
  · exact batch_1_10
  · exact batch_1_11
  · exact batch_1_12
  · exact batch_1_13
  · exact batch_1_14
  · exact batch_1_15

set_option maxRecDepth 10000 in
private theorem batch_2_0 :
    (((rows 2).drop (64 * 0)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_1 :
    (((rows 2).drop (64 * 1)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_2 :
    (((rows 2).drop (64 * 2)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_3 :
    (((rows 2).drop (64 * 3)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_4 :
    (((rows 2).drop (64 * 4)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_5 :
    (((rows 2).drop (64 * 5)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_6 :
    (((rows 2).drop (64 * 6)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_7 :
    (((rows 2).drop (64 * 7)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_8 :
    (((rows 2).drop (64 * 8)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_9 :
    (((rows 2).drop (64 * 9)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_10 :
    (((rows 2).drop (64 * 10)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_2_11 :
    (((rows 2).drop (64 * 11)).take 64).all (check 2) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_2 : (rows 2).all (check 2) = true := by
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_2_0
  · exact batch_2_1
  · exact batch_2_2
  · exact batch_2_3
  · exact batch_2_4
  · exact batch_2_5
  · exact batch_2_6
  · exact batch_2_7
  · exact batch_2_8
  · exact batch_2_9
  · exact batch_2_10
  · exact batch_2_11

set_option maxRecDepth 10000 in
private theorem batch_3_0 :
    (((rows 3).drop (64 * 0)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_1 :
    (((rows 3).drop (64 * 1)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_2 :
    (((rows 3).drop (64 * 2)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_3 :
    (((rows 3).drop (64 * 3)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_4 :
    (((rows 3).drop (64 * 4)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_5 :
    (((rows 3).drop (64 * 5)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_6 :
    (((rows 3).drop (64 * 6)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_7 :
    (((rows 3).drop (64 * 7)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_8 :
    (((rows 3).drop (64 * 8)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_9 :
    (((rows 3).drop (64 * 9)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_10 :
    (((rows 3).drop (64 * 10)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_11 :
    (((rows 3).drop (64 * 11)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_12 :
    (((rows 3).drop (64 * 12)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_13 :
    (((rows 3).drop (64 * 13)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_14 :
    (((rows 3).drop (64 * 14)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_15 :
    (((rows 3).drop (64 * 15)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_16 :
    (((rows 3).drop (64 * 16)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_17 :
    (((rows 3).drop (64 * 17)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_18 :
    (((rows 3).drop (64 * 18)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_3_19 :
    (((rows 3).drop (64 * 19)).take 64).all (check 3) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_3 : (rows 3).all (check 3) = true := by
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_3_0
  · exact batch_3_1
  · exact batch_3_2
  · exact batch_3_3
  · exact batch_3_4
  · exact batch_3_5
  · exact batch_3_6
  · exact batch_3_7
  · exact batch_3_8
  · exact batch_3_9
  · exact batch_3_10
  · exact batch_3_11
  · exact batch_3_12
  · exact batch_3_13
  · exact batch_3_14
  · exact batch_3_15
  · exact batch_3_16
  · exact batch_3_17
  · exact batch_3_18
  · exact batch_3_19

set_option maxRecDepth 10000 in
private theorem batch_4_0 :
    (((rows 4).drop (64 * 0)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_4_1 :
    (((rows 4).drop (64 * 1)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_4_2 :
    (((rows 4).drop (64 * 2)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_4_3 :
    (((rows 4).drop (64 * 3)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_4_4 :
    (((rows 4).drop (64 * 4)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_4_5 :
    (((rows 4).drop (64 * 5)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_4_6 :
    (((rows 4).drop (64 * 6)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_4_7 :
    (((rows 4).drop (64 * 7)).take 64).all (check 4) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_4 : (rows 4).all (check 4) = true := by
  refine all_of_chunk_checks _ 64 8 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_4_0
  · exact batch_4_1
  · exact batch_4_2
  · exact batch_4_3
  · exact batch_4_4
  · exact batch_4_5
  · exact batch_4_6
  · exact batch_4_7

set_option maxRecDepth 10000 in
private theorem batch_5_0 :
    (((rows 5).drop (64 * 0)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_1 :
    (((rows 5).drop (64 * 1)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_2 :
    (((rows 5).drop (64 * 2)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_3 :
    (((rows 5).drop (64 * 3)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_4 :
    (((rows 5).drop (64 * 4)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_5 :
    (((rows 5).drop (64 * 5)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_6 :
    (((rows 5).drop (64 * 6)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_7 :
    (((rows 5).drop (64 * 7)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_8 :
    (((rows 5).drop (64 * 8)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_9 :
    (((rows 5).drop (64 * 9)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_10 :
    (((rows 5).drop (64 * 10)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_11 :
    (((rows 5).drop (64 * 11)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_12 :
    (((rows 5).drop (64 * 12)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_13 :
    (((rows 5).drop (64 * 13)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_14 :
    (((rows 5).drop (64 * 14)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_15 :
    (((rows 5).drop (64 * 15)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_16 :
    (((rows 5).drop (64 * 16)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_17 :
    (((rows 5).drop (64 * 17)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_18 :
    (((rows 5).drop (64 * 18)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_5_19 :
    (((rows 5).drop (64 * 19)).take 64).all (check 5) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_5 : (rows 5).all (check 5) = true := by
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_5_0
  · exact batch_5_1
  · exact batch_5_2
  · exact batch_5_3
  · exact batch_5_4
  · exact batch_5_5
  · exact batch_5_6
  · exact batch_5_7
  · exact batch_5_8
  · exact batch_5_9
  · exact batch_5_10
  · exact batch_5_11
  · exact batch_5_12
  · exact batch_5_13
  · exact batch_5_14
  · exact batch_5_15
  · exact batch_5_16
  · exact batch_5_17
  · exact batch_5_18
  · exact batch_5_19

set_option maxRecDepth 10000 in
private theorem batch_6_0 :
    (((rows 6).drop (64 * 0)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_1 :
    (((rows 6).drop (64 * 1)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_2 :
    (((rows 6).drop (64 * 2)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_3 :
    (((rows 6).drop (64 * 3)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_4 :
    (((rows 6).drop (64 * 4)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_5 :
    (((rows 6).drop (64 * 5)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_6 :
    (((rows 6).drop (64 * 6)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_7 :
    (((rows 6).drop (64 * 7)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_8 :
    (((rows 6).drop (64 * 8)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_9 :
    (((rows 6).drop (64 * 9)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_10 :
    (((rows 6).drop (64 * 10)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_6_11 :
    (((rows 6).drop (64 * 11)).take 64).all (check 6) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_6 : (rows 6).all (check 6) = true := by
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_6_0
  · exact batch_6_1
  · exact batch_6_2
  · exact batch_6_3
  · exact batch_6_4
  · exact batch_6_5
  · exact batch_6_6
  · exact batch_6_7
  · exact batch_6_8
  · exact batch_6_9
  · exact batch_6_10
  · exact batch_6_11

set_option maxRecDepth 10000 in
private theorem batch_7_0 :
    (((rows 7).drop (64 * 0)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_1 :
    (((rows 7).drop (64 * 1)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_2 :
    (((rows 7).drop (64 * 2)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_3 :
    (((rows 7).drop (64 * 3)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_4 :
    (((rows 7).drop (64 * 4)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_5 :
    (((rows 7).drop (64 * 5)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_6 :
    (((rows 7).drop (64 * 6)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_7 :
    (((rows 7).drop (64 * 7)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_8 :
    (((rows 7).drop (64 * 8)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_9 :
    (((rows 7).drop (64 * 9)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_10 :
    (((rows 7).drop (64 * 10)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_7_11 :
    (((rows 7).drop (64 * 11)).take 64).all (check 7) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_7 : (rows 7).all (check 7) = true := by
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_7_0
  · exact batch_7_1
  · exact batch_7_2
  · exact batch_7_3
  · exact batch_7_4
  · exact batch_7_5
  · exact batch_7_6
  · exact batch_7_7
  · exact batch_7_8
  · exact batch_7_9
  · exact batch_7_10
  · exact batch_7_11

set_option maxRecDepth 10000 in
private theorem batch_8_0 :
    (((rows 8).drop (64 * 0)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_8_1 :
    (((rows 8).drop (64 * 1)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_8_2 :
    (((rows 8).drop (64 * 2)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_8_3 :
    (((rows 8).drop (64 * 3)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_8_4 :
    (((rows 8).drop (64 * 4)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_8_5 :
    (((rows 8).drop (64 * 5)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_8_6 :
    (((rows 8).drop (64 * 6)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_8_7 :
    (((rows 8).drop (64 * 7)).take 64).all (check 8) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_8 : (rows 8).all (check 8) = true := by
  refine all_of_chunk_checks _ 64 8 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_8_0
  · exact batch_8_1
  · exact batch_8_2
  · exact batch_8_3
  · exact batch_8_4
  · exact batch_8_5
  · exact batch_8_6
  · exact batch_8_7

set_option maxRecDepth 10000 in
private theorem batch_10_0 :
    (((rows 10).drop (64 * 0)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_1 :
    (((rows 10).drop (64 * 1)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_2 :
    (((rows 10).drop (64 * 2)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_3 :
    (((rows 10).drop (64 * 3)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_4 :
    (((rows 10).drop (64 * 4)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_5 :
    (((rows 10).drop (64 * 5)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_6 :
    (((rows 10).drop (64 * 6)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_7 :
    (((rows 10).drop (64 * 7)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_8 :
    (((rows 10).drop (64 * 8)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_9 :
    (((rows 10).drop (64 * 9)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_10 :
    (((rows 10).drop (64 * 10)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_11 :
    (((rows 10).drop (64 * 11)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_12 :
    (((rows 10).drop (64 * 12)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_13 :
    (((rows 10).drop (64 * 13)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_14 :
    (((rows 10).drop (64 * 14)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_15 :
    (((rows 10).drop (64 * 15)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_16 :
    (((rows 10).drop (64 * 16)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_17 :
    (((rows 10).drop (64 * 17)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_18 :
    (((rows 10).drop (64 * 18)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_10_19 :
    (((rows 10).drop (64 * 19)).take 64).all (check 10) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_10 : (rows 10).all (check 10) = true := by
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_10_0
  · exact batch_10_1
  · exact batch_10_2
  · exact batch_10_3
  · exact batch_10_4
  · exact batch_10_5
  · exact batch_10_6
  · exact batch_10_7
  · exact batch_10_8
  · exact batch_10_9
  · exact batch_10_10
  · exact batch_10_11
  · exact batch_10_12
  · exact batch_10_13
  · exact batch_10_14
  · exact batch_10_15
  · exact batch_10_16
  · exact batch_10_17
  · exact batch_10_18
  · exact batch_10_19

set_option maxRecDepth 10000 in
private theorem batch_11_0 :
    (((rows 11).drop (64 * 0)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_1 :
    (((rows 11).drop (64 * 1)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_2 :
    (((rows 11).drop (64 * 2)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_3 :
    (((rows 11).drop (64 * 3)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_4 :
    (((rows 11).drop (64 * 4)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_5 :
    (((rows 11).drop (64 * 5)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_6 :
    (((rows 11).drop (64 * 6)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_7 :
    (((rows 11).drop (64 * 7)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_8 :
    (((rows 11).drop (64 * 8)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_9 :
    (((rows 11).drop (64 * 9)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_10 :
    (((rows 11).drop (64 * 10)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_11_11 :
    (((rows 11).drop (64 * 11)).take 64).all (check 11) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_11 : (rows 11).all (check 11) = true := by
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_11_0
  · exact batch_11_1
  · exact batch_11_2
  · exact batch_11_3
  · exact batch_11_4
  · exact batch_11_5
  · exact batch_11_6
  · exact batch_11_7
  · exact batch_11_8
  · exact batch_11_9
  · exact batch_11_10
  · exact batch_11_11

set_option maxRecDepth 10000 in
private theorem batch_12_0 :
    (((rows 12).drop (64 * 0)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_1 :
    (((rows 12).drop (64 * 1)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_2 :
    (((rows 12).drop (64 * 2)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_3 :
    (((rows 12).drop (64 * 3)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_4 :
    (((rows 12).drop (64 * 4)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_5 :
    (((rows 12).drop (64 * 5)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_6 :
    (((rows 12).drop (64 * 6)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_7 :
    (((rows 12).drop (64 * 7)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_8 :
    (((rows 12).drop (64 * 8)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_9 :
    (((rows 12).drop (64 * 9)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_10 :
    (((rows 12).drop (64 * 10)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_11 :
    (((rows 12).drop (64 * 11)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_12 :
    (((rows 12).drop (64 * 12)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_13 :
    (((rows 12).drop (64 * 13)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_14 :
    (((rows 12).drop (64 * 14)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_12_15 :
    (((rows 12).drop (64 * 15)).take 64).all (check 12) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_12 : (rows 12).all (check 12) = true := by
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_12_0
  · exact batch_12_1
  · exact batch_12_2
  · exact batch_12_3
  · exact batch_12_4
  · exact batch_12_5
  · exact batch_12_6
  · exact batch_12_7
  · exact batch_12_8
  · exact batch_12_9
  · exact batch_12_10
  · exact batch_12_11
  · exact batch_12_12
  · exact batch_12_13
  · exact batch_12_14
  · exact batch_12_15

set_option maxRecDepth 10000 in
private theorem batch_13_0 :
    (((rows 13).drop (64 * 0)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_1 :
    (((rows 13).drop (64 * 1)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_2 :
    (((rows 13).drop (64 * 2)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_3 :
    (((rows 13).drop (64 * 3)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_4 :
    (((rows 13).drop (64 * 4)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_5 :
    (((rows 13).drop (64 * 5)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_6 :
    (((rows 13).drop (64 * 6)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_7 :
    (((rows 13).drop (64 * 7)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_8 :
    (((rows 13).drop (64 * 8)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_9 :
    (((rows 13).drop (64 * 9)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_10 :
    (((rows 13).drop (64 * 10)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_11 :
    (((rows 13).drop (64 * 11)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_12 :
    (((rows 13).drop (64 * 12)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_13 :
    (((rows 13).drop (64 * 13)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_14 :
    (((rows 13).drop (64 * 14)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_15 :
    (((rows 13).drop (64 * 15)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_16 :
    (((rows 13).drop (64 * 16)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_17 :
    (((rows 13).drop (64 * 17)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_18 :
    (((rows 13).drop (64 * 18)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_13_19 :
    (((rows 13).drop (64 * 19)).take 64).all (check 13) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_13 : (rows 13).all (check 13) = true := by
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_13_0
  · exact batch_13_1
  · exact batch_13_2
  · exact batch_13_3
  · exact batch_13_4
  · exact batch_13_5
  · exact batch_13_6
  · exact batch_13_7
  · exact batch_13_8
  · exact batch_13_9
  · exact batch_13_10
  · exact batch_13_11
  · exact batch_13_12
  · exact batch_13_13
  · exact batch_13_14
  · exact batch_13_15
  · exact batch_13_16
  · exact batch_13_17
  · exact batch_13_18
  · exact batch_13_19

set_option maxRecDepth 10000 in
private theorem batch_14_0 :
    (((rows 14).drop (64 * 0)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_1 :
    (((rows 14).drop (64 * 1)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_2 :
    (((rows 14).drop (64 * 2)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_3 :
    (((rows 14).drop (64 * 3)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_4 :
    (((rows 14).drop (64 * 4)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_5 :
    (((rows 14).drop (64 * 5)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_6 :
    (((rows 14).drop (64 * 6)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_7 :
    (((rows 14).drop (64 * 7)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_8 :
    (((rows 14).drop (64 * 8)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_9 :
    (((rows 14).drop (64 * 9)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_10 :
    (((rows 14).drop (64 * 10)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_11 :
    (((rows 14).drop (64 * 11)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_12 :
    (((rows 14).drop (64 * 12)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_13 :
    (((rows 14).drop (64 * 13)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_14 :
    (((rows 14).drop (64 * 14)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_15 :
    (((rows 14).drop (64 * 15)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_16 :
    (((rows 14).drop (64 * 16)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_17 :
    (((rows 14).drop (64 * 17)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_18 :
    (((rows 14).drop (64 * 18)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_14_19 :
    (((rows 14).drop (64 * 19)).take 64).all (check 14) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_14 : (rows 14).all (check 14) = true := by
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_14_0
  · exact batch_14_1
  · exact batch_14_2
  · exact batch_14_3
  · exact batch_14_4
  · exact batch_14_5
  · exact batch_14_6
  · exact batch_14_7
  · exact batch_14_8
  · exact batch_14_9
  · exact batch_14_10
  · exact batch_14_11
  · exact batch_14_12
  · exact batch_14_13
  · exact batch_14_14
  · exact batch_14_15
  · exact batch_14_16
  · exact batch_14_17
  · exact batch_14_18
  · exact batch_14_19

set_option maxRecDepth 10000 in
private theorem batch_15_0 :
    (((rows 15).drop (64 * 0)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_1 :
    (((rows 15).drop (64 * 1)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_2 :
    (((rows 15).drop (64 * 2)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_3 :
    (((rows 15).drop (64 * 3)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_4 :
    (((rows 15).drop (64 * 4)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_5 :
    (((rows 15).drop (64 * 5)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_6 :
    (((rows 15).drop (64 * 6)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_7 :
    (((rows 15).drop (64 * 7)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_8 :
    (((rows 15).drop (64 * 8)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_9 :
    (((rows 15).drop (64 * 9)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_10 :
    (((rows 15).drop (64 * 10)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_11 :
    (((rows 15).drop (64 * 11)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_12 :
    (((rows 15).drop (64 * 12)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_13 :
    (((rows 15).drop (64 * 13)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_14 :
    (((rows 15).drop (64 * 14)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_15_15 :
    (((rows 15).drop (64 * 15)).take 64).all (check 15) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_15 : (rows 15).all (check 15) = true := by
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_15_0
  · exact batch_15_1
  · exact batch_15_2
  · exact batch_15_3
  · exact batch_15_4
  · exact batch_15_5
  · exact batch_15_6
  · exact batch_15_7
  · exact batch_15_8
  · exact batch_15_9
  · exact batch_15_10
  · exact batch_15_11
  · exact batch_15_12
  · exact batch_15_13
  · exact batch_15_14
  · exact batch_15_15

set_option maxRecDepth 10000 in
private theorem batch_16_0 :
    (((rows 16).drop (64 * 0)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_1 :
    (((rows 16).drop (64 * 1)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_2 :
    (((rows 16).drop (64 * 2)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_3 :
    (((rows 16).drop (64 * 3)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_4 :
    (((rows 16).drop (64 * 4)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_5 :
    (((rows 16).drop (64 * 5)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_6 :
    (((rows 16).drop (64 * 6)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_7 :
    (((rows 16).drop (64 * 7)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_8 :
    (((rows 16).drop (64 * 8)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_9 :
    (((rows 16).drop (64 * 9)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_10 :
    (((rows 16).drop (64 * 10)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_11 :
    (((rows 16).drop (64 * 11)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_12 :
    (((rows 16).drop (64 * 12)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_13 :
    (((rows 16).drop (64 * 13)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_14 :
    (((rows 16).drop (64 * 14)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_15 :
    (((rows 16).drop (64 * 15)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_16 :
    (((rows 16).drop (64 * 16)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_17 :
    (((rows 16).drop (64 * 17)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_18 :
    (((rows 16).drop (64 * 18)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_16_19 :
    (((rows 16).drop (64 * 19)).take 64).all (check 16) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_16 : (rows 16).all (check 16) = true := by
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_16_0
  · exact batch_16_1
  · exact batch_16_2
  · exact batch_16_3
  · exact batch_16_4
  · exact batch_16_5
  · exact batch_16_6
  · exact batch_16_7
  · exact batch_16_8
  · exact batch_16_9
  · exact batch_16_10
  · exact batch_16_11
  · exact batch_16_12
  · exact batch_16_13
  · exact batch_16_14
  · exact batch_16_15
  · exact batch_16_16
  · exact batch_16_17
  · exact batch_16_18
  · exact batch_16_19

set_option maxRecDepth 10000 in
private theorem batch_17_0 :
    (((rows 17).drop (64 * 0)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_1 :
    (((rows 17).drop (64 * 1)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_2 :
    (((rows 17).drop (64 * 2)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_3 :
    (((rows 17).drop (64 * 3)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_4 :
    (((rows 17).drop (64 * 4)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_5 :
    (((rows 17).drop (64 * 5)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_6 :
    (((rows 17).drop (64 * 6)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_7 :
    (((rows 17).drop (64 * 7)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_8 :
    (((rows 17).drop (64 * 8)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_9 :
    (((rows 17).drop (64 * 9)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_10 :
    (((rows 17).drop (64 * 10)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_11 :
    (((rows 17).drop (64 * 11)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_12 :
    (((rows 17).drop (64 * 12)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_13 :
    (((rows 17).drop (64 * 13)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_14 :
    (((rows 17).drop (64 * 14)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem batch_17_15 :
    (((rows 17).drop (64 * 15)).take 64).all (check 17) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_17 : (rows 17).all (check 17) = true := by
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact batch_17_0
  · exact batch_17_1
  · exact batch_17_2
  · exact batch_17_3
  · exact batch_17_4
  · exact batch_17_5
  · exact batch_17_6
  · exact batch_17_7
  · exact batch_17_8
  · exact batch_17_9
  · exact batch_17_10
  · exact batch_17_11
  · exact batch_17_12
  · exact batch_17_13
  · exact batch_17_14
  · exact batch_17_15

/-- Every requested candidate mask agrees with the certified point test. -/
public theorem checked (t : Fin 18) (ht : t ≠ 9) : (rows t).all (check t) = true := by
  fin_cases t
  · exact checked_0
  · exact checked_1
  · exact checked_2
  · exact checked_3
  · exact checked_4
  · exact checked_5
  · exact checked_6
  · exact checked_7
  · exact checked_8
  · exact (ht rfl).elim
  · exact checked_10
  · exact checked_11
  · exact checked_12
  · exact checked_13
  · exact checked_14
  · exact checked_15
  · exact checked_16
  · exact checked_17

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks
