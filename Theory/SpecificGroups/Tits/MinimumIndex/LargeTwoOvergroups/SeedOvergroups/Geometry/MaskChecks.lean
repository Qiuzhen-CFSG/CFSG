module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Reduction
import Mathlib.Tactic.FinCases

/-!
# Leaf elimination checks for the eighteen candidate support tables

The kernel checks every candidate support against every designated leaf
parent. These are assertions about the finite tables; correctness of the
tables as actual subgroup memberships remains a separate certificate.

Checks run in batches of 64 rows. The generic chunk-combination theorem
avoids reducing one large certificate. Declaration checks are sequential
to avoid multiplying their peak memory by the number of declarations.
Source: the literal Parrott place data in SeedOvergroups/source/places.json.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
set_option Elab.async false

set_option maxRecDepth 10000 in
private theorem mask_0_0 :
    (((rows 0).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_1 :
    (((rows 0).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_2 :
    (((rows 0).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_3 :
    (((rows 0).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_4 :
    (((rows 0).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_5 :
    (((rows 0).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_6 :
    (((rows 0).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_7 :
    (((rows 0).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_8 :
    (((rows 0).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_9 :
    (((rows 0).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_10 :
    (((rows 0).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_11 :
    (((rows 0).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_12 :
    (((rows 0).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_13 :
    (((rows 0).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_14 :
    (((rows 0).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_15 :
    (((rows 0).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_16 :
    (((rows 0).drop (64 * 16)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_17 :
    (((rows 0).drop (64 * 17)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_18 :
    (((rows 0).drop (64 * 18)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_0_19 :
    (((rows 0).drop (64 * 19)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 0) (parents 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_0 :
    leafCheck rowMember (rows 0) (placePattern 0) (parents 0) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_0_0
  · exact mask_0_1
  · exact mask_0_2
  · exact mask_0_3
  · exact mask_0_4
  · exact mask_0_5
  · exact mask_0_6
  · exact mask_0_7
  · exact mask_0_8
  · exact mask_0_9
  · exact mask_0_10
  · exact mask_0_11
  · exact mask_0_12
  · exact mask_0_13
  · exact mask_0_14
  · exact mask_0_15
  · exact mask_0_16
  · exact mask_0_17
  · exact mask_0_18
  · exact mask_0_19

set_option maxRecDepth 10000 in
private theorem mask_1_0 :
    (((rows 1).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_1 :
    (((rows 1).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_2 :
    (((rows 1).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_3 :
    (((rows 1).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_4 :
    (((rows 1).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_5 :
    (((rows 1).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_6 :
    (((rows 1).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_7 :
    (((rows 1).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_8 :
    (((rows 1).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_9 :
    (((rows 1).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_10 :
    (((rows 1).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_11 :
    (((rows 1).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_12 :
    (((rows 1).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_13 :
    (((rows 1).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_14 :
    (((rows 1).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_1_15 :
    (((rows 1).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 1) (parents 1)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_1 :
    leafCheck rowMember (rows 1) (placePattern 1) (parents 1) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_1_0
  · exact mask_1_1
  · exact mask_1_2
  · exact mask_1_3
  · exact mask_1_4
  · exact mask_1_5
  · exact mask_1_6
  · exact mask_1_7
  · exact mask_1_8
  · exact mask_1_9
  · exact mask_1_10
  · exact mask_1_11
  · exact mask_1_12
  · exact mask_1_13
  · exact mask_1_14
  · exact mask_1_15

set_option maxRecDepth 10000 in
private theorem mask_2_0 :
    (((rows 2).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_1 :
    (((rows 2).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_2 :
    (((rows 2).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_3 :
    (((rows 2).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_4 :
    (((rows 2).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_5 :
    (((rows 2).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_6 :
    (((rows 2).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_7 :
    (((rows 2).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_8 :
    (((rows 2).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_9 :
    (((rows 2).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_10 :
    (((rows 2).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_2_11 :
    (((rows 2).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 2) (parents 2)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_2 :
    leafCheck rowMember (rows 2) (placePattern 2) (parents 2) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_2_0
  · exact mask_2_1
  · exact mask_2_2
  · exact mask_2_3
  · exact mask_2_4
  · exact mask_2_5
  · exact mask_2_6
  · exact mask_2_7
  · exact mask_2_8
  · exact mask_2_9
  · exact mask_2_10
  · exact mask_2_11

set_option maxRecDepth 10000 in
private theorem mask_3_0 :
    (((rows 3).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_1 :
    (((rows 3).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_2 :
    (((rows 3).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_3 :
    (((rows 3).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_4 :
    (((rows 3).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_5 :
    (((rows 3).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_6 :
    (((rows 3).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_7 :
    (((rows 3).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_8 :
    (((rows 3).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_9 :
    (((rows 3).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_10 :
    (((rows 3).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_11 :
    (((rows 3).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_12 :
    (((rows 3).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_13 :
    (((rows 3).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_14 :
    (((rows 3).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_15 :
    (((rows 3).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_16 :
    (((rows 3).drop (64 * 16)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_17 :
    (((rows 3).drop (64 * 17)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_18 :
    (((rows 3).drop (64 * 18)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_3_19 :
    (((rows 3).drop (64 * 19)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 3) (parents 3)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_3 :
    leafCheck rowMember (rows 3) (placePattern 3) (parents 3) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_3_0
  · exact mask_3_1
  · exact mask_3_2
  · exact mask_3_3
  · exact mask_3_4
  · exact mask_3_5
  · exact mask_3_6
  · exact mask_3_7
  · exact mask_3_8
  · exact mask_3_9
  · exact mask_3_10
  · exact mask_3_11
  · exact mask_3_12
  · exact mask_3_13
  · exact mask_3_14
  · exact mask_3_15
  · exact mask_3_16
  · exact mask_3_17
  · exact mask_3_18
  · exact mask_3_19

set_option maxRecDepth 10000 in
private theorem mask_4_0 :
    (((rows 4).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_4_1 :
    (((rows 4).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_4_2 :
    (((rows 4).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_4_3 :
    (((rows 4).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_4_4 :
    (((rows 4).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_4_5 :
    (((rows 4).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_4_6 :
    (((rows 4).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_4_7 :
    (((rows 4).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 4) (parents 4)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_4 :
    leafCheck rowMember (rows 4) (placePattern 4) (parents 4) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 8 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_4_0
  · exact mask_4_1
  · exact mask_4_2
  · exact mask_4_3
  · exact mask_4_4
  · exact mask_4_5
  · exact mask_4_6
  · exact mask_4_7

set_option maxRecDepth 10000 in
private theorem mask_5_0 :
    (((rows 5).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_1 :
    (((rows 5).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_2 :
    (((rows 5).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_3 :
    (((rows 5).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_4 :
    (((rows 5).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_5 :
    (((rows 5).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_6 :
    (((rows 5).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_7 :
    (((rows 5).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_8 :
    (((rows 5).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_9 :
    (((rows 5).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_10 :
    (((rows 5).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_11 :
    (((rows 5).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_12 :
    (((rows 5).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_13 :
    (((rows 5).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_14 :
    (((rows 5).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_15 :
    (((rows 5).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_16 :
    (((rows 5).drop (64 * 16)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_17 :
    (((rows 5).drop (64 * 17)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_18 :
    (((rows 5).drop (64 * 18)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_5_19 :
    (((rows 5).drop (64 * 19)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 5) (parents 5)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_5 :
    leafCheck rowMember (rows 5) (placePattern 5) (parents 5) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_5_0
  · exact mask_5_1
  · exact mask_5_2
  · exact mask_5_3
  · exact mask_5_4
  · exact mask_5_5
  · exact mask_5_6
  · exact mask_5_7
  · exact mask_5_8
  · exact mask_5_9
  · exact mask_5_10
  · exact mask_5_11
  · exact mask_5_12
  · exact mask_5_13
  · exact mask_5_14
  · exact mask_5_15
  · exact mask_5_16
  · exact mask_5_17
  · exact mask_5_18
  · exact mask_5_19

set_option maxRecDepth 10000 in
private theorem mask_6_0 :
    (((rows 6).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_1 :
    (((rows 6).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_2 :
    (((rows 6).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_3 :
    (((rows 6).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_4 :
    (((rows 6).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_5 :
    (((rows 6).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_6 :
    (((rows 6).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_7 :
    (((rows 6).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_8 :
    (((rows 6).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_9 :
    (((rows 6).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_10 :
    (((rows 6).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_6_11 :
    (((rows 6).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 6) (parents 6)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_6 :
    leafCheck rowMember (rows 6) (placePattern 6) (parents 6) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_6_0
  · exact mask_6_1
  · exact mask_6_2
  · exact mask_6_3
  · exact mask_6_4
  · exact mask_6_5
  · exact mask_6_6
  · exact mask_6_7
  · exact mask_6_8
  · exact mask_6_9
  · exact mask_6_10
  · exact mask_6_11

set_option maxRecDepth 10000 in
private theorem mask_7_0 :
    (((rows 7).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_1 :
    (((rows 7).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_2 :
    (((rows 7).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_3 :
    (((rows 7).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_4 :
    (((rows 7).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_5 :
    (((rows 7).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_6 :
    (((rows 7).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_7 :
    (((rows 7).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_8 :
    (((rows 7).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_9 :
    (((rows 7).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_10 :
    (((rows 7).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_7_11 :
    (((rows 7).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 7) (parents 7)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_7 :
    leafCheck rowMember (rows 7) (placePattern 7) (parents 7) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_7_0
  · exact mask_7_1
  · exact mask_7_2
  · exact mask_7_3
  · exact mask_7_4
  · exact mask_7_5
  · exact mask_7_6
  · exact mask_7_7
  · exact mask_7_8
  · exact mask_7_9
  · exact mask_7_10
  · exact mask_7_11

set_option maxRecDepth 10000 in
private theorem mask_8_0 :
    (((rows 8).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_8_1 :
    (((rows 8).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_8_2 :
    (((rows 8).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_8_3 :
    (((rows 8).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_8_4 :
    (((rows 8).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_8_5 :
    (((rows 8).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_8_6 :
    (((rows 8).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_8_7 :
    (((rows 8).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 8) (parents 8)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_8 :
    leafCheck rowMember (rows 8) (placePattern 8) (parents 8) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 8 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_8_0
  · exact mask_8_1
  · exact mask_8_2
  · exact mask_8_3
  · exact mask_8_4
  · exact mask_8_5
  · exact mask_8_6
  · exact mask_8_7

set_option maxRecDepth 10000 in
private theorem mask_9_0 :
    (((rows 9).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 9) (parents 9)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_9_1 :
    (((rows 9).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 9) (parents 9)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_9_2 :
    (((rows 9).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 9) (parents 9)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_9_3 :
    (((rows 9).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 9) (parents 9)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_9 :
    leafCheck rowMember (rows 9) (placePattern 9) (parents 9) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 4 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_9_0
  · exact mask_9_1
  · exact mask_9_2
  · exact mask_9_3

set_option maxRecDepth 10000 in
private theorem mask_10_0 :
    (((rows 10).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_1 :
    (((rows 10).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_2 :
    (((rows 10).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_3 :
    (((rows 10).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_4 :
    (((rows 10).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_5 :
    (((rows 10).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_6 :
    (((rows 10).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_7 :
    (((rows 10).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_8 :
    (((rows 10).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_9 :
    (((rows 10).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_10 :
    (((rows 10).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_11 :
    (((rows 10).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_12 :
    (((rows 10).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_13 :
    (((rows 10).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_14 :
    (((rows 10).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_15 :
    (((rows 10).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_16 :
    (((rows 10).drop (64 * 16)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_17 :
    (((rows 10).drop (64 * 17)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_18 :
    (((rows 10).drop (64 * 18)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_10_19 :
    (((rows 10).drop (64 * 19)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 10) (parents 10)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_10 :
    leafCheck rowMember (rows 10) (placePattern 10) (parents 10) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_10_0
  · exact mask_10_1
  · exact mask_10_2
  · exact mask_10_3
  · exact mask_10_4
  · exact mask_10_5
  · exact mask_10_6
  · exact mask_10_7
  · exact mask_10_8
  · exact mask_10_9
  · exact mask_10_10
  · exact mask_10_11
  · exact mask_10_12
  · exact mask_10_13
  · exact mask_10_14
  · exact mask_10_15
  · exact mask_10_16
  · exact mask_10_17
  · exact mask_10_18
  · exact mask_10_19

set_option maxRecDepth 10000 in
private theorem mask_11_0 :
    (((rows 11).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_1 :
    (((rows 11).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_2 :
    (((rows 11).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_3 :
    (((rows 11).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_4 :
    (((rows 11).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_5 :
    (((rows 11).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_6 :
    (((rows 11).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_7 :
    (((rows 11).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_8 :
    (((rows 11).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_9 :
    (((rows 11).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_10 :
    (((rows 11).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_11_11 :
    (((rows 11).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 11) (parents 11)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_11 :
    leafCheck rowMember (rows 11) (placePattern 11) (parents 11) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 12 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_11_0
  · exact mask_11_1
  · exact mask_11_2
  · exact mask_11_3
  · exact mask_11_4
  · exact mask_11_5
  · exact mask_11_6
  · exact mask_11_7
  · exact mask_11_8
  · exact mask_11_9
  · exact mask_11_10
  · exact mask_11_11

set_option maxRecDepth 10000 in
private theorem mask_12_0 :
    (((rows 12).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_1 :
    (((rows 12).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_2 :
    (((rows 12).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_3 :
    (((rows 12).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_4 :
    (((rows 12).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_5 :
    (((rows 12).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_6 :
    (((rows 12).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_7 :
    (((rows 12).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_8 :
    (((rows 12).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_9 :
    (((rows 12).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_10 :
    (((rows 12).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_11 :
    (((rows 12).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_12 :
    (((rows 12).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_13 :
    (((rows 12).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_14 :
    (((rows 12).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_12_15 :
    (((rows 12).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 12) (parents 12)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_12 :
    leafCheck rowMember (rows 12) (placePattern 12) (parents 12) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_12_0
  · exact mask_12_1
  · exact mask_12_2
  · exact mask_12_3
  · exact mask_12_4
  · exact mask_12_5
  · exact mask_12_6
  · exact mask_12_7
  · exact mask_12_8
  · exact mask_12_9
  · exact mask_12_10
  · exact mask_12_11
  · exact mask_12_12
  · exact mask_12_13
  · exact mask_12_14
  · exact mask_12_15

set_option maxRecDepth 10000 in
private theorem mask_13_0 :
    (((rows 13).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_1 :
    (((rows 13).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_2 :
    (((rows 13).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_3 :
    (((rows 13).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_4 :
    (((rows 13).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_5 :
    (((rows 13).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_6 :
    (((rows 13).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_7 :
    (((rows 13).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_8 :
    (((rows 13).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_9 :
    (((rows 13).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_10 :
    (((rows 13).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_11 :
    (((rows 13).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_12 :
    (((rows 13).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_13 :
    (((rows 13).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_14 :
    (((rows 13).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_15 :
    (((rows 13).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_16 :
    (((rows 13).drop (64 * 16)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_17 :
    (((rows 13).drop (64 * 17)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_18 :
    (((rows 13).drop (64 * 18)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_13_19 :
    (((rows 13).drop (64 * 19)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 13) (parents 13)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_13 :
    leafCheck rowMember (rows 13) (placePattern 13) (parents 13) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_13_0
  · exact mask_13_1
  · exact mask_13_2
  · exact mask_13_3
  · exact mask_13_4
  · exact mask_13_5
  · exact mask_13_6
  · exact mask_13_7
  · exact mask_13_8
  · exact mask_13_9
  · exact mask_13_10
  · exact mask_13_11
  · exact mask_13_12
  · exact mask_13_13
  · exact mask_13_14
  · exact mask_13_15
  · exact mask_13_16
  · exact mask_13_17
  · exact mask_13_18
  · exact mask_13_19

set_option maxRecDepth 10000 in
private theorem mask_14_0 :
    (((rows 14).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_1 :
    (((rows 14).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_2 :
    (((rows 14).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_3 :
    (((rows 14).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_4 :
    (((rows 14).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_5 :
    (((rows 14).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_6 :
    (((rows 14).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_7 :
    (((rows 14).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_8 :
    (((rows 14).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_9 :
    (((rows 14).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_10 :
    (((rows 14).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_11 :
    (((rows 14).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_12 :
    (((rows 14).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_13 :
    (((rows 14).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_14 :
    (((rows 14).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_15 :
    (((rows 14).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_16 :
    (((rows 14).drop (64 * 16)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_17 :
    (((rows 14).drop (64 * 17)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_18 :
    (((rows 14).drop (64 * 18)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_14_19 :
    (((rows 14).drop (64 * 19)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 14) (parents 14)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_14 :
    leafCheck rowMember (rows 14) (placePattern 14) (parents 14) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_14_0
  · exact mask_14_1
  · exact mask_14_2
  · exact mask_14_3
  · exact mask_14_4
  · exact mask_14_5
  · exact mask_14_6
  · exact mask_14_7
  · exact mask_14_8
  · exact mask_14_9
  · exact mask_14_10
  · exact mask_14_11
  · exact mask_14_12
  · exact mask_14_13
  · exact mask_14_14
  · exact mask_14_15
  · exact mask_14_16
  · exact mask_14_17
  · exact mask_14_18
  · exact mask_14_19

set_option maxRecDepth 10000 in
private theorem mask_15_0 :
    (((rows 15).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_1 :
    (((rows 15).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_2 :
    (((rows 15).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_3 :
    (((rows 15).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_4 :
    (((rows 15).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_5 :
    (((rows 15).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_6 :
    (((rows 15).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_7 :
    (((rows 15).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_8 :
    (((rows 15).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_9 :
    (((rows 15).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_10 :
    (((rows 15).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_11 :
    (((rows 15).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_12 :
    (((rows 15).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_13 :
    (((rows 15).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_14 :
    (((rows 15).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_15_15 :
    (((rows 15).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 15) (parents 15)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_15 :
    leafCheck rowMember (rows 15) (placePattern 15) (parents 15) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_15_0
  · exact mask_15_1
  · exact mask_15_2
  · exact mask_15_3
  · exact mask_15_4
  · exact mask_15_5
  · exact mask_15_6
  · exact mask_15_7
  · exact mask_15_8
  · exact mask_15_9
  · exact mask_15_10
  · exact mask_15_11
  · exact mask_15_12
  · exact mask_15_13
  · exact mask_15_14
  · exact mask_15_15

set_option maxRecDepth 10000 in
private theorem mask_16_0 :
    (((rows 16).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_1 :
    (((rows 16).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_2 :
    (((rows 16).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_3 :
    (((rows 16).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_4 :
    (((rows 16).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_5 :
    (((rows 16).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_6 :
    (((rows 16).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_7 :
    (((rows 16).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_8 :
    (((rows 16).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_9 :
    (((rows 16).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_10 :
    (((rows 16).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_11 :
    (((rows 16).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_12 :
    (((rows 16).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_13 :
    (((rows 16).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_14 :
    (((rows 16).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_15 :
    (((rows 16).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_16 :
    (((rows 16).drop (64 * 16)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_17 :
    (((rows 16).drop (64 * 17)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_18 :
    (((rows 16).drop (64 * 18)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_16_19 :
    (((rows 16).drop (64 * 19)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 16) (parents 16)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_16 :
    leafCheck rowMember (rows 16) (placePattern 16) (parents 16) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 20 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_16_0
  · exact mask_16_1
  · exact mask_16_2
  · exact mask_16_3
  · exact mask_16_4
  · exact mask_16_5
  · exact mask_16_6
  · exact mask_16_7
  · exact mask_16_8
  · exact mask_16_9
  · exact mask_16_10
  · exact mask_16_11
  · exact mask_16_12
  · exact mask_16_13
  · exact mask_16_14
  · exact mask_16_15
  · exact mask_16_16
  · exact mask_16_17
  · exact mask_16_18
  · exact mask_16_19

set_option maxRecDepth 10000 in
private theorem mask_17_0 :
    (((rows 17).drop (64 * 0)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_1 :
    (((rows 17).drop (64 * 1)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_2 :
    (((rows 17).drop (64 * 2)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_3 :
    (((rows 17).drop (64 * 3)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_4 :
    (((rows 17).drop (64 * 4)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_5 :
    (((rows 17).drop (64 * 5)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_6 :
    (((rows 17).drop (64 * 6)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_7 :
    (((rows 17).drop (64 * 7)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_8 :
    (((rows 17).drop (64 * 8)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_9 :
    (((rows 17).drop (64 * 9)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_10 :
    (((rows 17).drop (64 * 10)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_11 :
    (((rows 17).drop (64 * 11)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_12 :
    (((rows 17).drop (64 * 12)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_13 :
    (((rows 17).drop (64 * 13)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_14 :
    (((rows 17).drop (64 * 14)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem mask_17_15 :
    (((rows 17).drop (64 * 15)).take 64).all
      (fun r => rowLeafCheck rowMember r (placePattern 17) (parents 17)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked_17 :
    leafCheck rowMember (rows 17) (placePattern 17) (parents 17) = true := by
  simp only [leafCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, ?_⟩
  refine all_of_chunk_checks _ 64 16 _ (by decide +kernel) ?_
  intro k
  fin_cases k
  · exact mask_17_0
  · exact mask_17_1
  · exact mask_17_2
  · exact mask_17_3
  · exact mask_17_4
  · exact mask_17_5
  · exact mask_17_6
  · exact mask_17_7
  · exact mask_17_8
  · exact mask_17_9
  · exact mask_17_10
  · exact mask_17_11
  · exact mask_17_12
  · exact mask_17_13
  · exact mask_17_14
  · exact mask_17_15

/-- Every stored support satisfies the prescribed leaf elimination. -/
public theorem leafCheck_checked (t : Fin 18) :
    leafCheck rowMember (rows t) (placePattern t) (parents t) = true := by
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
  · exact checked_9
  · exact checked_10
  · exact checked_11
  · exact checked_12
  · exact checked_13
  · exact checked_14
  · exact checked_15
  · exact checked_16
  · exact checked_17

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
