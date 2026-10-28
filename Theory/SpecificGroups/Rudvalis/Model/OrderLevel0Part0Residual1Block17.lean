module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 99–100

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point99Slice0 : pointSliceCheck 1 2520 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice1 : pointSliceCheck 1 2520 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice2 : pointSliceCheck 1 2520 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice3 : pointSliceCheck 1 2520 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice4 : pointSliceCheck 1 2520 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice5 : pointSliceCheck 1 2520 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice6 : pointSliceCheck 1 2520 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice7 : pointSliceCheck 1 2520 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice8 : pointSliceCheck 1 2520 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice9 : pointSliceCheck 1 2520 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice10 : pointSliceCheck 1 2520 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice11 : pointSliceCheck 1 2520 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice12 : pointSliceCheck 1 2520 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice13 : pointSliceCheck 1 2520 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice14 : pointSliceCheck 1 2520 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice15 : pointSliceCheck 1 2520 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice16 : pointSliceCheck 1 2520 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice17 : pointSliceCheck 1 2520 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice18 : pointSliceCheck 1 2520 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice19 : pointSliceCheck 1 2520 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice20 : pointSliceCheck 1 2520 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice21 : pointSliceCheck 1 2520 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice22 : pointSliceCheck 1 2520 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice23 : pointSliceCheck 1 2520 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice24 : pointSliceCheck 1 2520 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice25 : pointSliceCheck 1 2520 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice26 : pointSliceCheck 1 2520 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice27 : pointSliceCheck 1 2520 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point99Slice28 : pointSliceCheck 1 2520 28 := by
  decide +kernel

/-- Original transition at residual index 99, certified on every point. -/
public theorem point99 : stepCheck 1 2520 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point99Slice0
  · exact point99Slice1
  · exact point99Slice2
  · exact point99Slice3
  · exact point99Slice4
  · exact point99Slice5
  · exact point99Slice6
  · exact point99Slice7
  · exact point99Slice8
  · exact point99Slice9
  · exact point99Slice10
  · exact point99Slice11
  · exact point99Slice12
  · exact point99Slice13
  · exact point99Slice14
  · exact point99Slice15
  · exact point99Slice16
  · exact point99Slice17
  · exact point99Slice18
  · exact point99Slice19
  · exact point99Slice20
  · exact point99Slice21
  · exact point99Slice22
  · exact point99Slice23
  · exact point99Slice24
  · exact point99Slice25
  · exact point99Slice26
  · exact point99Slice27
  · exact point99Slice28

set_option maxHeartbeats 1600000 in
private theorem point100Slice0 : pointSliceCheck 1 2526 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice1 : pointSliceCheck 1 2526 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice2 : pointSliceCheck 1 2526 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice3 : pointSliceCheck 1 2526 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice4 : pointSliceCheck 1 2526 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice5 : pointSliceCheck 1 2526 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice6 : pointSliceCheck 1 2526 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice7 : pointSliceCheck 1 2526 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice8 : pointSliceCheck 1 2526 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice9 : pointSliceCheck 1 2526 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice10 : pointSliceCheck 1 2526 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice11 : pointSliceCheck 1 2526 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice12 : pointSliceCheck 1 2526 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice13 : pointSliceCheck 1 2526 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice14 : pointSliceCheck 1 2526 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice15 : pointSliceCheck 1 2526 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice16 : pointSliceCheck 1 2526 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice17 : pointSliceCheck 1 2526 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice18 : pointSliceCheck 1 2526 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice19 : pointSliceCheck 1 2526 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice20 : pointSliceCheck 1 2526 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice21 : pointSliceCheck 1 2526 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice22 : pointSliceCheck 1 2526 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice23 : pointSliceCheck 1 2526 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice24 : pointSliceCheck 1 2526 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice25 : pointSliceCheck 1 2526 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice26 : pointSliceCheck 1 2526 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice27 : pointSliceCheck 1 2526 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point100Slice28 : pointSliceCheck 1 2526 28 := by
  decide +kernel

/-- Original transition at residual index 100, certified on every point. -/
public theorem point100 : stepCheck 1 2526 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point100Slice0
  · exact point100Slice1
  · exact point100Slice2
  · exact point100Slice3
  · exact point100Slice4
  · exact point100Slice5
  · exact point100Slice6
  · exact point100Slice7
  · exact point100Slice8
  · exact point100Slice9
  · exact point100Slice10
  · exact point100Slice11
  · exact point100Slice12
  · exact point100Slice13
  · exact point100Slice14
  · exact point100Slice15
  · exact point100Slice16
  · exact point100Slice17
  · exact point100Slice18
  · exact point100Slice19
  · exact point100Slice20
  · exact point100Slice21
  · exact point100Slice22
  · exact point100Slice23
  · exact point100Slice24
  · exact point100Slice25
  · exact point100Slice26
  · exact point100Slice27
  · exact point100Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
