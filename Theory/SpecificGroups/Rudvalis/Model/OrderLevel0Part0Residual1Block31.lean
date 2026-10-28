module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 127–128

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point127Slice0 : pointSliceCheck 0 2948 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice1 : pointSliceCheck 0 2948 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice2 : pointSliceCheck 0 2948 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice3 : pointSliceCheck 0 2948 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice4 : pointSliceCheck 0 2948 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice5 : pointSliceCheck 0 2948 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice6 : pointSliceCheck 0 2948 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice7 : pointSliceCheck 0 2948 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice8 : pointSliceCheck 0 2948 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice9 : pointSliceCheck 0 2948 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice10 : pointSliceCheck 0 2948 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice11 : pointSliceCheck 0 2948 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice12 : pointSliceCheck 0 2948 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice13 : pointSliceCheck 0 2948 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice14 : pointSliceCheck 0 2948 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice15 : pointSliceCheck 0 2948 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice16 : pointSliceCheck 0 2948 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice17 : pointSliceCheck 0 2948 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice18 : pointSliceCheck 0 2948 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice19 : pointSliceCheck 0 2948 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice20 : pointSliceCheck 0 2948 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice21 : pointSliceCheck 0 2948 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice22 : pointSliceCheck 0 2948 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice23 : pointSliceCheck 0 2948 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice24 : pointSliceCheck 0 2948 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice25 : pointSliceCheck 0 2948 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice26 : pointSliceCheck 0 2948 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice27 : pointSliceCheck 0 2948 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127Slice28 : pointSliceCheck 0 2948 28 := by
  decide +kernel

/-- Original transition at residual index 127, certified on every point. -/
public theorem point127 : stepCheck 0 2948 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point127Slice0
  · exact point127Slice1
  · exact point127Slice2
  · exact point127Slice3
  · exact point127Slice4
  · exact point127Slice5
  · exact point127Slice6
  · exact point127Slice7
  · exact point127Slice8
  · exact point127Slice9
  · exact point127Slice10
  · exact point127Slice11
  · exact point127Slice12
  · exact point127Slice13
  · exact point127Slice14
  · exact point127Slice15
  · exact point127Slice16
  · exact point127Slice17
  · exact point127Slice18
  · exact point127Slice19
  · exact point127Slice20
  · exact point127Slice21
  · exact point127Slice22
  · exact point127Slice23
  · exact point127Slice24
  · exact point127Slice25
  · exact point127Slice26
  · exact point127Slice27
  · exact point127Slice28

set_option maxHeartbeats 1600000 in
private theorem point128Slice0 : pointSliceCheck 0 2952 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice1 : pointSliceCheck 0 2952 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice2 : pointSliceCheck 0 2952 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice3 : pointSliceCheck 0 2952 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice4 : pointSliceCheck 0 2952 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice5 : pointSliceCheck 0 2952 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice6 : pointSliceCheck 0 2952 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice7 : pointSliceCheck 0 2952 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice8 : pointSliceCheck 0 2952 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice9 : pointSliceCheck 0 2952 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice10 : pointSliceCheck 0 2952 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice11 : pointSliceCheck 0 2952 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice12 : pointSliceCheck 0 2952 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice13 : pointSliceCheck 0 2952 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice14 : pointSliceCheck 0 2952 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice15 : pointSliceCheck 0 2952 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice16 : pointSliceCheck 0 2952 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice17 : pointSliceCheck 0 2952 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice18 : pointSliceCheck 0 2952 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice19 : pointSliceCheck 0 2952 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice20 : pointSliceCheck 0 2952 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice21 : pointSliceCheck 0 2952 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice22 : pointSliceCheck 0 2952 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice23 : pointSliceCheck 0 2952 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice24 : pointSliceCheck 0 2952 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice25 : pointSliceCheck 0 2952 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice26 : pointSliceCheck 0 2952 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice27 : pointSliceCheck 0 2952 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128Slice28 : pointSliceCheck 0 2952 28 := by
  decide +kernel

/-- Original transition at residual index 128, certified on every point. -/
public theorem point128 : stepCheck 0 2952 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point128Slice0
  · exact point128Slice1
  · exact point128Slice2
  · exact point128Slice3
  · exact point128Slice4
  · exact point128Slice5
  · exact point128Slice6
  · exact point128Slice7
  · exact point128Slice8
  · exact point128Slice9
  · exact point128Slice10
  · exact point128Slice11
  · exact point128Slice12
  · exact point128Slice13
  · exact point128Slice14
  · exact point128Slice15
  · exact point128Slice16
  · exact point128Slice17
  · exact point128Slice18
  · exact point128Slice19
  · exact point128Slice20
  · exact point128Slice21
  · exact point128Slice22
  · exact point128Slice23
  · exact point128Slice24
  · exact point128Slice25
  · exact point128Slice26
  · exact point128Slice27
  · exact point128Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
