module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 95–96

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point95Slice0 : pointSliceCheck 0 2527 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice1 : pointSliceCheck 0 2527 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice2 : pointSliceCheck 0 2527 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice3 : pointSliceCheck 0 2527 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice4 : pointSliceCheck 0 2527 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice5 : pointSliceCheck 0 2527 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice6 : pointSliceCheck 0 2527 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice7 : pointSliceCheck 0 2527 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice8 : pointSliceCheck 0 2527 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice9 : pointSliceCheck 0 2527 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice10 : pointSliceCheck 0 2527 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice11 : pointSliceCheck 0 2527 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice12 : pointSliceCheck 0 2527 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice13 : pointSliceCheck 0 2527 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice14 : pointSliceCheck 0 2527 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice15 : pointSliceCheck 0 2527 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice16 : pointSliceCheck 0 2527 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice17 : pointSliceCheck 0 2527 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice18 : pointSliceCheck 0 2527 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice19 : pointSliceCheck 0 2527 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice20 : pointSliceCheck 0 2527 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice21 : pointSliceCheck 0 2527 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice22 : pointSliceCheck 0 2527 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice23 : pointSliceCheck 0 2527 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice24 : pointSliceCheck 0 2527 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice25 : pointSliceCheck 0 2527 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice26 : pointSliceCheck 0 2527 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice27 : pointSliceCheck 0 2527 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point95Slice28 : pointSliceCheck 0 2527 28 := by
  decide +kernel

/-- Original transition at residual index 95, certified on every point. -/
public theorem point95 : stepCheck 0 2527 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point95Slice0
  · exact point95Slice1
  · exact point95Slice2
  · exact point95Slice3
  · exact point95Slice4
  · exact point95Slice5
  · exact point95Slice6
  · exact point95Slice7
  · exact point95Slice8
  · exact point95Slice9
  · exact point95Slice10
  · exact point95Slice11
  · exact point95Slice12
  · exact point95Slice13
  · exact point95Slice14
  · exact point95Slice15
  · exact point95Slice16
  · exact point95Slice17
  · exact point95Slice18
  · exact point95Slice19
  · exact point95Slice20
  · exact point95Slice21
  · exact point95Slice22
  · exact point95Slice23
  · exact point95Slice24
  · exact point95Slice25
  · exact point95Slice26
  · exact point95Slice27
  · exact point95Slice28

set_option maxHeartbeats 1600000 in
private theorem point96Slice0 : pointSliceCheck 0 2528 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice1 : pointSliceCheck 0 2528 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice2 : pointSliceCheck 0 2528 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice3 : pointSliceCheck 0 2528 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice4 : pointSliceCheck 0 2528 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice5 : pointSliceCheck 0 2528 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice6 : pointSliceCheck 0 2528 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice7 : pointSliceCheck 0 2528 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice8 : pointSliceCheck 0 2528 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice9 : pointSliceCheck 0 2528 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice10 : pointSliceCheck 0 2528 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice11 : pointSliceCheck 0 2528 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice12 : pointSliceCheck 0 2528 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice13 : pointSliceCheck 0 2528 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice14 : pointSliceCheck 0 2528 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice15 : pointSliceCheck 0 2528 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice16 : pointSliceCheck 0 2528 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice17 : pointSliceCheck 0 2528 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice18 : pointSliceCheck 0 2528 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice19 : pointSliceCheck 0 2528 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice20 : pointSliceCheck 0 2528 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice21 : pointSliceCheck 0 2528 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice22 : pointSliceCheck 0 2528 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice23 : pointSliceCheck 0 2528 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice24 : pointSliceCheck 0 2528 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice25 : pointSliceCheck 0 2528 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice26 : pointSliceCheck 0 2528 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice27 : pointSliceCheck 0 2528 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point96Slice28 : pointSliceCheck 0 2528 28 := by
  decide +kernel

/-- Original transition at residual index 96, certified on every point. -/
public theorem point96 : stepCheck 0 2528 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point96Slice0
  · exact point96Slice1
  · exact point96Slice2
  · exact point96Slice3
  · exact point96Slice4
  · exact point96Slice5
  · exact point96Slice6
  · exact point96Slice7
  · exact point96Slice8
  · exact point96Slice9
  · exact point96Slice10
  · exact point96Slice11
  · exact point96Slice12
  · exact point96Slice13
  · exact point96Slice14
  · exact point96Slice15
  · exact point96Slice16
  · exact point96Slice17
  · exact point96Slice18
  · exact point96Slice19
  · exact point96Slice20
  · exact point96Slice21
  · exact point96Slice22
  · exact point96Slice23
  · exact point96Slice24
  · exact point96Slice25
  · exact point96Slice26
  · exact point96Slice27
  · exact point96Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
