module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 105–106

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point105Slice0 : pointSliceCheck 0 2667 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice1 : pointSliceCheck 0 2667 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice2 : pointSliceCheck 0 2667 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice3 : pointSliceCheck 0 2667 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice4 : pointSliceCheck 0 2667 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice5 : pointSliceCheck 0 2667 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice6 : pointSliceCheck 0 2667 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice7 : pointSliceCheck 0 2667 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice8 : pointSliceCheck 0 2667 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice9 : pointSliceCheck 0 2667 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice10 : pointSliceCheck 0 2667 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice11 : pointSliceCheck 0 2667 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice12 : pointSliceCheck 0 2667 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice13 : pointSliceCheck 0 2667 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice14 : pointSliceCheck 0 2667 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice15 : pointSliceCheck 0 2667 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice16 : pointSliceCheck 0 2667 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice17 : pointSliceCheck 0 2667 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice18 : pointSliceCheck 0 2667 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice19 : pointSliceCheck 0 2667 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice20 : pointSliceCheck 0 2667 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice21 : pointSliceCheck 0 2667 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice22 : pointSliceCheck 0 2667 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice23 : pointSliceCheck 0 2667 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice24 : pointSliceCheck 0 2667 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice25 : pointSliceCheck 0 2667 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice26 : pointSliceCheck 0 2667 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice27 : pointSliceCheck 0 2667 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point105Slice28 : pointSliceCheck 0 2667 28 := by
  decide +kernel

/-- Original transition at residual index 105, certified on every point. -/
public theorem point105 : stepCheck 0 2667 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point105Slice0
  · exact point105Slice1
  · exact point105Slice2
  · exact point105Slice3
  · exact point105Slice4
  · exact point105Slice5
  · exact point105Slice6
  · exact point105Slice7
  · exact point105Slice8
  · exact point105Slice9
  · exact point105Slice10
  · exact point105Slice11
  · exact point105Slice12
  · exact point105Slice13
  · exact point105Slice14
  · exact point105Slice15
  · exact point105Slice16
  · exact point105Slice17
  · exact point105Slice18
  · exact point105Slice19
  · exact point105Slice20
  · exact point105Slice21
  · exact point105Slice22
  · exact point105Slice23
  · exact point105Slice24
  · exact point105Slice25
  · exact point105Slice26
  · exact point105Slice27
  · exact point105Slice28

set_option maxHeartbeats 1600000 in
private theorem point106Slice0 : pointSliceCheck 0 2668 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice1 : pointSliceCheck 0 2668 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice2 : pointSliceCheck 0 2668 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice3 : pointSliceCheck 0 2668 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice4 : pointSliceCheck 0 2668 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice5 : pointSliceCheck 0 2668 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice6 : pointSliceCheck 0 2668 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice7 : pointSliceCheck 0 2668 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice8 : pointSliceCheck 0 2668 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice9 : pointSliceCheck 0 2668 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice10 : pointSliceCheck 0 2668 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice11 : pointSliceCheck 0 2668 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice12 : pointSliceCheck 0 2668 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice13 : pointSliceCheck 0 2668 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice14 : pointSliceCheck 0 2668 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice15 : pointSliceCheck 0 2668 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice16 : pointSliceCheck 0 2668 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice17 : pointSliceCheck 0 2668 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice18 : pointSliceCheck 0 2668 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice19 : pointSliceCheck 0 2668 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice20 : pointSliceCheck 0 2668 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice21 : pointSliceCheck 0 2668 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice22 : pointSliceCheck 0 2668 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice23 : pointSliceCheck 0 2668 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice24 : pointSliceCheck 0 2668 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice25 : pointSliceCheck 0 2668 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice26 : pointSliceCheck 0 2668 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice27 : pointSliceCheck 0 2668 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point106Slice28 : pointSliceCheck 0 2668 28 := by
  decide +kernel

/-- Original transition at residual index 106, certified on every point. -/
public theorem point106 : stepCheck 0 2668 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point106Slice0
  · exact point106Slice1
  · exact point106Slice2
  · exact point106Slice3
  · exact point106Slice4
  · exact point106Slice5
  · exact point106Slice6
  · exact point106Slice7
  · exact point106Slice8
  · exact point106Slice9
  · exact point106Slice10
  · exact point106Slice11
  · exact point106Slice12
  · exact point106Slice13
  · exact point106Slice14
  · exact point106Slice15
  · exact point106Slice16
  · exact point106Slice17
  · exact point106Slice18
  · exact point106Slice19
  · exact point106Slice20
  · exact point106Slice21
  · exact point106Slice22
  · exact point106Slice23
  · exact point106Slice24
  · exact point106Slice25
  · exact point106Slice26
  · exact point106Slice27
  · exact point106Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
