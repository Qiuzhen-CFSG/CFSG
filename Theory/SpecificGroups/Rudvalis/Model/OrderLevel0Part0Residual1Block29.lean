module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 123–124

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point123Slice0 : pointSliceCheck 1 2818 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice1 : pointSliceCheck 1 2818 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice2 : pointSliceCheck 1 2818 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice3 : pointSliceCheck 1 2818 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice4 : pointSliceCheck 1 2818 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice5 : pointSliceCheck 1 2818 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice6 : pointSliceCheck 1 2818 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice7 : pointSliceCheck 1 2818 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice8 : pointSliceCheck 1 2818 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice9 : pointSliceCheck 1 2818 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice10 : pointSliceCheck 1 2818 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice11 : pointSliceCheck 1 2818 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice12 : pointSliceCheck 1 2818 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice13 : pointSliceCheck 1 2818 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice14 : pointSliceCheck 1 2818 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice15 : pointSliceCheck 1 2818 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice16 : pointSliceCheck 1 2818 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice17 : pointSliceCheck 1 2818 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice18 : pointSliceCheck 1 2818 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice19 : pointSliceCheck 1 2818 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice20 : pointSliceCheck 1 2818 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice21 : pointSliceCheck 1 2818 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice22 : pointSliceCheck 1 2818 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice23 : pointSliceCheck 1 2818 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice24 : pointSliceCheck 1 2818 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice25 : pointSliceCheck 1 2818 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice26 : pointSliceCheck 1 2818 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice27 : pointSliceCheck 1 2818 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123Slice28 : pointSliceCheck 1 2818 28 := by
  decide +kernel

/-- Original transition at residual index 123, certified on every point. -/
public theorem point123 : stepCheck 1 2818 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point123Slice0
  · exact point123Slice1
  · exact point123Slice2
  · exact point123Slice3
  · exact point123Slice4
  · exact point123Slice5
  · exact point123Slice6
  · exact point123Slice7
  · exact point123Slice8
  · exact point123Slice9
  · exact point123Slice10
  · exact point123Slice11
  · exact point123Slice12
  · exact point123Slice13
  · exact point123Slice14
  · exact point123Slice15
  · exact point123Slice16
  · exact point123Slice17
  · exact point123Slice18
  · exact point123Slice19
  · exact point123Slice20
  · exact point123Slice21
  · exact point123Slice22
  · exact point123Slice23
  · exact point123Slice24
  · exact point123Slice25
  · exact point123Slice26
  · exact point123Slice27
  · exact point123Slice28

set_option maxHeartbeats 1600000 in
private theorem point124Slice0 : pointSliceCheck 0 2942 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice1 : pointSliceCheck 0 2942 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice2 : pointSliceCheck 0 2942 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice3 : pointSliceCheck 0 2942 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice4 : pointSliceCheck 0 2942 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice5 : pointSliceCheck 0 2942 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice6 : pointSliceCheck 0 2942 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice7 : pointSliceCheck 0 2942 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice8 : pointSliceCheck 0 2942 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice9 : pointSliceCheck 0 2942 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice10 : pointSliceCheck 0 2942 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice11 : pointSliceCheck 0 2942 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice12 : pointSliceCheck 0 2942 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice13 : pointSliceCheck 0 2942 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice14 : pointSliceCheck 0 2942 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice15 : pointSliceCheck 0 2942 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice16 : pointSliceCheck 0 2942 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice17 : pointSliceCheck 0 2942 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice18 : pointSliceCheck 0 2942 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice19 : pointSliceCheck 0 2942 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice20 : pointSliceCheck 0 2942 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice21 : pointSliceCheck 0 2942 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice22 : pointSliceCheck 0 2942 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice23 : pointSliceCheck 0 2942 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice24 : pointSliceCheck 0 2942 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice25 : pointSliceCheck 0 2942 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice26 : pointSliceCheck 0 2942 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice27 : pointSliceCheck 0 2942 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124Slice28 : pointSliceCheck 0 2942 28 := by
  decide +kernel

/-- Original transition at residual index 124, certified on every point. -/
public theorem point124 : stepCheck 0 2942 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point124Slice0
  · exact point124Slice1
  · exact point124Slice2
  · exact point124Slice3
  · exact point124Slice4
  · exact point124Slice5
  · exact point124Slice6
  · exact point124Slice7
  · exact point124Slice8
  · exact point124Slice9
  · exact point124Slice10
  · exact point124Slice11
  · exact point124Slice12
  · exact point124Slice13
  · exact point124Slice14
  · exact point124Slice15
  · exact point124Slice16
  · exact point124Slice17
  · exact point124Slice18
  · exact point124Slice19
  · exact point124Slice20
  · exact point124Slice21
  · exact point124Slice22
  · exact point124Slice23
  · exact point124Slice24
  · exact point124Slice25
  · exact point124Slice26
  · exact point124Slice27
  · exact point124Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
