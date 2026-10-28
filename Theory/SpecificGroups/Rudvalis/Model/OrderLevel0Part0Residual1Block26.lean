module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 117–118

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point117Slice0 : pointSliceCheck 0 2809 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice1 : pointSliceCheck 0 2809 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice2 : pointSliceCheck 0 2809 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice3 : pointSliceCheck 0 2809 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice4 : pointSliceCheck 0 2809 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice5 : pointSliceCheck 0 2809 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice6 : pointSliceCheck 0 2809 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice7 : pointSliceCheck 0 2809 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice8 : pointSliceCheck 0 2809 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice9 : pointSliceCheck 0 2809 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice10 : pointSliceCheck 0 2809 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice11 : pointSliceCheck 0 2809 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice12 : pointSliceCheck 0 2809 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice13 : pointSliceCheck 0 2809 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice14 : pointSliceCheck 0 2809 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice15 : pointSliceCheck 0 2809 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice16 : pointSliceCheck 0 2809 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice17 : pointSliceCheck 0 2809 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice18 : pointSliceCheck 0 2809 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice19 : pointSliceCheck 0 2809 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice20 : pointSliceCheck 0 2809 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice21 : pointSliceCheck 0 2809 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice22 : pointSliceCheck 0 2809 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice23 : pointSliceCheck 0 2809 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice24 : pointSliceCheck 0 2809 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice25 : pointSliceCheck 0 2809 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice26 : pointSliceCheck 0 2809 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice27 : pointSliceCheck 0 2809 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117Slice28 : pointSliceCheck 0 2809 28 := by
  decide +kernel

/-- Original transition at residual index 117, certified on every point. -/
public theorem point117 : stepCheck 0 2809 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point117Slice0
  · exact point117Slice1
  · exact point117Slice2
  · exact point117Slice3
  · exact point117Slice4
  · exact point117Slice5
  · exact point117Slice6
  · exact point117Slice7
  · exact point117Slice8
  · exact point117Slice9
  · exact point117Slice10
  · exact point117Slice11
  · exact point117Slice12
  · exact point117Slice13
  · exact point117Slice14
  · exact point117Slice15
  · exact point117Slice16
  · exact point117Slice17
  · exact point117Slice18
  · exact point117Slice19
  · exact point117Slice20
  · exact point117Slice21
  · exact point117Slice22
  · exact point117Slice23
  · exact point117Slice24
  · exact point117Slice25
  · exact point117Slice26
  · exact point117Slice27
  · exact point117Slice28

set_option maxHeartbeats 1600000 in
private theorem point118Slice0 : pointSliceCheck 0 2812 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice1 : pointSliceCheck 0 2812 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice2 : pointSliceCheck 0 2812 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice3 : pointSliceCheck 0 2812 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice4 : pointSliceCheck 0 2812 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice5 : pointSliceCheck 0 2812 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice6 : pointSliceCheck 0 2812 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice7 : pointSliceCheck 0 2812 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice8 : pointSliceCheck 0 2812 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice9 : pointSliceCheck 0 2812 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice10 : pointSliceCheck 0 2812 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice11 : pointSliceCheck 0 2812 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice12 : pointSliceCheck 0 2812 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice13 : pointSliceCheck 0 2812 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice14 : pointSliceCheck 0 2812 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice15 : pointSliceCheck 0 2812 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice16 : pointSliceCheck 0 2812 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice17 : pointSliceCheck 0 2812 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice18 : pointSliceCheck 0 2812 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice19 : pointSliceCheck 0 2812 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice20 : pointSliceCheck 0 2812 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice21 : pointSliceCheck 0 2812 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice22 : pointSliceCheck 0 2812 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice23 : pointSliceCheck 0 2812 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice24 : pointSliceCheck 0 2812 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice25 : pointSliceCheck 0 2812 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice26 : pointSliceCheck 0 2812 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice27 : pointSliceCheck 0 2812 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118Slice28 : pointSliceCheck 0 2812 28 := by
  decide +kernel

/-- Original transition at residual index 118, certified on every point. -/
public theorem point118 : stepCheck 0 2812 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point118Slice0
  · exact point118Slice1
  · exact point118Slice2
  · exact point118Slice3
  · exact point118Slice4
  · exact point118Slice5
  · exact point118Slice6
  · exact point118Slice7
  · exact point118Slice8
  · exact point118Slice9
  · exact point118Slice10
  · exact point118Slice11
  · exact point118Slice12
  · exact point118Slice13
  · exact point118Slice14
  · exact point118Slice15
  · exact point118Slice16
  · exact point118Slice17
  · exact point118Slice18
  · exact point118Slice19
  · exact point118Slice20
  · exact point118Slice21
  · exact point118Slice22
  · exact point118Slice23
  · exact point118Slice24
  · exact point118Slice25
  · exact point118Slice26
  · exact point118Slice27
  · exact point118Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
