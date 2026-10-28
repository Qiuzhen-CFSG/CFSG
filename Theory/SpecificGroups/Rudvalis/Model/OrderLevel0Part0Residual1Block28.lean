module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 121–122

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point121Slice0 : pointSliceCheck 1 2802 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice1 : pointSliceCheck 1 2802 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice2 : pointSliceCheck 1 2802 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice3 : pointSliceCheck 1 2802 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice4 : pointSliceCheck 1 2802 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice5 : pointSliceCheck 1 2802 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice6 : pointSliceCheck 1 2802 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice7 : pointSliceCheck 1 2802 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice8 : pointSliceCheck 1 2802 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice9 : pointSliceCheck 1 2802 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice10 : pointSliceCheck 1 2802 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice11 : pointSliceCheck 1 2802 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice12 : pointSliceCheck 1 2802 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice13 : pointSliceCheck 1 2802 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice14 : pointSliceCheck 1 2802 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice15 : pointSliceCheck 1 2802 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice16 : pointSliceCheck 1 2802 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice17 : pointSliceCheck 1 2802 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice18 : pointSliceCheck 1 2802 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice19 : pointSliceCheck 1 2802 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice20 : pointSliceCheck 1 2802 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice21 : pointSliceCheck 1 2802 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice22 : pointSliceCheck 1 2802 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice23 : pointSliceCheck 1 2802 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice24 : pointSliceCheck 1 2802 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice25 : pointSliceCheck 1 2802 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice26 : pointSliceCheck 1 2802 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice27 : pointSliceCheck 1 2802 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121Slice28 : pointSliceCheck 1 2802 28 := by
  decide +kernel

/-- Original transition at residual index 121, certified on every point. -/
public theorem point121 : stepCheck 1 2802 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point121Slice0
  · exact point121Slice1
  · exact point121Slice2
  · exact point121Slice3
  · exact point121Slice4
  · exact point121Slice5
  · exact point121Slice6
  · exact point121Slice7
  · exact point121Slice8
  · exact point121Slice9
  · exact point121Slice10
  · exact point121Slice11
  · exact point121Slice12
  · exact point121Slice13
  · exact point121Slice14
  · exact point121Slice15
  · exact point121Slice16
  · exact point121Slice17
  · exact point121Slice18
  · exact point121Slice19
  · exact point121Slice20
  · exact point121Slice21
  · exact point121Slice22
  · exact point121Slice23
  · exact point121Slice24
  · exact point121Slice25
  · exact point121Slice26
  · exact point121Slice27
  · exact point121Slice28

set_option maxHeartbeats 1600000 in
private theorem point122Slice0 : pointSliceCheck 1 2811 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice1 : pointSliceCheck 1 2811 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice2 : pointSliceCheck 1 2811 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice3 : pointSliceCheck 1 2811 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice4 : pointSliceCheck 1 2811 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice5 : pointSliceCheck 1 2811 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice6 : pointSliceCheck 1 2811 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice7 : pointSliceCheck 1 2811 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice8 : pointSliceCheck 1 2811 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice9 : pointSliceCheck 1 2811 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice10 : pointSliceCheck 1 2811 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice11 : pointSliceCheck 1 2811 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice12 : pointSliceCheck 1 2811 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice13 : pointSliceCheck 1 2811 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice14 : pointSliceCheck 1 2811 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice15 : pointSliceCheck 1 2811 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice16 : pointSliceCheck 1 2811 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice17 : pointSliceCheck 1 2811 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice18 : pointSliceCheck 1 2811 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice19 : pointSliceCheck 1 2811 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice20 : pointSliceCheck 1 2811 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice21 : pointSliceCheck 1 2811 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice22 : pointSliceCheck 1 2811 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice23 : pointSliceCheck 1 2811 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice24 : pointSliceCheck 1 2811 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice25 : pointSliceCheck 1 2811 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice26 : pointSliceCheck 1 2811 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice27 : pointSliceCheck 1 2811 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122Slice28 : pointSliceCheck 1 2811 28 := by
  decide +kernel

/-- Original transition at residual index 122, certified on every point. -/
public theorem point122 : stepCheck 1 2811 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point122Slice0
  · exact point122Slice1
  · exact point122Slice2
  · exact point122Slice3
  · exact point122Slice4
  · exact point122Slice5
  · exact point122Slice6
  · exact point122Slice7
  · exact point122Slice8
  · exact point122Slice9
  · exact point122Slice10
  · exact point122Slice11
  · exact point122Slice12
  · exact point122Slice13
  · exact point122Slice14
  · exact point122Slice15
  · exact point122Slice16
  · exact point122Slice17
  · exact point122Slice18
  · exact point122Slice19
  · exact point122Slice20
  · exact point122Slice21
  · exact point122Slice22
  · exact point122Slice23
  · exact point122Slice24
  · exact point122Slice25
  · exact point122Slice26
  · exact point122Slice27
  · exact point122Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
