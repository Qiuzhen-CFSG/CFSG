module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 67–68

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point67Slice0 : pointSliceCheck 1 2107 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice1 : pointSliceCheck 1 2107 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice2 : pointSliceCheck 1 2107 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice3 : pointSliceCheck 1 2107 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice4 : pointSliceCheck 1 2107 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice5 : pointSliceCheck 1 2107 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice6 : pointSliceCheck 1 2107 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice7 : pointSliceCheck 1 2107 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice8 : pointSliceCheck 1 2107 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice9 : pointSliceCheck 1 2107 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice10 : pointSliceCheck 1 2107 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice11 : pointSliceCheck 1 2107 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice12 : pointSliceCheck 1 2107 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice13 : pointSliceCheck 1 2107 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice14 : pointSliceCheck 1 2107 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice15 : pointSliceCheck 1 2107 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice16 : pointSliceCheck 1 2107 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice17 : pointSliceCheck 1 2107 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice18 : pointSliceCheck 1 2107 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice19 : pointSliceCheck 1 2107 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice20 : pointSliceCheck 1 2107 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice21 : pointSliceCheck 1 2107 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice22 : pointSliceCheck 1 2107 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice23 : pointSliceCheck 1 2107 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice24 : pointSliceCheck 1 2107 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice25 : pointSliceCheck 1 2107 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice26 : pointSliceCheck 1 2107 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice27 : pointSliceCheck 1 2107 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice28 : pointSliceCheck 1 2107 28 := by
  decide +kernel

/-- Original transition at residual index 67, certified on every point. -/
public theorem point67 : stepCheck 1 2107 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point67Slice0
  · exact point67Slice1
  · exact point67Slice2
  · exact point67Slice3
  · exact point67Slice4
  · exact point67Slice5
  · exact point67Slice6
  · exact point67Slice7
  · exact point67Slice8
  · exact point67Slice9
  · exact point67Slice10
  · exact point67Slice11
  · exact point67Slice12
  · exact point67Slice13
  · exact point67Slice14
  · exact point67Slice15
  · exact point67Slice16
  · exact point67Slice17
  · exact point67Slice18
  · exact point67Slice19
  · exact point67Slice20
  · exact point67Slice21
  · exact point67Slice22
  · exact point67Slice23
  · exact point67Slice24
  · exact point67Slice25
  · exact point67Slice26
  · exact point67Slice27
  · exact point67Slice28

set_option maxHeartbeats 1600000 in
private theorem point68Slice0 : pointSliceCheck 1 2108 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice1 : pointSliceCheck 1 2108 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice2 : pointSliceCheck 1 2108 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice3 : pointSliceCheck 1 2108 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice4 : pointSliceCheck 1 2108 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice5 : pointSliceCheck 1 2108 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice6 : pointSliceCheck 1 2108 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice7 : pointSliceCheck 1 2108 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice8 : pointSliceCheck 1 2108 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice9 : pointSliceCheck 1 2108 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice10 : pointSliceCheck 1 2108 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice11 : pointSliceCheck 1 2108 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice12 : pointSliceCheck 1 2108 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice13 : pointSliceCheck 1 2108 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice14 : pointSliceCheck 1 2108 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice15 : pointSliceCheck 1 2108 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice16 : pointSliceCheck 1 2108 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice17 : pointSliceCheck 1 2108 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice18 : pointSliceCheck 1 2108 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice19 : pointSliceCheck 1 2108 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice20 : pointSliceCheck 1 2108 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice21 : pointSliceCheck 1 2108 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice22 : pointSliceCheck 1 2108 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice23 : pointSliceCheck 1 2108 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice24 : pointSliceCheck 1 2108 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice25 : pointSliceCheck 1 2108 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice26 : pointSliceCheck 1 2108 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice27 : pointSliceCheck 1 2108 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice28 : pointSliceCheck 1 2108 28 := by
  decide +kernel

/-- Original transition at residual index 68, certified on every point. -/
public theorem point68 : stepCheck 1 2108 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point68Slice0
  · exact point68Slice1
  · exact point68Slice2
  · exact point68Slice3
  · exact point68Slice4
  · exact point68Slice5
  · exact point68Slice6
  · exact point68Slice7
  · exact point68Slice8
  · exact point68Slice9
  · exact point68Slice10
  · exact point68Slice11
  · exact point68Slice12
  · exact point68Slice13
  · exact point68Slice14
  · exact point68Slice15
  · exact point68Slice16
  · exact point68Slice17
  · exact point68Slice18
  · exact point68Slice19
  · exact point68Slice20
  · exact point68Slice21
  · exact point68Slice22
  · exact point68Slice23
  · exact point68Slice24
  · exact point68Slice25
  · exact point68Slice26
  · exact point68Slice27
  · exact point68Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
