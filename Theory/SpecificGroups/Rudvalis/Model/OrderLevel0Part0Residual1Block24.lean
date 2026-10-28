module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 113–114

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point113Slice0 : pointSliceCheck 1 2676 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice1 : pointSliceCheck 1 2676 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice2 : pointSliceCheck 1 2676 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice3 : pointSliceCheck 1 2676 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice4 : pointSliceCheck 1 2676 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice5 : pointSliceCheck 1 2676 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice6 : pointSliceCheck 1 2676 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice7 : pointSliceCheck 1 2676 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice8 : pointSliceCheck 1 2676 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice9 : pointSliceCheck 1 2676 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice10 : pointSliceCheck 1 2676 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice11 : pointSliceCheck 1 2676 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice12 : pointSliceCheck 1 2676 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice13 : pointSliceCheck 1 2676 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice14 : pointSliceCheck 1 2676 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice15 : pointSliceCheck 1 2676 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice16 : pointSliceCheck 1 2676 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice17 : pointSliceCheck 1 2676 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice18 : pointSliceCheck 1 2676 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice19 : pointSliceCheck 1 2676 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice20 : pointSliceCheck 1 2676 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice21 : pointSliceCheck 1 2676 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice22 : pointSliceCheck 1 2676 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice23 : pointSliceCheck 1 2676 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice24 : pointSliceCheck 1 2676 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice25 : pointSliceCheck 1 2676 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice26 : pointSliceCheck 1 2676 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice27 : pointSliceCheck 1 2676 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point113Slice28 : pointSliceCheck 1 2676 28 := by
  decide +kernel

/-- Original transition at residual index 113, certified on every point. -/
public theorem point113 : stepCheck 1 2676 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point113Slice0
  · exact point113Slice1
  · exact point113Slice2
  · exact point113Slice3
  · exact point113Slice4
  · exact point113Slice5
  · exact point113Slice6
  · exact point113Slice7
  · exact point113Slice8
  · exact point113Slice9
  · exact point113Slice10
  · exact point113Slice11
  · exact point113Slice12
  · exact point113Slice13
  · exact point113Slice14
  · exact point113Slice15
  · exact point113Slice16
  · exact point113Slice17
  · exact point113Slice18
  · exact point113Slice19
  · exact point113Slice20
  · exact point113Slice21
  · exact point113Slice22
  · exact point113Slice23
  · exact point113Slice24
  · exact point113Slice25
  · exact point113Slice26
  · exact point113Slice27
  · exact point113Slice28

set_option maxHeartbeats 1600000 in
private theorem point114Slice0 : pointSliceCheck 1 2678 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice1 : pointSliceCheck 1 2678 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice2 : pointSliceCheck 1 2678 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice3 : pointSliceCheck 1 2678 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice4 : pointSliceCheck 1 2678 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice5 : pointSliceCheck 1 2678 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice6 : pointSliceCheck 1 2678 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice7 : pointSliceCheck 1 2678 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice8 : pointSliceCheck 1 2678 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice9 : pointSliceCheck 1 2678 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice10 : pointSliceCheck 1 2678 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice11 : pointSliceCheck 1 2678 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice12 : pointSliceCheck 1 2678 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice13 : pointSliceCheck 1 2678 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice14 : pointSliceCheck 1 2678 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice15 : pointSliceCheck 1 2678 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice16 : pointSliceCheck 1 2678 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice17 : pointSliceCheck 1 2678 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice18 : pointSliceCheck 1 2678 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice19 : pointSliceCheck 1 2678 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice20 : pointSliceCheck 1 2678 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice21 : pointSliceCheck 1 2678 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice22 : pointSliceCheck 1 2678 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice23 : pointSliceCheck 1 2678 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice24 : pointSliceCheck 1 2678 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice25 : pointSliceCheck 1 2678 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice26 : pointSliceCheck 1 2678 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice27 : pointSliceCheck 1 2678 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114Slice28 : pointSliceCheck 1 2678 28 := by
  decide +kernel

/-- Original transition at residual index 114, certified on every point. -/
public theorem point114 : stepCheck 1 2678 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point114Slice0
  · exact point114Slice1
  · exact point114Slice2
  · exact point114Slice3
  · exact point114Slice4
  · exact point114Slice5
  · exact point114Slice6
  · exact point114Slice7
  · exact point114Slice8
  · exact point114Slice9
  · exact point114Slice10
  · exact point114Slice11
  · exact point114Slice12
  · exact point114Slice13
  · exact point114Slice14
  · exact point114Slice15
  · exact point114Slice16
  · exact point114Slice17
  · exact point114Slice18
  · exact point114Slice19
  · exact point114Slice20
  · exact point114Slice21
  · exact point114Slice22
  · exact point114Slice23
  · exact point114Slice24
  · exact point114Slice25
  · exact point114Slice26
  · exact point114Slice27
  · exact point114Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
