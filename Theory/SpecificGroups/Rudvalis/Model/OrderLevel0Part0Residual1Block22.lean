module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 109–110

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point109Slice0 : pointSliceCheck 0 2675 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice1 : pointSliceCheck 0 2675 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice2 : pointSliceCheck 0 2675 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice3 : pointSliceCheck 0 2675 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice4 : pointSliceCheck 0 2675 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice5 : pointSliceCheck 0 2675 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice6 : pointSliceCheck 0 2675 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice7 : pointSliceCheck 0 2675 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice8 : pointSliceCheck 0 2675 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice9 : pointSliceCheck 0 2675 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice10 : pointSliceCheck 0 2675 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice11 : pointSliceCheck 0 2675 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice12 : pointSliceCheck 0 2675 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice13 : pointSliceCheck 0 2675 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice14 : pointSliceCheck 0 2675 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice15 : pointSliceCheck 0 2675 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice16 : pointSliceCheck 0 2675 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice17 : pointSliceCheck 0 2675 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice18 : pointSliceCheck 0 2675 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice19 : pointSliceCheck 0 2675 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice20 : pointSliceCheck 0 2675 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice21 : pointSliceCheck 0 2675 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice22 : pointSliceCheck 0 2675 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice23 : pointSliceCheck 0 2675 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice24 : pointSliceCheck 0 2675 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice25 : pointSliceCheck 0 2675 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice26 : pointSliceCheck 0 2675 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice27 : pointSliceCheck 0 2675 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point109Slice28 : pointSliceCheck 0 2675 28 := by
  decide +kernel

/-- Original transition at residual index 109, certified on every point. -/
public theorem point109 : stepCheck 0 2675 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point109Slice0
  · exact point109Slice1
  · exact point109Slice2
  · exact point109Slice3
  · exact point109Slice4
  · exact point109Slice5
  · exact point109Slice6
  · exact point109Slice7
  · exact point109Slice8
  · exact point109Slice9
  · exact point109Slice10
  · exact point109Slice11
  · exact point109Slice12
  · exact point109Slice13
  · exact point109Slice14
  · exact point109Slice15
  · exact point109Slice16
  · exact point109Slice17
  · exact point109Slice18
  · exact point109Slice19
  · exact point109Slice20
  · exact point109Slice21
  · exact point109Slice22
  · exact point109Slice23
  · exact point109Slice24
  · exact point109Slice25
  · exact point109Slice26
  · exact point109Slice27
  · exact point109Slice28

set_option maxHeartbeats 1600000 in
private theorem point110Slice0 : pointSliceCheck 1 2662 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice1 : pointSliceCheck 1 2662 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice2 : pointSliceCheck 1 2662 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice3 : pointSliceCheck 1 2662 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice4 : pointSliceCheck 1 2662 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice5 : pointSliceCheck 1 2662 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice6 : pointSliceCheck 1 2662 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice7 : pointSliceCheck 1 2662 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice8 : pointSliceCheck 1 2662 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice9 : pointSliceCheck 1 2662 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice10 : pointSliceCheck 1 2662 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice11 : pointSliceCheck 1 2662 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice12 : pointSliceCheck 1 2662 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice13 : pointSliceCheck 1 2662 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice14 : pointSliceCheck 1 2662 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice15 : pointSliceCheck 1 2662 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice16 : pointSliceCheck 1 2662 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice17 : pointSliceCheck 1 2662 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice18 : pointSliceCheck 1 2662 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice19 : pointSliceCheck 1 2662 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice20 : pointSliceCheck 1 2662 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice21 : pointSliceCheck 1 2662 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice22 : pointSliceCheck 1 2662 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice23 : pointSliceCheck 1 2662 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice24 : pointSliceCheck 1 2662 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice25 : pointSliceCheck 1 2662 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice26 : pointSliceCheck 1 2662 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice27 : pointSliceCheck 1 2662 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point110Slice28 : pointSliceCheck 1 2662 28 := by
  decide +kernel

/-- Original transition at residual index 110, certified on every point. -/
public theorem point110 : stepCheck 1 2662 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point110Slice0
  · exact point110Slice1
  · exact point110Slice2
  · exact point110Slice3
  · exact point110Slice4
  · exact point110Slice5
  · exact point110Slice6
  · exact point110Slice7
  · exact point110Slice8
  · exact point110Slice9
  · exact point110Slice10
  · exact point110Slice11
  · exact point110Slice12
  · exact point110Slice13
  · exact point110Slice14
  · exact point110Slice15
  · exact point110Slice16
  · exact point110Slice17
  · exact point110Slice18
  · exact point110Slice19
  · exact point110Slice20
  · exact point110Slice21
  · exact point110Slice22
  · exact point110Slice23
  · exact point110Slice24
  · exact point110Slice25
  · exact point110Slice26
  · exact point110Slice27
  · exact point110Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
