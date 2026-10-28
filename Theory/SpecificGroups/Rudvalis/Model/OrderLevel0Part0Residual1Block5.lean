module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 75–76

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point75Slice0 : pointSliceCheck 0 2253 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice1 : pointSliceCheck 0 2253 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice2 : pointSliceCheck 0 2253 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice3 : pointSliceCheck 0 2253 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice4 : pointSliceCheck 0 2253 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice5 : pointSliceCheck 0 2253 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice6 : pointSliceCheck 0 2253 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice7 : pointSliceCheck 0 2253 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice8 : pointSliceCheck 0 2253 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice9 : pointSliceCheck 0 2253 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice10 : pointSliceCheck 0 2253 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice11 : pointSliceCheck 0 2253 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice12 : pointSliceCheck 0 2253 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice13 : pointSliceCheck 0 2253 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice14 : pointSliceCheck 0 2253 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice15 : pointSliceCheck 0 2253 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice16 : pointSliceCheck 0 2253 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice17 : pointSliceCheck 0 2253 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice18 : pointSliceCheck 0 2253 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice19 : pointSliceCheck 0 2253 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice20 : pointSliceCheck 0 2253 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice21 : pointSliceCheck 0 2253 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice22 : pointSliceCheck 0 2253 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice23 : pointSliceCheck 0 2253 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice24 : pointSliceCheck 0 2253 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice25 : pointSliceCheck 0 2253 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice26 : pointSliceCheck 0 2253 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice27 : pointSliceCheck 0 2253 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point75Slice28 : pointSliceCheck 0 2253 28 := by
  decide +kernel

/-- Original transition at residual index 75, certified on every point. -/
public theorem point75 : stepCheck 0 2253 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point75Slice0
  · exact point75Slice1
  · exact point75Slice2
  · exact point75Slice3
  · exact point75Slice4
  · exact point75Slice5
  · exact point75Slice6
  · exact point75Slice7
  · exact point75Slice8
  · exact point75Slice9
  · exact point75Slice10
  · exact point75Slice11
  · exact point75Slice12
  · exact point75Slice13
  · exact point75Slice14
  · exact point75Slice15
  · exact point75Slice16
  · exact point75Slice17
  · exact point75Slice18
  · exact point75Slice19
  · exact point75Slice20
  · exact point75Slice21
  · exact point75Slice22
  · exact point75Slice23
  · exact point75Slice24
  · exact point75Slice25
  · exact point75Slice26
  · exact point75Slice27
  · exact point75Slice28

set_option maxHeartbeats 1600000 in
private theorem point76Slice0 : pointSliceCheck 0 2255 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice1 : pointSliceCheck 0 2255 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice2 : pointSliceCheck 0 2255 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice3 : pointSliceCheck 0 2255 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice4 : pointSliceCheck 0 2255 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice5 : pointSliceCheck 0 2255 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice6 : pointSliceCheck 0 2255 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice7 : pointSliceCheck 0 2255 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice8 : pointSliceCheck 0 2255 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice9 : pointSliceCheck 0 2255 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice10 : pointSliceCheck 0 2255 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice11 : pointSliceCheck 0 2255 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice12 : pointSliceCheck 0 2255 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice13 : pointSliceCheck 0 2255 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice14 : pointSliceCheck 0 2255 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice15 : pointSliceCheck 0 2255 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice16 : pointSliceCheck 0 2255 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice17 : pointSliceCheck 0 2255 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice18 : pointSliceCheck 0 2255 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice19 : pointSliceCheck 0 2255 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice20 : pointSliceCheck 0 2255 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice21 : pointSliceCheck 0 2255 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice22 : pointSliceCheck 0 2255 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice23 : pointSliceCheck 0 2255 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice24 : pointSliceCheck 0 2255 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice25 : pointSliceCheck 0 2255 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice26 : pointSliceCheck 0 2255 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice27 : pointSliceCheck 0 2255 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point76Slice28 : pointSliceCheck 0 2255 28 := by
  decide +kernel

/-- Original transition at residual index 76, certified on every point. -/
public theorem point76 : stepCheck 0 2255 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point76Slice0
  · exact point76Slice1
  · exact point76Slice2
  · exact point76Slice3
  · exact point76Slice4
  · exact point76Slice5
  · exact point76Slice6
  · exact point76Slice7
  · exact point76Slice8
  · exact point76Slice9
  · exact point76Slice10
  · exact point76Slice11
  · exact point76Slice12
  · exact point76Slice13
  · exact point76Slice14
  · exact point76Slice15
  · exact point76Slice16
  · exact point76Slice17
  · exact point76Slice18
  · exact point76Slice19
  · exact point76Slice20
  · exact point76Slice21
  · exact point76Slice22
  · exact point76Slice23
  · exact point76Slice24
  · exact point76Slice25
  · exact point76Slice26
  · exact point76Slice27
  · exact point76Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
