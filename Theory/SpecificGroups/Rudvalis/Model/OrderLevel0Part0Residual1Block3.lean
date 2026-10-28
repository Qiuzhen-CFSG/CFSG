module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 71–72

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point71Slice0 : pointSliceCheck 1 2118 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice1 : pointSliceCheck 1 2118 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice2 : pointSliceCheck 1 2118 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice3 : pointSliceCheck 1 2118 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice4 : pointSliceCheck 1 2118 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice5 : pointSliceCheck 1 2118 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice6 : pointSliceCheck 1 2118 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice7 : pointSliceCheck 1 2118 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice8 : pointSliceCheck 1 2118 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice9 : pointSliceCheck 1 2118 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice10 : pointSliceCheck 1 2118 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice11 : pointSliceCheck 1 2118 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice12 : pointSliceCheck 1 2118 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice13 : pointSliceCheck 1 2118 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice14 : pointSliceCheck 1 2118 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice15 : pointSliceCheck 1 2118 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice16 : pointSliceCheck 1 2118 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice17 : pointSliceCheck 1 2118 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice18 : pointSliceCheck 1 2118 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice19 : pointSliceCheck 1 2118 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice20 : pointSliceCheck 1 2118 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice21 : pointSliceCheck 1 2118 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice22 : pointSliceCheck 1 2118 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice23 : pointSliceCheck 1 2118 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice24 : pointSliceCheck 1 2118 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice25 : pointSliceCheck 1 2118 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice26 : pointSliceCheck 1 2118 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice27 : pointSliceCheck 1 2118 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point71Slice28 : pointSliceCheck 1 2118 28 := by
  decide +kernel

/-- Original transition at residual index 71, certified on every point. -/
public theorem point71 : stepCheck 1 2118 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point71Slice0
  · exact point71Slice1
  · exact point71Slice2
  · exact point71Slice3
  · exact point71Slice4
  · exact point71Slice5
  · exact point71Slice6
  · exact point71Slice7
  · exact point71Slice8
  · exact point71Slice9
  · exact point71Slice10
  · exact point71Slice11
  · exact point71Slice12
  · exact point71Slice13
  · exact point71Slice14
  · exact point71Slice15
  · exact point71Slice16
  · exact point71Slice17
  · exact point71Slice18
  · exact point71Slice19
  · exact point71Slice20
  · exact point71Slice21
  · exact point71Slice22
  · exact point71Slice23
  · exact point71Slice24
  · exact point71Slice25
  · exact point71Slice26
  · exact point71Slice27
  · exact point71Slice28

set_option maxHeartbeats 1600000 in
private theorem point72Slice0 : pointSliceCheck 0 2245 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice1 : pointSliceCheck 0 2245 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice2 : pointSliceCheck 0 2245 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice3 : pointSliceCheck 0 2245 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice4 : pointSliceCheck 0 2245 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice5 : pointSliceCheck 0 2245 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice6 : pointSliceCheck 0 2245 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice7 : pointSliceCheck 0 2245 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice8 : pointSliceCheck 0 2245 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice9 : pointSliceCheck 0 2245 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice10 : pointSliceCheck 0 2245 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice11 : pointSliceCheck 0 2245 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice12 : pointSliceCheck 0 2245 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice13 : pointSliceCheck 0 2245 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice14 : pointSliceCheck 0 2245 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice15 : pointSliceCheck 0 2245 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice16 : pointSliceCheck 0 2245 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice17 : pointSliceCheck 0 2245 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice18 : pointSliceCheck 0 2245 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice19 : pointSliceCheck 0 2245 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice20 : pointSliceCheck 0 2245 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice21 : pointSliceCheck 0 2245 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice22 : pointSliceCheck 0 2245 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice23 : pointSliceCheck 0 2245 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice24 : pointSliceCheck 0 2245 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice25 : pointSliceCheck 0 2245 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice26 : pointSliceCheck 0 2245 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice27 : pointSliceCheck 0 2245 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point72Slice28 : pointSliceCheck 0 2245 28 := by
  decide +kernel

/-- Original transition at residual index 72, certified on every point. -/
public theorem point72 : stepCheck 0 2245 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point72Slice0
  · exact point72Slice1
  · exact point72Slice2
  · exact point72Slice3
  · exact point72Slice4
  · exact point72Slice5
  · exact point72Slice6
  · exact point72Slice7
  · exact point72Slice8
  · exact point72Slice9
  · exact point72Slice10
  · exact point72Slice11
  · exact point72Slice12
  · exact point72Slice13
  · exact point72Slice14
  · exact point72Slice15
  · exact point72Slice16
  · exact point72Slice17
  · exact point72Slice18
  · exact point72Slice19
  · exact point72Slice20
  · exact point72Slice21
  · exact point72Slice22
  · exact point72Slice23
  · exact point72Slice24
  · exact point72Slice25
  · exact point72Slice26
  · exact point72Slice27
  · exact point72Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
