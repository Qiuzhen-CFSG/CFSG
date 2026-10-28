module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 85–86

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point85Slice0 : pointSliceCheck 0 2399 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice1 : pointSliceCheck 0 2399 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice2 : pointSliceCheck 0 2399 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice3 : pointSliceCheck 0 2399 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice4 : pointSliceCheck 0 2399 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice5 : pointSliceCheck 0 2399 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice6 : pointSliceCheck 0 2399 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice7 : pointSliceCheck 0 2399 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice8 : pointSliceCheck 0 2399 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice9 : pointSliceCheck 0 2399 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice10 : pointSliceCheck 0 2399 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice11 : pointSliceCheck 0 2399 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice12 : pointSliceCheck 0 2399 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice13 : pointSliceCheck 0 2399 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice14 : pointSliceCheck 0 2399 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice15 : pointSliceCheck 0 2399 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice16 : pointSliceCheck 0 2399 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice17 : pointSliceCheck 0 2399 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice18 : pointSliceCheck 0 2399 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice19 : pointSliceCheck 0 2399 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice20 : pointSliceCheck 0 2399 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice21 : pointSliceCheck 0 2399 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice22 : pointSliceCheck 0 2399 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice23 : pointSliceCheck 0 2399 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice24 : pointSliceCheck 0 2399 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice25 : pointSliceCheck 0 2399 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice26 : pointSliceCheck 0 2399 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice27 : pointSliceCheck 0 2399 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point85Slice28 : pointSliceCheck 0 2399 28 := by
  decide +kernel

/-- Original transition at residual index 85, certified on every point. -/
public theorem point85 : stepCheck 0 2399 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point85Slice0
  · exact point85Slice1
  · exact point85Slice2
  · exact point85Slice3
  · exact point85Slice4
  · exact point85Slice5
  · exact point85Slice6
  · exact point85Slice7
  · exact point85Slice8
  · exact point85Slice9
  · exact point85Slice10
  · exact point85Slice11
  · exact point85Slice12
  · exact point85Slice13
  · exact point85Slice14
  · exact point85Slice15
  · exact point85Slice16
  · exact point85Slice17
  · exact point85Slice18
  · exact point85Slice19
  · exact point85Slice20
  · exact point85Slice21
  · exact point85Slice22
  · exact point85Slice23
  · exact point85Slice24
  · exact point85Slice25
  · exact point85Slice26
  · exact point85Slice27
  · exact point85Slice28

set_option maxHeartbeats 1600000 in
private theorem point86Slice0 : pointSliceCheck 1 2382 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice1 : pointSliceCheck 1 2382 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice2 : pointSliceCheck 1 2382 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice3 : pointSliceCheck 1 2382 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice4 : pointSliceCheck 1 2382 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice5 : pointSliceCheck 1 2382 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice6 : pointSliceCheck 1 2382 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice7 : pointSliceCheck 1 2382 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice8 : pointSliceCheck 1 2382 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice9 : pointSliceCheck 1 2382 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice10 : pointSliceCheck 1 2382 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice11 : pointSliceCheck 1 2382 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice12 : pointSliceCheck 1 2382 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice13 : pointSliceCheck 1 2382 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice14 : pointSliceCheck 1 2382 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice15 : pointSliceCheck 1 2382 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice16 : pointSliceCheck 1 2382 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice17 : pointSliceCheck 1 2382 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice18 : pointSliceCheck 1 2382 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice19 : pointSliceCheck 1 2382 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice20 : pointSliceCheck 1 2382 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice21 : pointSliceCheck 1 2382 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice22 : pointSliceCheck 1 2382 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice23 : pointSliceCheck 1 2382 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice24 : pointSliceCheck 1 2382 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice25 : pointSliceCheck 1 2382 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice26 : pointSliceCheck 1 2382 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice27 : pointSliceCheck 1 2382 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point86Slice28 : pointSliceCheck 1 2382 28 := by
  decide +kernel

/-- Original transition at residual index 86, certified on every point. -/
public theorem point86 : stepCheck 1 2382 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point86Slice0
  · exact point86Slice1
  · exact point86Slice2
  · exact point86Slice3
  · exact point86Slice4
  · exact point86Slice5
  · exact point86Slice6
  · exact point86Slice7
  · exact point86Slice8
  · exact point86Slice9
  · exact point86Slice10
  · exact point86Slice11
  · exact point86Slice12
  · exact point86Slice13
  · exact point86Slice14
  · exact point86Slice15
  · exact point86Slice16
  · exact point86Slice17
  · exact point86Slice18
  · exact point86Slice19
  · exact point86Slice20
  · exact point86Slice21
  · exact point86Slice22
  · exact point86Slice23
  · exact point86Slice24
  · exact point86Slice25
  · exact point86Slice26
  · exact point86Slice27
  · exact point86Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
