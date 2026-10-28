module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 89–90

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point89Slice0 : pointSliceCheck 1 2395 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice1 : pointSliceCheck 1 2395 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice2 : pointSliceCheck 1 2395 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice3 : pointSliceCheck 1 2395 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice4 : pointSliceCheck 1 2395 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice5 : pointSliceCheck 1 2395 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice6 : pointSliceCheck 1 2395 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice7 : pointSliceCheck 1 2395 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice8 : pointSliceCheck 1 2395 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice9 : pointSliceCheck 1 2395 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice10 : pointSliceCheck 1 2395 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice11 : pointSliceCheck 1 2395 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice12 : pointSliceCheck 1 2395 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice13 : pointSliceCheck 1 2395 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice14 : pointSliceCheck 1 2395 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice15 : pointSliceCheck 1 2395 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice16 : pointSliceCheck 1 2395 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice17 : pointSliceCheck 1 2395 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice18 : pointSliceCheck 1 2395 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice19 : pointSliceCheck 1 2395 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice20 : pointSliceCheck 1 2395 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice21 : pointSliceCheck 1 2395 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice22 : pointSliceCheck 1 2395 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice23 : pointSliceCheck 1 2395 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice24 : pointSliceCheck 1 2395 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice25 : pointSliceCheck 1 2395 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice26 : pointSliceCheck 1 2395 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice27 : pointSliceCheck 1 2395 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point89Slice28 : pointSliceCheck 1 2395 28 := by
  decide +kernel

/-- Original transition at residual index 89, certified on every point. -/
public theorem point89 : stepCheck 1 2395 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point89Slice0
  · exact point89Slice1
  · exact point89Slice2
  · exact point89Slice3
  · exact point89Slice4
  · exact point89Slice5
  · exact point89Slice6
  · exact point89Slice7
  · exact point89Slice8
  · exact point89Slice9
  · exact point89Slice10
  · exact point89Slice11
  · exact point89Slice12
  · exact point89Slice13
  · exact point89Slice14
  · exact point89Slice15
  · exact point89Slice16
  · exact point89Slice17
  · exact point89Slice18
  · exact point89Slice19
  · exact point89Slice20
  · exact point89Slice21
  · exact point89Slice22
  · exact point89Slice23
  · exact point89Slice24
  · exact point89Slice25
  · exact point89Slice26
  · exact point89Slice27
  · exact point89Slice28

set_option maxHeartbeats 1600000 in
private theorem point90Slice0 : pointSliceCheck 1 2396 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice1 : pointSliceCheck 1 2396 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice2 : pointSliceCheck 1 2396 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice3 : pointSliceCheck 1 2396 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice4 : pointSliceCheck 1 2396 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice5 : pointSliceCheck 1 2396 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice6 : pointSliceCheck 1 2396 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice7 : pointSliceCheck 1 2396 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice8 : pointSliceCheck 1 2396 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice9 : pointSliceCheck 1 2396 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice10 : pointSliceCheck 1 2396 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice11 : pointSliceCheck 1 2396 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice12 : pointSliceCheck 1 2396 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice13 : pointSliceCheck 1 2396 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice14 : pointSliceCheck 1 2396 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice15 : pointSliceCheck 1 2396 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice16 : pointSliceCheck 1 2396 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice17 : pointSliceCheck 1 2396 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice18 : pointSliceCheck 1 2396 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice19 : pointSliceCheck 1 2396 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice20 : pointSliceCheck 1 2396 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice21 : pointSliceCheck 1 2396 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice22 : pointSliceCheck 1 2396 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice23 : pointSliceCheck 1 2396 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice24 : pointSliceCheck 1 2396 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice25 : pointSliceCheck 1 2396 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice26 : pointSliceCheck 1 2396 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice27 : pointSliceCheck 1 2396 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point90Slice28 : pointSliceCheck 1 2396 28 := by
  decide +kernel

/-- Original transition at residual index 90, certified on every point. -/
public theorem point90 : stepCheck 1 2396 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point90Slice0
  · exact point90Slice1
  · exact point90Slice2
  · exact point90Slice3
  · exact point90Slice4
  · exact point90Slice5
  · exact point90Slice6
  · exact point90Slice7
  · exact point90Slice8
  · exact point90Slice9
  · exact point90Slice10
  · exact point90Slice11
  · exact point90Slice12
  · exact point90Slice13
  · exact point90Slice14
  · exact point90Slice15
  · exact point90Slice16
  · exact point90Slice17
  · exact point90Slice18
  · exact point90Slice19
  · exact point90Slice20
  · exact point90Slice21
  · exact point90Slice22
  · exact point90Slice23
  · exact point90Slice24
  · exact point90Slice25
  · exact point90Slice26
  · exact point90Slice27
  · exact point90Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
