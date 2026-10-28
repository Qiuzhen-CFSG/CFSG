module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 93–94

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point93Slice0 : pointSliceCheck 0 2521 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice1 : pointSliceCheck 0 2521 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice2 : pointSliceCheck 0 2521 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice3 : pointSliceCheck 0 2521 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice4 : pointSliceCheck 0 2521 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice5 : pointSliceCheck 0 2521 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice6 : pointSliceCheck 0 2521 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice7 : pointSliceCheck 0 2521 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice8 : pointSliceCheck 0 2521 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice9 : pointSliceCheck 0 2521 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice10 : pointSliceCheck 0 2521 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice11 : pointSliceCheck 0 2521 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice12 : pointSliceCheck 0 2521 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice13 : pointSliceCheck 0 2521 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice14 : pointSliceCheck 0 2521 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice15 : pointSliceCheck 0 2521 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice16 : pointSliceCheck 0 2521 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice17 : pointSliceCheck 0 2521 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice18 : pointSliceCheck 0 2521 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice19 : pointSliceCheck 0 2521 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice20 : pointSliceCheck 0 2521 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice21 : pointSliceCheck 0 2521 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice22 : pointSliceCheck 0 2521 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice23 : pointSliceCheck 0 2521 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice24 : pointSliceCheck 0 2521 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice25 : pointSliceCheck 0 2521 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice26 : pointSliceCheck 0 2521 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice27 : pointSliceCheck 0 2521 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point93Slice28 : pointSliceCheck 0 2521 28 := by
  decide +kernel

/-- Original transition at residual index 93, certified on every point. -/
public theorem point93 : stepCheck 0 2521 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point93Slice0
  · exact point93Slice1
  · exact point93Slice2
  · exact point93Slice3
  · exact point93Slice4
  · exact point93Slice5
  · exact point93Slice6
  · exact point93Slice7
  · exact point93Slice8
  · exact point93Slice9
  · exact point93Slice10
  · exact point93Slice11
  · exact point93Slice12
  · exact point93Slice13
  · exact point93Slice14
  · exact point93Slice15
  · exact point93Slice16
  · exact point93Slice17
  · exact point93Slice18
  · exact point93Slice19
  · exact point93Slice20
  · exact point93Slice21
  · exact point93Slice22
  · exact point93Slice23
  · exact point93Slice24
  · exact point93Slice25
  · exact point93Slice26
  · exact point93Slice27
  · exact point93Slice28

set_option maxHeartbeats 1600000 in
private theorem point94Slice0 : pointSliceCheck 0 2522 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice1 : pointSliceCheck 0 2522 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice2 : pointSliceCheck 0 2522 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice3 : pointSliceCheck 0 2522 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice4 : pointSliceCheck 0 2522 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice5 : pointSliceCheck 0 2522 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice6 : pointSliceCheck 0 2522 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice7 : pointSliceCheck 0 2522 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice8 : pointSliceCheck 0 2522 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice9 : pointSliceCheck 0 2522 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice10 : pointSliceCheck 0 2522 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice11 : pointSliceCheck 0 2522 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice12 : pointSliceCheck 0 2522 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice13 : pointSliceCheck 0 2522 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice14 : pointSliceCheck 0 2522 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice15 : pointSliceCheck 0 2522 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice16 : pointSliceCheck 0 2522 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice17 : pointSliceCheck 0 2522 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice18 : pointSliceCheck 0 2522 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice19 : pointSliceCheck 0 2522 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice20 : pointSliceCheck 0 2522 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice21 : pointSliceCheck 0 2522 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice22 : pointSliceCheck 0 2522 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice23 : pointSliceCheck 0 2522 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice24 : pointSliceCheck 0 2522 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice25 : pointSliceCheck 0 2522 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice26 : pointSliceCheck 0 2522 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice27 : pointSliceCheck 0 2522 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point94Slice28 : pointSliceCheck 0 2522 28 := by
  decide +kernel

/-- Original transition at residual index 94, certified on every point. -/
public theorem point94 : stepCheck 0 2522 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point94Slice0
  · exact point94Slice1
  · exact point94Slice2
  · exact point94Slice3
  · exact point94Slice4
  · exact point94Slice5
  · exact point94Slice6
  · exact point94Slice7
  · exact point94Slice8
  · exact point94Slice9
  · exact point94Slice10
  · exact point94Slice11
  · exact point94Slice12
  · exact point94Slice13
  · exact point94Slice14
  · exact point94Slice15
  · exact point94Slice16
  · exact point94Slice17
  · exact point94Slice18
  · exact point94Slice19
  · exact point94Slice20
  · exact point94Slice21
  · exact point94Slice22
  · exact point94Slice23
  · exact point94Slice24
  · exact point94Slice25
  · exact point94Slice26
  · exact point94Slice27
  · exact point94Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
