module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 103–104

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point103Slice0 : pointSliceCheck 0 2662 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice1 : pointSliceCheck 0 2662 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice2 : pointSliceCheck 0 2662 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice3 : pointSliceCheck 0 2662 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice4 : pointSliceCheck 0 2662 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice5 : pointSliceCheck 0 2662 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice6 : pointSliceCheck 0 2662 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice7 : pointSliceCheck 0 2662 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice8 : pointSliceCheck 0 2662 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice9 : pointSliceCheck 0 2662 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice10 : pointSliceCheck 0 2662 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice11 : pointSliceCheck 0 2662 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice12 : pointSliceCheck 0 2662 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice13 : pointSliceCheck 0 2662 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice14 : pointSliceCheck 0 2662 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice15 : pointSliceCheck 0 2662 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice16 : pointSliceCheck 0 2662 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice17 : pointSliceCheck 0 2662 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice18 : pointSliceCheck 0 2662 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice19 : pointSliceCheck 0 2662 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice20 : pointSliceCheck 0 2662 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice21 : pointSliceCheck 0 2662 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice22 : pointSliceCheck 0 2662 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice23 : pointSliceCheck 0 2662 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice24 : pointSliceCheck 0 2662 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice25 : pointSliceCheck 0 2662 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice26 : pointSliceCheck 0 2662 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice27 : pointSliceCheck 0 2662 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point103Slice28 : pointSliceCheck 0 2662 28 := by
  decide +kernel

/-- Original transition at residual index 103, certified on every point. -/
public theorem point103 : stepCheck 0 2662 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point103Slice0
  · exact point103Slice1
  · exact point103Slice2
  · exact point103Slice3
  · exact point103Slice4
  · exact point103Slice5
  · exact point103Slice6
  · exact point103Slice7
  · exact point103Slice8
  · exact point103Slice9
  · exact point103Slice10
  · exact point103Slice11
  · exact point103Slice12
  · exact point103Slice13
  · exact point103Slice14
  · exact point103Slice15
  · exact point103Slice16
  · exact point103Slice17
  · exact point103Slice18
  · exact point103Slice19
  · exact point103Slice20
  · exact point103Slice21
  · exact point103Slice22
  · exact point103Slice23
  · exact point103Slice24
  · exact point103Slice25
  · exact point103Slice26
  · exact point103Slice27
  · exact point103Slice28

set_option maxHeartbeats 1600000 in
private theorem point104Slice0 : pointSliceCheck 0 2663 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice1 : pointSliceCheck 0 2663 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice2 : pointSliceCheck 0 2663 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice3 : pointSliceCheck 0 2663 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice4 : pointSliceCheck 0 2663 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice5 : pointSliceCheck 0 2663 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice6 : pointSliceCheck 0 2663 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice7 : pointSliceCheck 0 2663 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice8 : pointSliceCheck 0 2663 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice9 : pointSliceCheck 0 2663 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice10 : pointSliceCheck 0 2663 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice11 : pointSliceCheck 0 2663 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice12 : pointSliceCheck 0 2663 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice13 : pointSliceCheck 0 2663 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice14 : pointSliceCheck 0 2663 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice15 : pointSliceCheck 0 2663 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice16 : pointSliceCheck 0 2663 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice17 : pointSliceCheck 0 2663 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice18 : pointSliceCheck 0 2663 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice19 : pointSliceCheck 0 2663 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice20 : pointSliceCheck 0 2663 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice21 : pointSliceCheck 0 2663 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice22 : pointSliceCheck 0 2663 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice23 : pointSliceCheck 0 2663 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice24 : pointSliceCheck 0 2663 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice25 : pointSliceCheck 0 2663 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice26 : pointSliceCheck 0 2663 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice27 : pointSliceCheck 0 2663 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point104Slice28 : pointSliceCheck 0 2663 28 := by
  decide +kernel

/-- Original transition at residual index 104, certified on every point. -/
public theorem point104 : stepCheck 0 2663 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point104Slice0
  · exact point104Slice1
  · exact point104Slice2
  · exact point104Slice3
  · exact point104Slice4
  · exact point104Slice5
  · exact point104Slice6
  · exact point104Slice7
  · exact point104Slice8
  · exact point104Slice9
  · exact point104Slice10
  · exact point104Slice11
  · exact point104Slice12
  · exact point104Slice13
  · exact point104Slice14
  · exact point104Slice15
  · exact point104Slice16
  · exact point104Slice17
  · exact point104Slice18
  · exact point104Slice19
  · exact point104Slice20
  · exact point104Slice21
  · exact point104Slice22
  · exact point104Slice23
  · exact point104Slice24
  · exact point104Slice25
  · exact point104Slice26
  · exact point104Slice27
  · exact point104Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
