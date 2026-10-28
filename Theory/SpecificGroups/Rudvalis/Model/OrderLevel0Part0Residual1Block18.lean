module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 101–102

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point101Slice0 : pointSliceCheck 1 2529 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice1 : pointSliceCheck 1 2529 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice2 : pointSliceCheck 1 2529 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice3 : pointSliceCheck 1 2529 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice4 : pointSliceCheck 1 2529 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice5 : pointSliceCheck 1 2529 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice6 : pointSliceCheck 1 2529 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice7 : pointSliceCheck 1 2529 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice8 : pointSliceCheck 1 2529 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice9 : pointSliceCheck 1 2529 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice10 : pointSliceCheck 1 2529 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice11 : pointSliceCheck 1 2529 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice12 : pointSliceCheck 1 2529 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice13 : pointSliceCheck 1 2529 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice14 : pointSliceCheck 1 2529 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice15 : pointSliceCheck 1 2529 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice16 : pointSliceCheck 1 2529 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice17 : pointSliceCheck 1 2529 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice18 : pointSliceCheck 1 2529 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice19 : pointSliceCheck 1 2529 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice20 : pointSliceCheck 1 2529 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice21 : pointSliceCheck 1 2529 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice22 : pointSliceCheck 1 2529 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice23 : pointSliceCheck 1 2529 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice24 : pointSliceCheck 1 2529 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice25 : pointSliceCheck 1 2529 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice26 : pointSliceCheck 1 2529 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice27 : pointSliceCheck 1 2529 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point101Slice28 : pointSliceCheck 1 2529 28 := by
  decide +kernel

/-- Original transition at residual index 101, certified on every point. -/
public theorem point101 : stepCheck 1 2529 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point101Slice0
  · exact point101Slice1
  · exact point101Slice2
  · exact point101Slice3
  · exact point101Slice4
  · exact point101Slice5
  · exact point101Slice6
  · exact point101Slice7
  · exact point101Slice8
  · exact point101Slice9
  · exact point101Slice10
  · exact point101Slice11
  · exact point101Slice12
  · exact point101Slice13
  · exact point101Slice14
  · exact point101Slice15
  · exact point101Slice16
  · exact point101Slice17
  · exact point101Slice18
  · exact point101Slice19
  · exact point101Slice20
  · exact point101Slice21
  · exact point101Slice22
  · exact point101Slice23
  · exact point101Slice24
  · exact point101Slice25
  · exact point101Slice26
  · exact point101Slice27
  · exact point101Slice28

set_option maxHeartbeats 1600000 in
private theorem point102Slice0 : pointSliceCheck 1 2531 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice1 : pointSliceCheck 1 2531 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice2 : pointSliceCheck 1 2531 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice3 : pointSliceCheck 1 2531 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice4 : pointSliceCheck 1 2531 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice5 : pointSliceCheck 1 2531 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice6 : pointSliceCheck 1 2531 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice7 : pointSliceCheck 1 2531 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice8 : pointSliceCheck 1 2531 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice9 : pointSliceCheck 1 2531 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice10 : pointSliceCheck 1 2531 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice11 : pointSliceCheck 1 2531 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice12 : pointSliceCheck 1 2531 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice13 : pointSliceCheck 1 2531 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice14 : pointSliceCheck 1 2531 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice15 : pointSliceCheck 1 2531 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice16 : pointSliceCheck 1 2531 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice17 : pointSliceCheck 1 2531 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice18 : pointSliceCheck 1 2531 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice19 : pointSliceCheck 1 2531 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice20 : pointSliceCheck 1 2531 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice21 : pointSliceCheck 1 2531 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice22 : pointSliceCheck 1 2531 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice23 : pointSliceCheck 1 2531 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice24 : pointSliceCheck 1 2531 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice25 : pointSliceCheck 1 2531 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice26 : pointSliceCheck 1 2531 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice27 : pointSliceCheck 1 2531 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point102Slice28 : pointSliceCheck 1 2531 28 := by
  decide +kernel

/-- Original transition at residual index 102, certified on every point. -/
public theorem point102 : stepCheck 1 2531 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point102Slice0
  · exact point102Slice1
  · exact point102Slice2
  · exact point102Slice3
  · exact point102Slice4
  · exact point102Slice5
  · exact point102Slice6
  · exact point102Slice7
  · exact point102Slice8
  · exact point102Slice9
  · exact point102Slice10
  · exact point102Slice11
  · exact point102Slice12
  · exact point102Slice13
  · exact point102Slice14
  · exact point102Slice15
  · exact point102Slice16
  · exact point102Slice17
  · exact point102Slice18
  · exact point102Slice19
  · exact point102Slice20
  · exact point102Slice21
  · exact point102Slice22
  · exact point102Slice23
  · exact point102Slice24
  · exact point102Slice25
  · exact point102Slice26
  · exact point102Slice27
  · exact point102Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
