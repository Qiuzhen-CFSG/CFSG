module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 125–126

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point125Slice0 : pointSliceCheck 0 2943 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice1 : pointSliceCheck 0 2943 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice2 : pointSliceCheck 0 2943 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice3 : pointSliceCheck 0 2943 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice4 : pointSliceCheck 0 2943 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice5 : pointSliceCheck 0 2943 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice6 : pointSliceCheck 0 2943 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice7 : pointSliceCheck 0 2943 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice8 : pointSliceCheck 0 2943 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice9 : pointSliceCheck 0 2943 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice10 : pointSliceCheck 0 2943 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice11 : pointSliceCheck 0 2943 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice12 : pointSliceCheck 0 2943 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice13 : pointSliceCheck 0 2943 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice14 : pointSliceCheck 0 2943 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice15 : pointSliceCheck 0 2943 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice16 : pointSliceCheck 0 2943 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice17 : pointSliceCheck 0 2943 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice18 : pointSliceCheck 0 2943 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice19 : pointSliceCheck 0 2943 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice20 : pointSliceCheck 0 2943 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice21 : pointSliceCheck 0 2943 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice22 : pointSliceCheck 0 2943 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice23 : pointSliceCheck 0 2943 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice24 : pointSliceCheck 0 2943 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice25 : pointSliceCheck 0 2943 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice26 : pointSliceCheck 0 2943 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice27 : pointSliceCheck 0 2943 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125Slice28 : pointSliceCheck 0 2943 28 := by
  decide +kernel

/-- Original transition at residual index 125, certified on every point. -/
public theorem point125 : stepCheck 0 2943 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point125Slice0
  · exact point125Slice1
  · exact point125Slice2
  · exact point125Slice3
  · exact point125Slice4
  · exact point125Slice5
  · exact point125Slice6
  · exact point125Slice7
  · exact point125Slice8
  · exact point125Slice9
  · exact point125Slice10
  · exact point125Slice11
  · exact point125Slice12
  · exact point125Slice13
  · exact point125Slice14
  · exact point125Slice15
  · exact point125Slice16
  · exact point125Slice17
  · exact point125Slice18
  · exact point125Slice19
  · exact point125Slice20
  · exact point125Slice21
  · exact point125Slice22
  · exact point125Slice23
  · exact point125Slice24
  · exact point125Slice25
  · exact point125Slice26
  · exact point125Slice27
  · exact point125Slice28

set_option maxHeartbeats 1600000 in
private theorem point126Slice0 : pointSliceCheck 0 2945 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice1 : pointSliceCheck 0 2945 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice2 : pointSliceCheck 0 2945 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice3 : pointSliceCheck 0 2945 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice4 : pointSliceCheck 0 2945 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice5 : pointSliceCheck 0 2945 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice6 : pointSliceCheck 0 2945 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice7 : pointSliceCheck 0 2945 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice8 : pointSliceCheck 0 2945 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice9 : pointSliceCheck 0 2945 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice10 : pointSliceCheck 0 2945 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice11 : pointSliceCheck 0 2945 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice12 : pointSliceCheck 0 2945 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice13 : pointSliceCheck 0 2945 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice14 : pointSliceCheck 0 2945 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice15 : pointSliceCheck 0 2945 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice16 : pointSliceCheck 0 2945 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice17 : pointSliceCheck 0 2945 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice18 : pointSliceCheck 0 2945 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice19 : pointSliceCheck 0 2945 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice20 : pointSliceCheck 0 2945 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice21 : pointSliceCheck 0 2945 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice22 : pointSliceCheck 0 2945 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice23 : pointSliceCheck 0 2945 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice24 : pointSliceCheck 0 2945 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice25 : pointSliceCheck 0 2945 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice26 : pointSliceCheck 0 2945 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice27 : pointSliceCheck 0 2945 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126Slice28 : pointSliceCheck 0 2945 28 := by
  decide +kernel

/-- Original transition at residual index 126, certified on every point. -/
public theorem point126 : stepCheck 0 2945 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point126Slice0
  · exact point126Slice1
  · exact point126Slice2
  · exact point126Slice3
  · exact point126Slice4
  · exact point126Slice5
  · exact point126Slice6
  · exact point126Slice7
  · exact point126Slice8
  · exact point126Slice9
  · exact point126Slice10
  · exact point126Slice11
  · exact point126Slice12
  · exact point126Slice13
  · exact point126Slice14
  · exact point126Slice15
  · exact point126Slice16
  · exact point126Slice17
  · exact point126Slice18
  · exact point126Slice19
  · exact point126Slice20
  · exact point126Slice21
  · exact point126Slice22
  · exact point126Slice23
  · exact point126Slice24
  · exact point126Slice25
  · exact point126Slice26
  · exact point126Slice27
  · exact point126Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
