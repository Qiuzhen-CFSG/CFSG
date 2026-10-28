module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 97–98

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point97Slice0 : pointSliceCheck 0 2529 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice1 : pointSliceCheck 0 2529 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice2 : pointSliceCheck 0 2529 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice3 : pointSliceCheck 0 2529 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice4 : pointSliceCheck 0 2529 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice5 : pointSliceCheck 0 2529 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice6 : pointSliceCheck 0 2529 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice7 : pointSliceCheck 0 2529 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice8 : pointSliceCheck 0 2529 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice9 : pointSliceCheck 0 2529 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice10 : pointSliceCheck 0 2529 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice11 : pointSliceCheck 0 2529 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice12 : pointSliceCheck 0 2529 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice13 : pointSliceCheck 0 2529 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice14 : pointSliceCheck 0 2529 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice15 : pointSliceCheck 0 2529 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice16 : pointSliceCheck 0 2529 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice17 : pointSliceCheck 0 2529 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice18 : pointSliceCheck 0 2529 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice19 : pointSliceCheck 0 2529 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice20 : pointSliceCheck 0 2529 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice21 : pointSliceCheck 0 2529 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice22 : pointSliceCheck 0 2529 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice23 : pointSliceCheck 0 2529 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice24 : pointSliceCheck 0 2529 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice25 : pointSliceCheck 0 2529 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice26 : pointSliceCheck 0 2529 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice27 : pointSliceCheck 0 2529 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point97Slice28 : pointSliceCheck 0 2529 28 := by
  decide +kernel

/-- Original transition at residual index 97, certified on every point. -/
public theorem point97 : stepCheck 0 2529 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point97Slice0
  · exact point97Slice1
  · exact point97Slice2
  · exact point97Slice3
  · exact point97Slice4
  · exact point97Slice5
  · exact point97Slice6
  · exact point97Slice7
  · exact point97Slice8
  · exact point97Slice9
  · exact point97Slice10
  · exact point97Slice11
  · exact point97Slice12
  · exact point97Slice13
  · exact point97Slice14
  · exact point97Slice15
  · exact point97Slice16
  · exact point97Slice17
  · exact point97Slice18
  · exact point97Slice19
  · exact point97Slice20
  · exact point97Slice21
  · exact point97Slice22
  · exact point97Slice23
  · exact point97Slice24
  · exact point97Slice25
  · exact point97Slice26
  · exact point97Slice27
  · exact point97Slice28

set_option maxHeartbeats 1600000 in
private theorem point98Slice0 : pointSliceCheck 0 2535 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice1 : pointSliceCheck 0 2535 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice2 : pointSliceCheck 0 2535 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice3 : pointSliceCheck 0 2535 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice4 : pointSliceCheck 0 2535 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice5 : pointSliceCheck 0 2535 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice6 : pointSliceCheck 0 2535 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice7 : pointSliceCheck 0 2535 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice8 : pointSliceCheck 0 2535 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice9 : pointSliceCheck 0 2535 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice10 : pointSliceCheck 0 2535 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice11 : pointSliceCheck 0 2535 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice12 : pointSliceCheck 0 2535 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice13 : pointSliceCheck 0 2535 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice14 : pointSliceCheck 0 2535 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice15 : pointSliceCheck 0 2535 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice16 : pointSliceCheck 0 2535 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice17 : pointSliceCheck 0 2535 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice18 : pointSliceCheck 0 2535 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice19 : pointSliceCheck 0 2535 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice20 : pointSliceCheck 0 2535 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice21 : pointSliceCheck 0 2535 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice22 : pointSliceCheck 0 2535 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice23 : pointSliceCheck 0 2535 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice24 : pointSliceCheck 0 2535 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice25 : pointSliceCheck 0 2535 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice26 : pointSliceCheck 0 2535 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice27 : pointSliceCheck 0 2535 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point98Slice28 : pointSliceCheck 0 2535 28 := by
  decide +kernel

/-- Original transition at residual index 98, certified on every point. -/
public theorem point98 : stepCheck 0 2535 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point98Slice0
  · exact point98Slice1
  · exact point98Slice2
  · exact point98Slice3
  · exact point98Slice4
  · exact point98Slice5
  · exact point98Slice6
  · exact point98Slice7
  · exact point98Slice8
  · exact point98Slice9
  · exact point98Slice10
  · exact point98Slice11
  · exact point98Slice12
  · exact point98Slice13
  · exact point98Slice14
  · exact point98Slice15
  · exact point98Slice16
  · exact point98Slice17
  · exact point98Slice18
  · exact point98Slice19
  · exact point98Slice20
  · exact point98Slice21
  · exact point98Slice22
  · exact point98Slice23
  · exact point98Slice24
  · exact point98Slice25
  · exact point98Slice26
  · exact point98Slice27
  · exact point98Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
