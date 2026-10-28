module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 69–70

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point69Slice0 : pointSliceCheck 1 2111 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice1 : pointSliceCheck 1 2111 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice2 : pointSliceCheck 1 2111 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice3 : pointSliceCheck 1 2111 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice4 : pointSliceCheck 1 2111 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice5 : pointSliceCheck 1 2111 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice6 : pointSliceCheck 1 2111 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice7 : pointSliceCheck 1 2111 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice8 : pointSliceCheck 1 2111 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice9 : pointSliceCheck 1 2111 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice10 : pointSliceCheck 1 2111 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice11 : pointSliceCheck 1 2111 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice12 : pointSliceCheck 1 2111 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice13 : pointSliceCheck 1 2111 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice14 : pointSliceCheck 1 2111 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice15 : pointSliceCheck 1 2111 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice16 : pointSliceCheck 1 2111 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice17 : pointSliceCheck 1 2111 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice18 : pointSliceCheck 1 2111 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice19 : pointSliceCheck 1 2111 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice20 : pointSliceCheck 1 2111 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice21 : pointSliceCheck 1 2111 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice22 : pointSliceCheck 1 2111 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice23 : pointSliceCheck 1 2111 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice24 : pointSliceCheck 1 2111 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice25 : pointSliceCheck 1 2111 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice26 : pointSliceCheck 1 2111 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice27 : pointSliceCheck 1 2111 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice28 : pointSliceCheck 1 2111 28 := by
  decide +kernel

/-- Original transition at residual index 69, certified on every point. -/
public theorem point69 : stepCheck 1 2111 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point69Slice0
  · exact point69Slice1
  · exact point69Slice2
  · exact point69Slice3
  · exact point69Slice4
  · exact point69Slice5
  · exact point69Slice6
  · exact point69Slice7
  · exact point69Slice8
  · exact point69Slice9
  · exact point69Slice10
  · exact point69Slice11
  · exact point69Slice12
  · exact point69Slice13
  · exact point69Slice14
  · exact point69Slice15
  · exact point69Slice16
  · exact point69Slice17
  · exact point69Slice18
  · exact point69Slice19
  · exact point69Slice20
  · exact point69Slice21
  · exact point69Slice22
  · exact point69Slice23
  · exact point69Slice24
  · exact point69Slice25
  · exact point69Slice26
  · exact point69Slice27
  · exact point69Slice28

set_option maxHeartbeats 1600000 in
private theorem point70Slice0 : pointSliceCheck 1 2114 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice1 : pointSliceCheck 1 2114 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice2 : pointSliceCheck 1 2114 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice3 : pointSliceCheck 1 2114 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice4 : pointSliceCheck 1 2114 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice5 : pointSliceCheck 1 2114 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice6 : pointSliceCheck 1 2114 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice7 : pointSliceCheck 1 2114 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice8 : pointSliceCheck 1 2114 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice9 : pointSliceCheck 1 2114 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice10 : pointSliceCheck 1 2114 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice11 : pointSliceCheck 1 2114 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice12 : pointSliceCheck 1 2114 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice13 : pointSliceCheck 1 2114 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice14 : pointSliceCheck 1 2114 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice15 : pointSliceCheck 1 2114 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice16 : pointSliceCheck 1 2114 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice17 : pointSliceCheck 1 2114 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice18 : pointSliceCheck 1 2114 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice19 : pointSliceCheck 1 2114 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice20 : pointSliceCheck 1 2114 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice21 : pointSliceCheck 1 2114 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice22 : pointSliceCheck 1 2114 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice23 : pointSliceCheck 1 2114 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice24 : pointSliceCheck 1 2114 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice25 : pointSliceCheck 1 2114 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice26 : pointSliceCheck 1 2114 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice27 : pointSliceCheck 1 2114 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point70Slice28 : pointSliceCheck 1 2114 28 := by
  decide +kernel

/-- Original transition at residual index 70, certified on every point. -/
public theorem point70 : stepCheck 1 2114 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point70Slice0
  · exact point70Slice1
  · exact point70Slice2
  · exact point70Slice3
  · exact point70Slice4
  · exact point70Slice5
  · exact point70Slice6
  · exact point70Slice7
  · exact point70Slice8
  · exact point70Slice9
  · exact point70Slice10
  · exact point70Slice11
  · exact point70Slice12
  · exact point70Slice13
  · exact point70Slice14
  · exact point70Slice15
  · exact point70Slice16
  · exact point70Slice17
  · exact point70Slice18
  · exact point70Slice19
  · exact point70Slice20
  · exact point70Slice21
  · exact point70Slice22
  · exact point70Slice23
  · exact point70Slice24
  · exact point70Slice25
  · exact point70Slice26
  · exact point70Slice27
  · exact point70Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
