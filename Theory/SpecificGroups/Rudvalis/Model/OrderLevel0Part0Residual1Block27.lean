module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 119–120

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point119Slice0 : pointSliceCheck 0 2816 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice1 : pointSliceCheck 0 2816 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice2 : pointSliceCheck 0 2816 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice3 : pointSliceCheck 0 2816 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice4 : pointSliceCheck 0 2816 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice5 : pointSliceCheck 0 2816 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice6 : pointSliceCheck 0 2816 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice7 : pointSliceCheck 0 2816 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice8 : pointSliceCheck 0 2816 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice9 : pointSliceCheck 0 2816 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice10 : pointSliceCheck 0 2816 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice11 : pointSliceCheck 0 2816 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice12 : pointSliceCheck 0 2816 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice13 : pointSliceCheck 0 2816 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice14 : pointSliceCheck 0 2816 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice15 : pointSliceCheck 0 2816 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice16 : pointSliceCheck 0 2816 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice17 : pointSliceCheck 0 2816 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice18 : pointSliceCheck 0 2816 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice19 : pointSliceCheck 0 2816 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice20 : pointSliceCheck 0 2816 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice21 : pointSliceCheck 0 2816 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice22 : pointSliceCheck 0 2816 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice23 : pointSliceCheck 0 2816 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice24 : pointSliceCheck 0 2816 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice25 : pointSliceCheck 0 2816 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice26 : pointSliceCheck 0 2816 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice27 : pointSliceCheck 0 2816 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119Slice28 : pointSliceCheck 0 2816 28 := by
  decide +kernel

/-- Original transition at residual index 119, certified on every point. -/
public theorem point119 : stepCheck 0 2816 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point119Slice0
  · exact point119Slice1
  · exact point119Slice2
  · exact point119Slice3
  · exact point119Slice4
  · exact point119Slice5
  · exact point119Slice6
  · exact point119Slice7
  · exact point119Slice8
  · exact point119Slice9
  · exact point119Slice10
  · exact point119Slice11
  · exact point119Slice12
  · exact point119Slice13
  · exact point119Slice14
  · exact point119Slice15
  · exact point119Slice16
  · exact point119Slice17
  · exact point119Slice18
  · exact point119Slice19
  · exact point119Slice20
  · exact point119Slice21
  · exact point119Slice22
  · exact point119Slice23
  · exact point119Slice24
  · exact point119Slice25
  · exact point119Slice26
  · exact point119Slice27
  · exact point119Slice28

set_option maxHeartbeats 1600000 in
private theorem point120Slice0 : pointSliceCheck 0 2819 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice1 : pointSliceCheck 0 2819 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice2 : pointSliceCheck 0 2819 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice3 : pointSliceCheck 0 2819 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice4 : pointSliceCheck 0 2819 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice5 : pointSliceCheck 0 2819 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice6 : pointSliceCheck 0 2819 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice7 : pointSliceCheck 0 2819 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice8 : pointSliceCheck 0 2819 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice9 : pointSliceCheck 0 2819 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice10 : pointSliceCheck 0 2819 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice11 : pointSliceCheck 0 2819 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice12 : pointSliceCheck 0 2819 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice13 : pointSliceCheck 0 2819 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice14 : pointSliceCheck 0 2819 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice15 : pointSliceCheck 0 2819 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice16 : pointSliceCheck 0 2819 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice17 : pointSliceCheck 0 2819 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice18 : pointSliceCheck 0 2819 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice19 : pointSliceCheck 0 2819 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice20 : pointSliceCheck 0 2819 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice21 : pointSliceCheck 0 2819 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice22 : pointSliceCheck 0 2819 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice23 : pointSliceCheck 0 2819 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice24 : pointSliceCheck 0 2819 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice25 : pointSliceCheck 0 2819 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice26 : pointSliceCheck 0 2819 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice27 : pointSliceCheck 0 2819 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120Slice28 : pointSliceCheck 0 2819 28 := by
  decide +kernel

/-- Original transition at residual index 120, certified on every point. -/
public theorem point120 : stepCheck 0 2819 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point120Slice0
  · exact point120Slice1
  · exact point120Slice2
  · exact point120Slice3
  · exact point120Slice4
  · exact point120Slice5
  · exact point120Slice6
  · exact point120Slice7
  · exact point120Slice8
  · exact point120Slice9
  · exact point120Slice10
  · exact point120Slice11
  · exact point120Slice12
  · exact point120Slice13
  · exact point120Slice14
  · exact point120Slice15
  · exact point120Slice16
  · exact point120Slice17
  · exact point120Slice18
  · exact point120Slice19
  · exact point120Slice20
  · exact point120Slice21
  · exact point120Slice22
  · exact point120Slice23
  · exact point120Slice24
  · exact point120Slice25
  · exact point120Slice26
  · exact point120Slice27
  · exact point120Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
