module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 129–129

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point129Slice0 : pointSliceCheck 0 2953 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice1 : pointSliceCheck 0 2953 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice2 : pointSliceCheck 0 2953 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice3 : pointSliceCheck 0 2953 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice4 : pointSliceCheck 0 2953 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice5 : pointSliceCheck 0 2953 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice6 : pointSliceCheck 0 2953 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice7 : pointSliceCheck 0 2953 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice8 : pointSliceCheck 0 2953 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice9 : pointSliceCheck 0 2953 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice10 : pointSliceCheck 0 2953 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice11 : pointSliceCheck 0 2953 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice12 : pointSliceCheck 0 2953 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice13 : pointSliceCheck 0 2953 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice14 : pointSliceCheck 0 2953 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice15 : pointSliceCheck 0 2953 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice16 : pointSliceCheck 0 2953 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice17 : pointSliceCheck 0 2953 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice18 : pointSliceCheck 0 2953 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice19 : pointSliceCheck 0 2953 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice20 : pointSliceCheck 0 2953 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice21 : pointSliceCheck 0 2953 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice22 : pointSliceCheck 0 2953 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice23 : pointSliceCheck 0 2953 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice24 : pointSliceCheck 0 2953 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice25 : pointSliceCheck 0 2953 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice26 : pointSliceCheck 0 2953 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice27 : pointSliceCheck 0 2953 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129Slice28 : pointSliceCheck 0 2953 28 := by
  decide +kernel

/-- Original transition at residual index 129, certified on every point. -/
public theorem point129 : stepCheck 0 2953 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point129Slice0
  · exact point129Slice1
  · exact point129Slice2
  · exact point129Slice3
  · exact point129Slice4
  · exact point129Slice5
  · exact point129Slice6
  · exact point129Slice7
  · exact point129Slice8
  · exact point129Slice9
  · exact point129Slice10
  · exact point129Slice11
  · exact point129Slice12
  · exact point129Slice13
  · exact point129Slice14
  · exact point129Slice15
  · exact point129Slice16
  · exact point129Slice17
  · exact point129Slice18
  · exact point129Slice19
  · exact point129Slice20
  · exact point129Slice21
  · exact point129Slice22
  · exact point129Slice23
  · exact point129Slice24
  · exact point129Slice25
  · exact point129Slice26
  · exact point129Slice27
  · exact point129Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
