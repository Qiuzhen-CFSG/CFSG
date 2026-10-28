module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 73–74

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point73Slice0 : pointSliceCheck 0 2246 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice1 : pointSliceCheck 0 2246 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice2 : pointSliceCheck 0 2246 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice3 : pointSliceCheck 0 2246 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice4 : pointSliceCheck 0 2246 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice5 : pointSliceCheck 0 2246 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice6 : pointSliceCheck 0 2246 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice7 : pointSliceCheck 0 2246 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice8 : pointSliceCheck 0 2246 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice9 : pointSliceCheck 0 2246 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice10 : pointSliceCheck 0 2246 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice11 : pointSliceCheck 0 2246 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice12 : pointSliceCheck 0 2246 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice13 : pointSliceCheck 0 2246 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice14 : pointSliceCheck 0 2246 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice15 : pointSliceCheck 0 2246 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice16 : pointSliceCheck 0 2246 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice17 : pointSliceCheck 0 2246 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice18 : pointSliceCheck 0 2246 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice19 : pointSliceCheck 0 2246 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice20 : pointSliceCheck 0 2246 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice21 : pointSliceCheck 0 2246 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice22 : pointSliceCheck 0 2246 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice23 : pointSliceCheck 0 2246 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice24 : pointSliceCheck 0 2246 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice25 : pointSliceCheck 0 2246 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice26 : pointSliceCheck 0 2246 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice27 : pointSliceCheck 0 2246 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point73Slice28 : pointSliceCheck 0 2246 28 := by
  decide +kernel

/-- Original transition at residual index 73, certified on every point. -/
public theorem point73 : stepCheck 0 2246 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point73Slice0
  · exact point73Slice1
  · exact point73Slice2
  · exact point73Slice3
  · exact point73Slice4
  · exact point73Slice5
  · exact point73Slice6
  · exact point73Slice7
  · exact point73Slice8
  · exact point73Slice9
  · exact point73Slice10
  · exact point73Slice11
  · exact point73Slice12
  · exact point73Slice13
  · exact point73Slice14
  · exact point73Slice15
  · exact point73Slice16
  · exact point73Slice17
  · exact point73Slice18
  · exact point73Slice19
  · exact point73Slice20
  · exact point73Slice21
  · exact point73Slice22
  · exact point73Slice23
  · exact point73Slice24
  · exact point73Slice25
  · exact point73Slice26
  · exact point73Slice27
  · exact point73Slice28

set_option maxHeartbeats 1600000 in
private theorem point74Slice0 : pointSliceCheck 0 2248 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice1 : pointSliceCheck 0 2248 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice2 : pointSliceCheck 0 2248 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice3 : pointSliceCheck 0 2248 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice4 : pointSliceCheck 0 2248 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice5 : pointSliceCheck 0 2248 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice6 : pointSliceCheck 0 2248 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice7 : pointSliceCheck 0 2248 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice8 : pointSliceCheck 0 2248 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice9 : pointSliceCheck 0 2248 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice10 : pointSliceCheck 0 2248 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice11 : pointSliceCheck 0 2248 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice12 : pointSliceCheck 0 2248 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice13 : pointSliceCheck 0 2248 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice14 : pointSliceCheck 0 2248 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice15 : pointSliceCheck 0 2248 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice16 : pointSliceCheck 0 2248 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice17 : pointSliceCheck 0 2248 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice18 : pointSliceCheck 0 2248 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice19 : pointSliceCheck 0 2248 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice20 : pointSliceCheck 0 2248 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice21 : pointSliceCheck 0 2248 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice22 : pointSliceCheck 0 2248 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice23 : pointSliceCheck 0 2248 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice24 : pointSliceCheck 0 2248 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice25 : pointSliceCheck 0 2248 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice26 : pointSliceCheck 0 2248 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice27 : pointSliceCheck 0 2248 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point74Slice28 : pointSliceCheck 0 2248 28 := by
  decide +kernel

/-- Original transition at residual index 74, certified on every point. -/
public theorem point74 : stepCheck 0 2248 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point74Slice0
  · exact point74Slice1
  · exact point74Slice2
  · exact point74Slice3
  · exact point74Slice4
  · exact point74Slice5
  · exact point74Slice6
  · exact point74Slice7
  · exact point74Slice8
  · exact point74Slice9
  · exact point74Slice10
  · exact point74Slice11
  · exact point74Slice12
  · exact point74Slice13
  · exact point74Slice14
  · exact point74Slice15
  · exact point74Slice16
  · exact point74Slice17
  · exact point74Slice18
  · exact point74Slice19
  · exact point74Slice20
  · exact point74Slice21
  · exact point74Slice22
  · exact point74Slice23
  · exact point74Slice24
  · exact point74Slice25
  · exact point74Slice26
  · exact point74Slice27
  · exact point74Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
