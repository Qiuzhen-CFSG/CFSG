module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 91–92

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point91Slice0 : pointSliceCheck 1 2397 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice1 : pointSliceCheck 1 2397 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice2 : pointSliceCheck 1 2397 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice3 : pointSliceCheck 1 2397 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice4 : pointSliceCheck 1 2397 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice5 : pointSliceCheck 1 2397 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice6 : pointSliceCheck 1 2397 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice7 : pointSliceCheck 1 2397 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice8 : pointSliceCheck 1 2397 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice9 : pointSliceCheck 1 2397 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice10 : pointSliceCheck 1 2397 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice11 : pointSliceCheck 1 2397 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice12 : pointSliceCheck 1 2397 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice13 : pointSliceCheck 1 2397 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice14 : pointSliceCheck 1 2397 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice15 : pointSliceCheck 1 2397 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice16 : pointSliceCheck 1 2397 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice17 : pointSliceCheck 1 2397 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice18 : pointSliceCheck 1 2397 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice19 : pointSliceCheck 1 2397 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice20 : pointSliceCheck 1 2397 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice21 : pointSliceCheck 1 2397 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice22 : pointSliceCheck 1 2397 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice23 : pointSliceCheck 1 2397 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice24 : pointSliceCheck 1 2397 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice25 : pointSliceCheck 1 2397 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice26 : pointSliceCheck 1 2397 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice27 : pointSliceCheck 1 2397 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point91Slice28 : pointSliceCheck 1 2397 28 := by
  decide +kernel

/-- Original transition at residual index 91, certified on every point. -/
public theorem point91 : stepCheck 1 2397 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point91Slice0
  · exact point91Slice1
  · exact point91Slice2
  · exact point91Slice3
  · exact point91Slice4
  · exact point91Slice5
  · exact point91Slice6
  · exact point91Slice7
  · exact point91Slice8
  · exact point91Slice9
  · exact point91Slice10
  · exact point91Slice11
  · exact point91Slice12
  · exact point91Slice13
  · exact point91Slice14
  · exact point91Slice15
  · exact point91Slice16
  · exact point91Slice17
  · exact point91Slice18
  · exact point91Slice19
  · exact point91Slice20
  · exact point91Slice21
  · exact point91Slice22
  · exact point91Slice23
  · exact point91Slice24
  · exact point91Slice25
  · exact point91Slice26
  · exact point91Slice27
  · exact point91Slice28

set_option maxHeartbeats 1600000 in
private theorem point92Slice0 : pointSliceCheck 1 2398 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice1 : pointSliceCheck 1 2398 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice2 : pointSliceCheck 1 2398 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice3 : pointSliceCheck 1 2398 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice4 : pointSliceCheck 1 2398 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice5 : pointSliceCheck 1 2398 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice6 : pointSliceCheck 1 2398 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice7 : pointSliceCheck 1 2398 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice8 : pointSliceCheck 1 2398 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice9 : pointSliceCheck 1 2398 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice10 : pointSliceCheck 1 2398 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice11 : pointSliceCheck 1 2398 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice12 : pointSliceCheck 1 2398 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice13 : pointSliceCheck 1 2398 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice14 : pointSliceCheck 1 2398 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice15 : pointSliceCheck 1 2398 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice16 : pointSliceCheck 1 2398 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice17 : pointSliceCheck 1 2398 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice18 : pointSliceCheck 1 2398 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice19 : pointSliceCheck 1 2398 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice20 : pointSliceCheck 1 2398 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice21 : pointSliceCheck 1 2398 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice22 : pointSliceCheck 1 2398 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice23 : pointSliceCheck 1 2398 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice24 : pointSliceCheck 1 2398 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice25 : pointSliceCheck 1 2398 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice26 : pointSliceCheck 1 2398 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice27 : pointSliceCheck 1 2398 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point92Slice28 : pointSliceCheck 1 2398 28 := by
  decide +kernel

/-- Original transition at residual index 92, certified on every point. -/
public theorem point92 : stepCheck 1 2398 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point92Slice0
  · exact point92Slice1
  · exact point92Slice2
  · exact point92Slice3
  · exact point92Slice4
  · exact point92Slice5
  · exact point92Slice6
  · exact point92Slice7
  · exact point92Slice8
  · exact point92Slice9
  · exact point92Slice10
  · exact point92Slice11
  · exact point92Slice12
  · exact point92Slice13
  · exact point92Slice14
  · exact point92Slice15
  · exact point92Slice16
  · exact point92Slice17
  · exact point92Slice18
  · exact point92Slice19
  · exact point92Slice20
  · exact point92Slice21
  · exact point92Slice22
  · exact point92Slice23
  · exact point92Slice24
  · exact point92Slice25
  · exact point92Slice26
  · exact point92Slice27
  · exact point92Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
