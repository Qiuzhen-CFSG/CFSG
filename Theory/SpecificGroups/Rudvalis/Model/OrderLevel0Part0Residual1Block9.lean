module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 83–84

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point83Slice0 : pointSliceCheck 0 2392 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice1 : pointSliceCheck 0 2392 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice2 : pointSliceCheck 0 2392 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice3 : pointSliceCheck 0 2392 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice4 : pointSliceCheck 0 2392 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice5 : pointSliceCheck 0 2392 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice6 : pointSliceCheck 0 2392 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice7 : pointSliceCheck 0 2392 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice8 : pointSliceCheck 0 2392 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice9 : pointSliceCheck 0 2392 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice10 : pointSliceCheck 0 2392 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice11 : pointSliceCheck 0 2392 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice12 : pointSliceCheck 0 2392 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice13 : pointSliceCheck 0 2392 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice14 : pointSliceCheck 0 2392 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice15 : pointSliceCheck 0 2392 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice16 : pointSliceCheck 0 2392 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice17 : pointSliceCheck 0 2392 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice18 : pointSliceCheck 0 2392 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice19 : pointSliceCheck 0 2392 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice20 : pointSliceCheck 0 2392 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice21 : pointSliceCheck 0 2392 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice22 : pointSliceCheck 0 2392 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice23 : pointSliceCheck 0 2392 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice24 : pointSliceCheck 0 2392 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice25 : pointSliceCheck 0 2392 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice26 : pointSliceCheck 0 2392 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice27 : pointSliceCheck 0 2392 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point83Slice28 : pointSliceCheck 0 2392 28 := by
  decide +kernel

/-- Original transition at residual index 83, certified on every point. -/
public theorem point83 : stepCheck 0 2392 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point83Slice0
  · exact point83Slice1
  · exact point83Slice2
  · exact point83Slice3
  · exact point83Slice4
  · exact point83Slice5
  · exact point83Slice6
  · exact point83Slice7
  · exact point83Slice8
  · exact point83Slice9
  · exact point83Slice10
  · exact point83Slice11
  · exact point83Slice12
  · exact point83Slice13
  · exact point83Slice14
  · exact point83Slice15
  · exact point83Slice16
  · exact point83Slice17
  · exact point83Slice18
  · exact point83Slice19
  · exact point83Slice20
  · exact point83Slice21
  · exact point83Slice22
  · exact point83Slice23
  · exact point83Slice24
  · exact point83Slice25
  · exact point83Slice26
  · exact point83Slice27
  · exact point83Slice28

set_option maxHeartbeats 1600000 in
private theorem point84Slice0 : pointSliceCheck 0 2398 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice1 : pointSliceCheck 0 2398 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice2 : pointSliceCheck 0 2398 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice3 : pointSliceCheck 0 2398 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice4 : pointSliceCheck 0 2398 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice5 : pointSliceCheck 0 2398 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice6 : pointSliceCheck 0 2398 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice7 : pointSliceCheck 0 2398 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice8 : pointSliceCheck 0 2398 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice9 : pointSliceCheck 0 2398 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice10 : pointSliceCheck 0 2398 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice11 : pointSliceCheck 0 2398 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice12 : pointSliceCheck 0 2398 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice13 : pointSliceCheck 0 2398 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice14 : pointSliceCheck 0 2398 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice15 : pointSliceCheck 0 2398 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice16 : pointSliceCheck 0 2398 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice17 : pointSliceCheck 0 2398 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice18 : pointSliceCheck 0 2398 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice19 : pointSliceCheck 0 2398 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice20 : pointSliceCheck 0 2398 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice21 : pointSliceCheck 0 2398 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice22 : pointSliceCheck 0 2398 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice23 : pointSliceCheck 0 2398 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice24 : pointSliceCheck 0 2398 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice25 : pointSliceCheck 0 2398 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice26 : pointSliceCheck 0 2398 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice27 : pointSliceCheck 0 2398 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point84Slice28 : pointSliceCheck 0 2398 28 := by
  decide +kernel

/-- Original transition at residual index 84, certified on every point. -/
public theorem point84 : stepCheck 0 2398 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point84Slice0
  · exact point84Slice1
  · exact point84Slice2
  · exact point84Slice3
  · exact point84Slice4
  · exact point84Slice5
  · exact point84Slice6
  · exact point84Slice7
  · exact point84Slice8
  · exact point84Slice9
  · exact point84Slice10
  · exact point84Slice11
  · exact point84Slice12
  · exact point84Slice13
  · exact point84Slice14
  · exact point84Slice15
  · exact point84Slice16
  · exact point84Slice17
  · exact point84Slice18
  · exact point84Slice19
  · exact point84Slice20
  · exact point84Slice21
  · exact point84Slice22
  · exact point84Slice23
  · exact point84Slice24
  · exact point84Slice25
  · exact point84Slice26
  · exact point84Slice27
  · exact point84Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
