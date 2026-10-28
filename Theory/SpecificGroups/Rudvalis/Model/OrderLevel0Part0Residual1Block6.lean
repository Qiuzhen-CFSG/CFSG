module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 77–78

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point77Slice0 : pointSliceCheck 1 2255 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice1 : pointSliceCheck 1 2255 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice2 : pointSliceCheck 1 2255 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice3 : pointSliceCheck 1 2255 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice4 : pointSliceCheck 1 2255 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice5 : pointSliceCheck 1 2255 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice6 : pointSliceCheck 1 2255 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice7 : pointSliceCheck 1 2255 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice8 : pointSliceCheck 1 2255 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice9 : pointSliceCheck 1 2255 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice10 : pointSliceCheck 1 2255 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice11 : pointSliceCheck 1 2255 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice12 : pointSliceCheck 1 2255 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice13 : pointSliceCheck 1 2255 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice14 : pointSliceCheck 1 2255 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice15 : pointSliceCheck 1 2255 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice16 : pointSliceCheck 1 2255 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice17 : pointSliceCheck 1 2255 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice18 : pointSliceCheck 1 2255 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice19 : pointSliceCheck 1 2255 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice20 : pointSliceCheck 1 2255 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice21 : pointSliceCheck 1 2255 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice22 : pointSliceCheck 1 2255 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice23 : pointSliceCheck 1 2255 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice24 : pointSliceCheck 1 2255 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice25 : pointSliceCheck 1 2255 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice26 : pointSliceCheck 1 2255 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice27 : pointSliceCheck 1 2255 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point77Slice28 : pointSliceCheck 1 2255 28 := by
  decide +kernel

/-- Original transition at residual index 77, certified on every point. -/
public theorem point77 : stepCheck 1 2255 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point77Slice0
  · exact point77Slice1
  · exact point77Slice2
  · exact point77Slice3
  · exact point77Slice4
  · exact point77Slice5
  · exact point77Slice6
  · exact point77Slice7
  · exact point77Slice8
  · exact point77Slice9
  · exact point77Slice10
  · exact point77Slice11
  · exact point77Slice12
  · exact point77Slice13
  · exact point77Slice14
  · exact point77Slice15
  · exact point77Slice16
  · exact point77Slice17
  · exact point77Slice18
  · exact point77Slice19
  · exact point77Slice20
  · exact point77Slice21
  · exact point77Slice22
  · exact point77Slice23
  · exact point77Slice24
  · exact point77Slice25
  · exact point77Slice26
  · exact point77Slice27
  · exact point77Slice28

set_option maxHeartbeats 1600000 in
private theorem point78Slice0 : pointSliceCheck 1 2257 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice1 : pointSliceCheck 1 2257 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice2 : pointSliceCheck 1 2257 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice3 : pointSliceCheck 1 2257 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice4 : pointSliceCheck 1 2257 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice5 : pointSliceCheck 1 2257 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice6 : pointSliceCheck 1 2257 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice7 : pointSliceCheck 1 2257 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice8 : pointSliceCheck 1 2257 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice9 : pointSliceCheck 1 2257 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice10 : pointSliceCheck 1 2257 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice11 : pointSliceCheck 1 2257 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice12 : pointSliceCheck 1 2257 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice13 : pointSliceCheck 1 2257 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice14 : pointSliceCheck 1 2257 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice15 : pointSliceCheck 1 2257 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice16 : pointSliceCheck 1 2257 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice17 : pointSliceCheck 1 2257 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice18 : pointSliceCheck 1 2257 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice19 : pointSliceCheck 1 2257 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice20 : pointSliceCheck 1 2257 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice21 : pointSliceCheck 1 2257 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice22 : pointSliceCheck 1 2257 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice23 : pointSliceCheck 1 2257 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice24 : pointSliceCheck 1 2257 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice25 : pointSliceCheck 1 2257 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice26 : pointSliceCheck 1 2257 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice27 : pointSliceCheck 1 2257 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point78Slice28 : pointSliceCheck 1 2257 28 := by
  decide +kernel

/-- Original transition at residual index 78, certified on every point. -/
public theorem point78 : stepCheck 1 2257 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point78Slice0
  · exact point78Slice1
  · exact point78Slice2
  · exact point78Slice3
  · exact point78Slice4
  · exact point78Slice5
  · exact point78Slice6
  · exact point78Slice7
  · exact point78Slice8
  · exact point78Slice9
  · exact point78Slice10
  · exact point78Slice11
  · exact point78Slice12
  · exact point78Slice13
  · exact point78Slice14
  · exact point78Slice15
  · exact point78Slice16
  · exact point78Slice17
  · exact point78Slice18
  · exact point78Slice19
  · exact point78Slice20
  · exact point78Slice21
  · exact point78Slice22
  · exact point78Slice23
  · exact point78Slice24
  · exact point78Slice25
  · exact point78Slice26
  · exact point78Slice27
  · exact point78Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
