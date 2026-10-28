module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 65–66

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point65Slice0 : pointSliceCheck 1 2103 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice1 : pointSliceCheck 1 2103 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice2 : pointSliceCheck 1 2103 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice3 : pointSliceCheck 1 2103 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice4 : pointSliceCheck 1 2103 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice5 : pointSliceCheck 1 2103 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice6 : pointSliceCheck 1 2103 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice7 : pointSliceCheck 1 2103 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice8 : pointSliceCheck 1 2103 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice9 : pointSliceCheck 1 2103 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice10 : pointSliceCheck 1 2103 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice11 : pointSliceCheck 1 2103 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice12 : pointSliceCheck 1 2103 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice13 : pointSliceCheck 1 2103 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice14 : pointSliceCheck 1 2103 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice15 : pointSliceCheck 1 2103 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice16 : pointSliceCheck 1 2103 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice17 : pointSliceCheck 1 2103 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice18 : pointSliceCheck 1 2103 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice19 : pointSliceCheck 1 2103 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice20 : pointSliceCheck 1 2103 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice21 : pointSliceCheck 1 2103 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice22 : pointSliceCheck 1 2103 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice23 : pointSliceCheck 1 2103 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice24 : pointSliceCheck 1 2103 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice25 : pointSliceCheck 1 2103 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice26 : pointSliceCheck 1 2103 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice27 : pointSliceCheck 1 2103 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice28 : pointSliceCheck 1 2103 28 := by
  decide +kernel

/-- Original transition at residual index 65, certified on every point. -/
public theorem point65 : stepCheck 1 2103 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point65Slice0
  · exact point65Slice1
  · exact point65Slice2
  · exact point65Slice3
  · exact point65Slice4
  · exact point65Slice5
  · exact point65Slice6
  · exact point65Slice7
  · exact point65Slice8
  · exact point65Slice9
  · exact point65Slice10
  · exact point65Slice11
  · exact point65Slice12
  · exact point65Slice13
  · exact point65Slice14
  · exact point65Slice15
  · exact point65Slice16
  · exact point65Slice17
  · exact point65Slice18
  · exact point65Slice19
  · exact point65Slice20
  · exact point65Slice21
  · exact point65Slice22
  · exact point65Slice23
  · exact point65Slice24
  · exact point65Slice25
  · exact point65Slice26
  · exact point65Slice27
  · exact point65Slice28

set_option maxHeartbeats 1600000 in
private theorem point66Slice0 : pointSliceCheck 1 2104 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice1 : pointSliceCheck 1 2104 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice2 : pointSliceCheck 1 2104 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice3 : pointSliceCheck 1 2104 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice4 : pointSliceCheck 1 2104 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice5 : pointSliceCheck 1 2104 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice6 : pointSliceCheck 1 2104 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice7 : pointSliceCheck 1 2104 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice8 : pointSliceCheck 1 2104 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice9 : pointSliceCheck 1 2104 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice10 : pointSliceCheck 1 2104 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice11 : pointSliceCheck 1 2104 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice12 : pointSliceCheck 1 2104 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice13 : pointSliceCheck 1 2104 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice14 : pointSliceCheck 1 2104 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice15 : pointSliceCheck 1 2104 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice16 : pointSliceCheck 1 2104 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice17 : pointSliceCheck 1 2104 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice18 : pointSliceCheck 1 2104 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice19 : pointSliceCheck 1 2104 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice20 : pointSliceCheck 1 2104 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice21 : pointSliceCheck 1 2104 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice22 : pointSliceCheck 1 2104 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice23 : pointSliceCheck 1 2104 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice24 : pointSliceCheck 1 2104 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice25 : pointSliceCheck 1 2104 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice26 : pointSliceCheck 1 2104 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice27 : pointSliceCheck 1 2104 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice28 : pointSliceCheck 1 2104 28 := by
  decide +kernel

/-- Original transition at residual index 66, certified on every point. -/
public theorem point66 : stepCheck 1 2104 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point66Slice0
  · exact point66Slice1
  · exact point66Slice2
  · exact point66Slice3
  · exact point66Slice4
  · exact point66Slice5
  · exact point66Slice6
  · exact point66Slice7
  · exact point66Slice8
  · exact point66Slice9
  · exact point66Slice10
  · exact point66Slice11
  · exact point66Slice12
  · exact point66Slice13
  · exact point66Slice14
  · exact point66Slice15
  · exact point66Slice16
  · exact point66Slice17
  · exact point66Slice18
  · exact point66Slice19
  · exact point66Slice20
  · exact point66Slice21
  · exact point66Slice22
  · exact point66Slice23
  · exact point66Slice24
  · exact point66Slice25
  · exact point66Slice26
  · exact point66Slice27
  · exact point66Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
