module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 115–116

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point115Slice0 : pointSliceCheck 0 2804 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice1 : pointSliceCheck 0 2804 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice2 : pointSliceCheck 0 2804 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice3 : pointSliceCheck 0 2804 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice4 : pointSliceCheck 0 2804 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice5 : pointSliceCheck 0 2804 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice6 : pointSliceCheck 0 2804 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice7 : pointSliceCheck 0 2804 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice8 : pointSliceCheck 0 2804 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice9 : pointSliceCheck 0 2804 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice10 : pointSliceCheck 0 2804 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice11 : pointSliceCheck 0 2804 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice12 : pointSliceCheck 0 2804 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice13 : pointSliceCheck 0 2804 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice14 : pointSliceCheck 0 2804 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice15 : pointSliceCheck 0 2804 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice16 : pointSliceCheck 0 2804 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice17 : pointSliceCheck 0 2804 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice18 : pointSliceCheck 0 2804 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice19 : pointSliceCheck 0 2804 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice20 : pointSliceCheck 0 2804 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice21 : pointSliceCheck 0 2804 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice22 : pointSliceCheck 0 2804 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice23 : pointSliceCheck 0 2804 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice24 : pointSliceCheck 0 2804 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice25 : pointSliceCheck 0 2804 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice26 : pointSliceCheck 0 2804 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice27 : pointSliceCheck 0 2804 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point115Slice28 : pointSliceCheck 0 2804 28 := by
  decide +kernel

/-- Original transition at residual index 115, certified on every point. -/
public theorem point115 : stepCheck 0 2804 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point115Slice0
  · exact point115Slice1
  · exact point115Slice2
  · exact point115Slice3
  · exact point115Slice4
  · exact point115Slice5
  · exact point115Slice6
  · exact point115Slice7
  · exact point115Slice8
  · exact point115Slice9
  · exact point115Slice10
  · exact point115Slice11
  · exact point115Slice12
  · exact point115Slice13
  · exact point115Slice14
  · exact point115Slice15
  · exact point115Slice16
  · exact point115Slice17
  · exact point115Slice18
  · exact point115Slice19
  · exact point115Slice20
  · exact point115Slice21
  · exact point115Slice22
  · exact point115Slice23
  · exact point115Slice24
  · exact point115Slice25
  · exact point115Slice26
  · exact point115Slice27
  · exact point115Slice28

set_option maxHeartbeats 1600000 in
private theorem point116Slice0 : pointSliceCheck 0 2808 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice1 : pointSliceCheck 0 2808 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice2 : pointSliceCheck 0 2808 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice3 : pointSliceCheck 0 2808 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice4 : pointSliceCheck 0 2808 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice5 : pointSliceCheck 0 2808 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice6 : pointSliceCheck 0 2808 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice7 : pointSliceCheck 0 2808 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice8 : pointSliceCheck 0 2808 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice9 : pointSliceCheck 0 2808 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice10 : pointSliceCheck 0 2808 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice11 : pointSliceCheck 0 2808 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice12 : pointSliceCheck 0 2808 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice13 : pointSliceCheck 0 2808 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice14 : pointSliceCheck 0 2808 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice15 : pointSliceCheck 0 2808 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice16 : pointSliceCheck 0 2808 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice17 : pointSliceCheck 0 2808 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice18 : pointSliceCheck 0 2808 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice19 : pointSliceCheck 0 2808 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice20 : pointSliceCheck 0 2808 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice21 : pointSliceCheck 0 2808 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice22 : pointSliceCheck 0 2808 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice23 : pointSliceCheck 0 2808 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice24 : pointSliceCheck 0 2808 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice25 : pointSliceCheck 0 2808 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice26 : pointSliceCheck 0 2808 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice27 : pointSliceCheck 0 2808 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point116Slice28 : pointSliceCheck 0 2808 28 := by
  decide +kernel

/-- Original transition at residual index 116, certified on every point. -/
public theorem point116 : stepCheck 0 2808 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point116Slice0
  · exact point116Slice1
  · exact point116Slice2
  · exact point116Slice3
  · exact point116Slice4
  · exact point116Slice5
  · exact point116Slice6
  · exact point116Slice7
  · exact point116Slice8
  · exact point116Slice9
  · exact point116Slice10
  · exact point116Slice11
  · exact point116Slice12
  · exact point116Slice13
  · exact point116Slice14
  · exact point116Slice15
  · exact point116Slice16
  · exact point116Slice17
  · exact point116Slice18
  · exact point116Slice19
  · exact point116Slice20
  · exact point116Slice21
  · exact point116Slice22
  · exact point116Slice23
  · exact point116Slice24
  · exact point116Slice25
  · exact point116Slice26
  · exact point116Slice27
  · exact point116Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
