module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 111–112

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point111Slice0 : pointSliceCheck 1 2664 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice1 : pointSliceCheck 1 2664 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice2 : pointSliceCheck 1 2664 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice3 : pointSliceCheck 1 2664 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice4 : pointSliceCheck 1 2664 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice5 : pointSliceCheck 1 2664 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice6 : pointSliceCheck 1 2664 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice7 : pointSliceCheck 1 2664 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice8 : pointSliceCheck 1 2664 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice9 : pointSliceCheck 1 2664 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice10 : pointSliceCheck 1 2664 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice11 : pointSliceCheck 1 2664 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice12 : pointSliceCheck 1 2664 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice13 : pointSliceCheck 1 2664 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice14 : pointSliceCheck 1 2664 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice15 : pointSliceCheck 1 2664 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice16 : pointSliceCheck 1 2664 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice17 : pointSliceCheck 1 2664 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice18 : pointSliceCheck 1 2664 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice19 : pointSliceCheck 1 2664 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice20 : pointSliceCheck 1 2664 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice21 : pointSliceCheck 1 2664 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice22 : pointSliceCheck 1 2664 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice23 : pointSliceCheck 1 2664 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice24 : pointSliceCheck 1 2664 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice25 : pointSliceCheck 1 2664 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice26 : pointSliceCheck 1 2664 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice27 : pointSliceCheck 1 2664 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point111Slice28 : pointSliceCheck 1 2664 28 := by
  decide +kernel

/-- Original transition at residual index 111, certified on every point. -/
public theorem point111 : stepCheck 1 2664 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point111Slice0
  · exact point111Slice1
  · exact point111Slice2
  · exact point111Slice3
  · exact point111Slice4
  · exact point111Slice5
  · exact point111Slice6
  · exact point111Slice7
  · exact point111Slice8
  · exact point111Slice9
  · exact point111Slice10
  · exact point111Slice11
  · exact point111Slice12
  · exact point111Slice13
  · exact point111Slice14
  · exact point111Slice15
  · exact point111Slice16
  · exact point111Slice17
  · exact point111Slice18
  · exact point111Slice19
  · exact point111Slice20
  · exact point111Slice21
  · exact point111Slice22
  · exact point111Slice23
  · exact point111Slice24
  · exact point111Slice25
  · exact point111Slice26
  · exact point111Slice27
  · exact point111Slice28

set_option maxHeartbeats 1600000 in
private theorem point112Slice0 : pointSliceCheck 1 2665 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice1 : pointSliceCheck 1 2665 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice2 : pointSliceCheck 1 2665 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice3 : pointSliceCheck 1 2665 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice4 : pointSliceCheck 1 2665 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice5 : pointSliceCheck 1 2665 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice6 : pointSliceCheck 1 2665 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice7 : pointSliceCheck 1 2665 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice8 : pointSliceCheck 1 2665 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice9 : pointSliceCheck 1 2665 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice10 : pointSliceCheck 1 2665 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice11 : pointSliceCheck 1 2665 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice12 : pointSliceCheck 1 2665 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice13 : pointSliceCheck 1 2665 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice14 : pointSliceCheck 1 2665 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice15 : pointSliceCheck 1 2665 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice16 : pointSliceCheck 1 2665 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice17 : pointSliceCheck 1 2665 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice18 : pointSliceCheck 1 2665 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice19 : pointSliceCheck 1 2665 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice20 : pointSliceCheck 1 2665 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice21 : pointSliceCheck 1 2665 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice22 : pointSliceCheck 1 2665 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice23 : pointSliceCheck 1 2665 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice24 : pointSliceCheck 1 2665 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice25 : pointSliceCheck 1 2665 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice26 : pointSliceCheck 1 2665 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice27 : pointSliceCheck 1 2665 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point112Slice28 : pointSliceCheck 1 2665 28 := by
  decide +kernel

/-- Original transition at residual index 112, certified on every point. -/
public theorem point112 : stepCheck 1 2665 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point112Slice0
  · exact point112Slice1
  · exact point112Slice2
  · exact point112Slice3
  · exact point112Slice4
  · exact point112Slice5
  · exact point112Slice6
  · exact point112Slice7
  · exact point112Slice8
  · exact point112Slice9
  · exact point112Slice10
  · exact point112Slice11
  · exact point112Slice12
  · exact point112Slice13
  · exact point112Slice14
  · exact point112Slice15
  · exact point112Slice16
  · exact point112Slice17
  · exact point112Slice18
  · exact point112Slice19
  · exact point112Slice20
  · exact point112Slice21
  · exact point112Slice22
  · exact point112Slice23
  · exact point112Slice24
  · exact point112Slice25
  · exact point112Slice26
  · exact point112Slice27
  · exact point112Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
