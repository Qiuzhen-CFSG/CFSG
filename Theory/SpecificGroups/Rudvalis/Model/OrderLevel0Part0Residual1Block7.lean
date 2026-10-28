module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 79–80

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point79Slice0 : pointSliceCheck 0 2380 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice1 : pointSliceCheck 0 2380 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice2 : pointSliceCheck 0 2380 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice3 : pointSliceCheck 0 2380 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice4 : pointSliceCheck 0 2380 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice5 : pointSliceCheck 0 2380 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice6 : pointSliceCheck 0 2380 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice7 : pointSliceCheck 0 2380 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice8 : pointSliceCheck 0 2380 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice9 : pointSliceCheck 0 2380 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice10 : pointSliceCheck 0 2380 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice11 : pointSliceCheck 0 2380 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice12 : pointSliceCheck 0 2380 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice13 : pointSliceCheck 0 2380 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice14 : pointSliceCheck 0 2380 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice15 : pointSliceCheck 0 2380 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice16 : pointSliceCheck 0 2380 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice17 : pointSliceCheck 0 2380 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice18 : pointSliceCheck 0 2380 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice19 : pointSliceCheck 0 2380 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice20 : pointSliceCheck 0 2380 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice21 : pointSliceCheck 0 2380 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice22 : pointSliceCheck 0 2380 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice23 : pointSliceCheck 0 2380 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice24 : pointSliceCheck 0 2380 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice25 : pointSliceCheck 0 2380 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice26 : pointSliceCheck 0 2380 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice27 : pointSliceCheck 0 2380 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point79Slice28 : pointSliceCheck 0 2380 28 := by
  decide +kernel

/-- Original transition at residual index 79, certified on every point. -/
public theorem point79 : stepCheck 0 2380 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point79Slice0
  · exact point79Slice1
  · exact point79Slice2
  · exact point79Slice3
  · exact point79Slice4
  · exact point79Slice5
  · exact point79Slice6
  · exact point79Slice7
  · exact point79Slice8
  · exact point79Slice9
  · exact point79Slice10
  · exact point79Slice11
  · exact point79Slice12
  · exact point79Slice13
  · exact point79Slice14
  · exact point79Slice15
  · exact point79Slice16
  · exact point79Slice17
  · exact point79Slice18
  · exact point79Slice19
  · exact point79Slice20
  · exact point79Slice21
  · exact point79Slice22
  · exact point79Slice23
  · exact point79Slice24
  · exact point79Slice25
  · exact point79Slice26
  · exact point79Slice27
  · exact point79Slice28

set_option maxHeartbeats 1600000 in
private theorem point80Slice0 : pointSliceCheck 0 2381 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice1 : pointSliceCheck 0 2381 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice2 : pointSliceCheck 0 2381 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice3 : pointSliceCheck 0 2381 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice4 : pointSliceCheck 0 2381 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice5 : pointSliceCheck 0 2381 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice6 : pointSliceCheck 0 2381 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice7 : pointSliceCheck 0 2381 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice8 : pointSliceCheck 0 2381 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice9 : pointSliceCheck 0 2381 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice10 : pointSliceCheck 0 2381 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice11 : pointSliceCheck 0 2381 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice12 : pointSliceCheck 0 2381 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice13 : pointSliceCheck 0 2381 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice14 : pointSliceCheck 0 2381 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice15 : pointSliceCheck 0 2381 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice16 : pointSliceCheck 0 2381 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice17 : pointSliceCheck 0 2381 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice18 : pointSliceCheck 0 2381 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice19 : pointSliceCheck 0 2381 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice20 : pointSliceCheck 0 2381 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice21 : pointSliceCheck 0 2381 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice22 : pointSliceCheck 0 2381 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice23 : pointSliceCheck 0 2381 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice24 : pointSliceCheck 0 2381 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice25 : pointSliceCheck 0 2381 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice26 : pointSliceCheck 0 2381 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice27 : pointSliceCheck 0 2381 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point80Slice28 : pointSliceCheck 0 2381 28 := by
  decide +kernel

/-- Original transition at residual index 80, certified on every point. -/
public theorem point80 : stepCheck 0 2381 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point80Slice0
  · exact point80Slice1
  · exact point80Slice2
  · exact point80Slice3
  · exact point80Slice4
  · exact point80Slice5
  · exact point80Slice6
  · exact point80Slice7
  · exact point80Slice8
  · exact point80Slice9
  · exact point80Slice10
  · exact point80Slice11
  · exact point80Slice12
  · exact point80Slice13
  · exact point80Slice14
  · exact point80Slice15
  · exact point80Slice16
  · exact point80Slice17
  · exact point80Slice18
  · exact point80Slice19
  · exact point80Slice20
  · exact point80Slice21
  · exact point80Slice22
  · exact point80Slice23
  · exact point80Slice24
  · exact point80Slice25
  · exact point80Slice26
  · exact point80Slice27
  · exact point80Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
