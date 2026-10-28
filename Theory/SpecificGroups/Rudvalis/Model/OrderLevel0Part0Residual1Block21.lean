module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 107–108

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point107Slice0 : pointSliceCheck 0 2670 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice1 : pointSliceCheck 0 2670 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice2 : pointSliceCheck 0 2670 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice3 : pointSliceCheck 0 2670 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice4 : pointSliceCheck 0 2670 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice5 : pointSliceCheck 0 2670 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice6 : pointSliceCheck 0 2670 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice7 : pointSliceCheck 0 2670 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice8 : pointSliceCheck 0 2670 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice9 : pointSliceCheck 0 2670 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice10 : pointSliceCheck 0 2670 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice11 : pointSliceCheck 0 2670 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice12 : pointSliceCheck 0 2670 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice13 : pointSliceCheck 0 2670 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice14 : pointSliceCheck 0 2670 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice15 : pointSliceCheck 0 2670 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice16 : pointSliceCheck 0 2670 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice17 : pointSliceCheck 0 2670 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice18 : pointSliceCheck 0 2670 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice19 : pointSliceCheck 0 2670 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice20 : pointSliceCheck 0 2670 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice21 : pointSliceCheck 0 2670 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice22 : pointSliceCheck 0 2670 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice23 : pointSliceCheck 0 2670 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice24 : pointSliceCheck 0 2670 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice25 : pointSliceCheck 0 2670 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice26 : pointSliceCheck 0 2670 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice27 : pointSliceCheck 0 2670 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point107Slice28 : pointSliceCheck 0 2670 28 := by
  decide +kernel

/-- Original transition at residual index 107, certified on every point. -/
public theorem point107 : stepCheck 0 2670 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point107Slice0
  · exact point107Slice1
  · exact point107Slice2
  · exact point107Slice3
  · exact point107Slice4
  · exact point107Slice5
  · exact point107Slice6
  · exact point107Slice7
  · exact point107Slice8
  · exact point107Slice9
  · exact point107Slice10
  · exact point107Slice11
  · exact point107Slice12
  · exact point107Slice13
  · exact point107Slice14
  · exact point107Slice15
  · exact point107Slice16
  · exact point107Slice17
  · exact point107Slice18
  · exact point107Slice19
  · exact point107Slice20
  · exact point107Slice21
  · exact point107Slice22
  · exact point107Slice23
  · exact point107Slice24
  · exact point107Slice25
  · exact point107Slice26
  · exact point107Slice27
  · exact point107Slice28

set_option maxHeartbeats 1600000 in
private theorem point108Slice0 : pointSliceCheck 0 2672 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice1 : pointSliceCheck 0 2672 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice2 : pointSliceCheck 0 2672 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice3 : pointSliceCheck 0 2672 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice4 : pointSliceCheck 0 2672 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice5 : pointSliceCheck 0 2672 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice6 : pointSliceCheck 0 2672 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice7 : pointSliceCheck 0 2672 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice8 : pointSliceCheck 0 2672 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice9 : pointSliceCheck 0 2672 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice10 : pointSliceCheck 0 2672 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice11 : pointSliceCheck 0 2672 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice12 : pointSliceCheck 0 2672 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice13 : pointSliceCheck 0 2672 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice14 : pointSliceCheck 0 2672 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice15 : pointSliceCheck 0 2672 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice16 : pointSliceCheck 0 2672 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice17 : pointSliceCheck 0 2672 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice18 : pointSliceCheck 0 2672 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice19 : pointSliceCheck 0 2672 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice20 : pointSliceCheck 0 2672 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice21 : pointSliceCheck 0 2672 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice22 : pointSliceCheck 0 2672 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice23 : pointSliceCheck 0 2672 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice24 : pointSliceCheck 0 2672 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice25 : pointSliceCheck 0 2672 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice26 : pointSliceCheck 0 2672 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice27 : pointSliceCheck 0 2672 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point108Slice28 : pointSliceCheck 0 2672 28 := by
  decide +kernel

/-- Original transition at residual index 108, certified on every point. -/
public theorem point108 : stepCheck 0 2672 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point108Slice0
  · exact point108Slice1
  · exact point108Slice2
  · exact point108Slice3
  · exact point108Slice4
  · exact point108Slice5
  · exact point108Slice6
  · exact point108Slice7
  · exact point108Slice8
  · exact point108Slice9
  · exact point108Slice10
  · exact point108Slice11
  · exact point108Slice12
  · exact point108Slice13
  · exact point108Slice14
  · exact point108Slice15
  · exact point108Slice16
  · exact point108Slice17
  · exact point108Slice18
  · exact point108Slice19
  · exact point108Slice20
  · exact point108Slice21
  · exact point108Slice22
  · exact point108Slice23
  · exact point108Slice24
  · exact point108Slice25
  · exact point108Slice26
  · exact point108Slice27
  · exact point108Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
