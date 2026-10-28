module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 81–82

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point81Slice0 : pointSliceCheck 0 2385 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice1 : pointSliceCheck 0 2385 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice2 : pointSliceCheck 0 2385 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice3 : pointSliceCheck 0 2385 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice4 : pointSliceCheck 0 2385 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice5 : pointSliceCheck 0 2385 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice6 : pointSliceCheck 0 2385 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice7 : pointSliceCheck 0 2385 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice8 : pointSliceCheck 0 2385 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice9 : pointSliceCheck 0 2385 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice10 : pointSliceCheck 0 2385 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice11 : pointSliceCheck 0 2385 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice12 : pointSliceCheck 0 2385 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice13 : pointSliceCheck 0 2385 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice14 : pointSliceCheck 0 2385 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice15 : pointSliceCheck 0 2385 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice16 : pointSliceCheck 0 2385 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice17 : pointSliceCheck 0 2385 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice18 : pointSliceCheck 0 2385 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice19 : pointSliceCheck 0 2385 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice20 : pointSliceCheck 0 2385 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice21 : pointSliceCheck 0 2385 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice22 : pointSliceCheck 0 2385 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice23 : pointSliceCheck 0 2385 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice24 : pointSliceCheck 0 2385 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice25 : pointSliceCheck 0 2385 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice26 : pointSliceCheck 0 2385 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice27 : pointSliceCheck 0 2385 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point81Slice28 : pointSliceCheck 0 2385 28 := by
  decide +kernel

/-- Original transition at residual index 81, certified on every point. -/
public theorem point81 : stepCheck 0 2385 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point81Slice0
  · exact point81Slice1
  · exact point81Slice2
  · exact point81Slice3
  · exact point81Slice4
  · exact point81Slice5
  · exact point81Slice6
  · exact point81Slice7
  · exact point81Slice8
  · exact point81Slice9
  · exact point81Slice10
  · exact point81Slice11
  · exact point81Slice12
  · exact point81Slice13
  · exact point81Slice14
  · exact point81Slice15
  · exact point81Slice16
  · exact point81Slice17
  · exact point81Slice18
  · exact point81Slice19
  · exact point81Slice20
  · exact point81Slice21
  · exact point81Slice22
  · exact point81Slice23
  · exact point81Slice24
  · exact point81Slice25
  · exact point81Slice26
  · exact point81Slice27
  · exact point81Slice28

set_option maxHeartbeats 1600000 in
private theorem point82Slice0 : pointSliceCheck 0 2387 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice1 : pointSliceCheck 0 2387 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice2 : pointSliceCheck 0 2387 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice3 : pointSliceCheck 0 2387 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice4 : pointSliceCheck 0 2387 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice5 : pointSliceCheck 0 2387 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice6 : pointSliceCheck 0 2387 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice7 : pointSliceCheck 0 2387 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice8 : pointSliceCheck 0 2387 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice9 : pointSliceCheck 0 2387 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice10 : pointSliceCheck 0 2387 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice11 : pointSliceCheck 0 2387 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice12 : pointSliceCheck 0 2387 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice13 : pointSliceCheck 0 2387 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice14 : pointSliceCheck 0 2387 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice15 : pointSliceCheck 0 2387 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice16 : pointSliceCheck 0 2387 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice17 : pointSliceCheck 0 2387 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice18 : pointSliceCheck 0 2387 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice19 : pointSliceCheck 0 2387 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice20 : pointSliceCheck 0 2387 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice21 : pointSliceCheck 0 2387 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice22 : pointSliceCheck 0 2387 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice23 : pointSliceCheck 0 2387 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice24 : pointSliceCheck 0 2387 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice25 : pointSliceCheck 0 2387 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice26 : pointSliceCheck 0 2387 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice27 : pointSliceCheck 0 2387 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point82Slice28 : pointSliceCheck 0 2387 28 := by
  decide +kernel

/-- Original transition at residual index 82, certified on every point. -/
public theorem point82 : stepCheck 0 2387 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point82Slice0
  · exact point82Slice1
  · exact point82Slice2
  · exact point82Slice3
  · exact point82Slice4
  · exact point82Slice5
  · exact point82Slice6
  · exact point82Slice7
  · exact point82Slice8
  · exact point82Slice9
  · exact point82Slice10
  · exact point82Slice11
  · exact point82Slice12
  · exact point82Slice13
  · exact point82Slice14
  · exact point82Slice15
  · exact point82Slice16
  · exact point82Slice17
  · exact point82Slice18
  · exact point82Slice19
  · exact point82Slice20
  · exact point82Slice21
  · exact point82Slice22
  · exact point82Slice23
  · exact point82Slice24
  · exact point82Slice25
  · exact point82Slice26
  · exact point82Slice27
  · exact point82Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
