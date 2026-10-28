module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis residual transitions 87–88

These transitions are checked on 29 slices of 140 points each.
The separate slice lemmas bound kernel reduction memory, and `ofPointSlices`
recovers the original permutation checks. Source: the ATLAS-derived witnesses
in `OrderLevel0Data` and the indices in `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point87Slice0 : pointSliceCheck 1 2386 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice1 : pointSliceCheck 1 2386 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice2 : pointSliceCheck 1 2386 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice3 : pointSliceCheck 1 2386 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice4 : pointSliceCheck 1 2386 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice5 : pointSliceCheck 1 2386 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice6 : pointSliceCheck 1 2386 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice7 : pointSliceCheck 1 2386 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice8 : pointSliceCheck 1 2386 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice9 : pointSliceCheck 1 2386 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice10 : pointSliceCheck 1 2386 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice11 : pointSliceCheck 1 2386 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice12 : pointSliceCheck 1 2386 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice13 : pointSliceCheck 1 2386 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice14 : pointSliceCheck 1 2386 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice15 : pointSliceCheck 1 2386 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice16 : pointSliceCheck 1 2386 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice17 : pointSliceCheck 1 2386 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice18 : pointSliceCheck 1 2386 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice19 : pointSliceCheck 1 2386 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice20 : pointSliceCheck 1 2386 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice21 : pointSliceCheck 1 2386 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice22 : pointSliceCheck 1 2386 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice23 : pointSliceCheck 1 2386 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice24 : pointSliceCheck 1 2386 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice25 : pointSliceCheck 1 2386 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice26 : pointSliceCheck 1 2386 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice27 : pointSliceCheck 1 2386 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point87Slice28 : pointSliceCheck 1 2386 28 := by
  decide +kernel

/-- Original transition at residual index 87, certified on every point. -/
public theorem point87 : stepCheck 1 2386 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point87Slice0
  · exact point87Slice1
  · exact point87Slice2
  · exact point87Slice3
  · exact point87Slice4
  · exact point87Slice5
  · exact point87Slice6
  · exact point87Slice7
  · exact point87Slice8
  · exact point87Slice9
  · exact point87Slice10
  · exact point87Slice11
  · exact point87Slice12
  · exact point87Slice13
  · exact point87Slice14
  · exact point87Slice15
  · exact point87Slice16
  · exact point87Slice17
  · exact point87Slice18
  · exact point87Slice19
  · exact point87Slice20
  · exact point87Slice21
  · exact point87Slice22
  · exact point87Slice23
  · exact point87Slice24
  · exact point87Slice25
  · exact point87Slice26
  · exact point87Slice27
  · exact point87Slice28

set_option maxHeartbeats 1600000 in
private theorem point88Slice0 : pointSliceCheck 1 2387 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice1 : pointSliceCheck 1 2387 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice2 : pointSliceCheck 1 2387 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice3 : pointSliceCheck 1 2387 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice4 : pointSliceCheck 1 2387 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice5 : pointSliceCheck 1 2387 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice6 : pointSliceCheck 1 2387 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice7 : pointSliceCheck 1 2387 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice8 : pointSliceCheck 1 2387 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice9 : pointSliceCheck 1 2387 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice10 : pointSliceCheck 1 2387 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice11 : pointSliceCheck 1 2387 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice12 : pointSliceCheck 1 2387 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice13 : pointSliceCheck 1 2387 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice14 : pointSliceCheck 1 2387 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice15 : pointSliceCheck 1 2387 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice16 : pointSliceCheck 1 2387 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice17 : pointSliceCheck 1 2387 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice18 : pointSliceCheck 1 2387 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice19 : pointSliceCheck 1 2387 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice20 : pointSliceCheck 1 2387 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice21 : pointSliceCheck 1 2387 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice22 : pointSliceCheck 1 2387 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice23 : pointSliceCheck 1 2387 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice24 : pointSliceCheck 1 2387 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice25 : pointSliceCheck 1 2387 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice26 : pointSliceCheck 1 2387 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice27 : pointSliceCheck 1 2387 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point88Slice28 : pointSliceCheck 1 2387 28 := by
  decide +kernel

/-- Original transition at residual index 88, certified on every point. -/
public theorem point88 : stepCheck 1 2387 := by
  apply ofPointSlices
  intro c
  fin_cases c
  · exact point88Slice0
  · exact point88Slice1
  · exact point88Slice2
  · exact point88Slice3
  · exact point88Slice4
  · exact point88Slice5
  · exact point88Slice6
  · exact point88Slice7
  · exact point88Slice8
  · exact point88Slice9
  · exact point88Slice10
  · exact point88Slice11
  · exact point88Slice12
  · exact point88Slice13
  · exact point88Slice14
  · exact point88Slice15
  · exact point88Slice16
  · exact point88Slice17
  · exact point88Slice18
  · exact point88Slice19
  · exact point88Slice20
  · exact point88Slice21
  · exact point88Slice22
  · exact point88Slice23
  · exact point88Slice24
  · exact point88Slice25
  · exact point88Slice26
  · exact point88Slice27
  · exact point88Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual1
