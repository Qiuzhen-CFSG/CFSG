module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 198–203

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point198Slice0 : Part0Residual.pointSliceCheck 1 3402 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice1 : Part0Residual.pointSliceCheck 1 3402 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice2 : Part0Residual.pointSliceCheck 1 3402 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice3 : Part0Residual.pointSliceCheck 1 3402 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice4 : Part0Residual.pointSliceCheck 1 3402 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice5 : Part0Residual.pointSliceCheck 1 3402 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice6 : Part0Residual.pointSliceCheck 1 3402 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice7 : Part0Residual.pointSliceCheck 1 3402 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice8 : Part0Residual.pointSliceCheck 1 3402 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice9 : Part0Residual.pointSliceCheck 1 3402 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice10 : Part0Residual.pointSliceCheck 1 3402 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice11 : Part0Residual.pointSliceCheck 1 3402 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice12 : Part0Residual.pointSliceCheck 1 3402 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice13 : Part0Residual.pointSliceCheck 1 3402 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice14 : Part0Residual.pointSliceCheck 1 3402 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice15 : Part0Residual.pointSliceCheck 1 3402 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice16 : Part0Residual.pointSliceCheck 1 3402 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice17 : Part0Residual.pointSliceCheck 1 3402 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice18 : Part0Residual.pointSliceCheck 1 3402 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice19 : Part0Residual.pointSliceCheck 1 3402 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice20 : Part0Residual.pointSliceCheck 1 3402 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice21 : Part0Residual.pointSliceCheck 1 3402 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice22 : Part0Residual.pointSliceCheck 1 3402 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice23 : Part0Residual.pointSliceCheck 1 3402 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice24 : Part0Residual.pointSliceCheck 1 3402 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice25 : Part0Residual.pointSliceCheck 1 3402 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice26 : Part0Residual.pointSliceCheck 1 3402 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice27 : Part0Residual.pointSliceCheck 1 3402 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point198Slice28 : Part0Residual.pointSliceCheck 1 3402 28 := by
  decide +kernel

public theorem point198 : stepCheck 1 3402 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point198Slice0
  · exact point198Slice1
  · exact point198Slice2
  · exact point198Slice3
  · exact point198Slice4
  · exact point198Slice5
  · exact point198Slice6
  · exact point198Slice7
  · exact point198Slice8
  · exact point198Slice9
  · exact point198Slice10
  · exact point198Slice11
  · exact point198Slice12
  · exact point198Slice13
  · exact point198Slice14
  · exact point198Slice15
  · exact point198Slice16
  · exact point198Slice17
  · exact point198Slice18
  · exact point198Slice19
  · exact point198Slice20
  · exact point198Slice21
  · exact point198Slice22
  · exact point198Slice23
  · exact point198Slice24
  · exact point198Slice25
  · exact point198Slice26
  · exact point198Slice27
  · exact point198Slice28

set_option maxHeartbeats 1600000 in
private theorem point199Slice0 : Part0Residual.pointSliceCheck 1 3409 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice1 : Part0Residual.pointSliceCheck 1 3409 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice2 : Part0Residual.pointSliceCheck 1 3409 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice3 : Part0Residual.pointSliceCheck 1 3409 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice4 : Part0Residual.pointSliceCheck 1 3409 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice5 : Part0Residual.pointSliceCheck 1 3409 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice6 : Part0Residual.pointSliceCheck 1 3409 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice7 : Part0Residual.pointSliceCheck 1 3409 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice8 : Part0Residual.pointSliceCheck 1 3409 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice9 : Part0Residual.pointSliceCheck 1 3409 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice10 : Part0Residual.pointSliceCheck 1 3409 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice11 : Part0Residual.pointSliceCheck 1 3409 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice12 : Part0Residual.pointSliceCheck 1 3409 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice13 : Part0Residual.pointSliceCheck 1 3409 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice14 : Part0Residual.pointSliceCheck 1 3409 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice15 : Part0Residual.pointSliceCheck 1 3409 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice16 : Part0Residual.pointSliceCheck 1 3409 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice17 : Part0Residual.pointSliceCheck 1 3409 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice18 : Part0Residual.pointSliceCheck 1 3409 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice19 : Part0Residual.pointSliceCheck 1 3409 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice20 : Part0Residual.pointSliceCheck 1 3409 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice21 : Part0Residual.pointSliceCheck 1 3409 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice22 : Part0Residual.pointSliceCheck 1 3409 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice23 : Part0Residual.pointSliceCheck 1 3409 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice24 : Part0Residual.pointSliceCheck 1 3409 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice25 : Part0Residual.pointSliceCheck 1 3409 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice26 : Part0Residual.pointSliceCheck 1 3409 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice27 : Part0Residual.pointSliceCheck 1 3409 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point199Slice28 : Part0Residual.pointSliceCheck 1 3409 28 := by
  decide +kernel

public theorem point199 : stepCheck 1 3409 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point199Slice0
  · exact point199Slice1
  · exact point199Slice2
  · exact point199Slice3
  · exact point199Slice4
  · exact point199Slice5
  · exact point199Slice6
  · exact point199Slice7
  · exact point199Slice8
  · exact point199Slice9
  · exact point199Slice10
  · exact point199Slice11
  · exact point199Slice12
  · exact point199Slice13
  · exact point199Slice14
  · exact point199Slice15
  · exact point199Slice16
  · exact point199Slice17
  · exact point199Slice18
  · exact point199Slice19
  · exact point199Slice20
  · exact point199Slice21
  · exact point199Slice22
  · exact point199Slice23
  · exact point199Slice24
  · exact point199Slice25
  · exact point199Slice26
  · exact point199Slice27
  · exact point199Slice28

set_option maxHeartbeats 1600000 in
private theorem point200Slice0 : Part0Residual.pointSliceCheck 1 3410 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice1 : Part0Residual.pointSliceCheck 1 3410 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice2 : Part0Residual.pointSliceCheck 1 3410 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice3 : Part0Residual.pointSliceCheck 1 3410 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice4 : Part0Residual.pointSliceCheck 1 3410 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice5 : Part0Residual.pointSliceCheck 1 3410 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice6 : Part0Residual.pointSliceCheck 1 3410 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice7 : Part0Residual.pointSliceCheck 1 3410 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice8 : Part0Residual.pointSliceCheck 1 3410 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice9 : Part0Residual.pointSliceCheck 1 3410 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice10 : Part0Residual.pointSliceCheck 1 3410 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice11 : Part0Residual.pointSliceCheck 1 3410 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice12 : Part0Residual.pointSliceCheck 1 3410 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice13 : Part0Residual.pointSliceCheck 1 3410 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice14 : Part0Residual.pointSliceCheck 1 3410 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice15 : Part0Residual.pointSliceCheck 1 3410 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice16 : Part0Residual.pointSliceCheck 1 3410 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice17 : Part0Residual.pointSliceCheck 1 3410 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice18 : Part0Residual.pointSliceCheck 1 3410 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice19 : Part0Residual.pointSliceCheck 1 3410 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice20 : Part0Residual.pointSliceCheck 1 3410 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice21 : Part0Residual.pointSliceCheck 1 3410 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice22 : Part0Residual.pointSliceCheck 1 3410 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice23 : Part0Residual.pointSliceCheck 1 3410 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice24 : Part0Residual.pointSliceCheck 1 3410 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice25 : Part0Residual.pointSliceCheck 1 3410 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice26 : Part0Residual.pointSliceCheck 1 3410 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice27 : Part0Residual.pointSliceCheck 1 3410 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point200Slice28 : Part0Residual.pointSliceCheck 1 3410 28 := by
  decide +kernel

public theorem point200 : stepCheck 1 3410 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point200Slice0
  · exact point200Slice1
  · exact point200Slice2
  · exact point200Slice3
  · exact point200Slice4
  · exact point200Slice5
  · exact point200Slice6
  · exact point200Slice7
  · exact point200Slice8
  · exact point200Slice9
  · exact point200Slice10
  · exact point200Slice11
  · exact point200Slice12
  · exact point200Slice13
  · exact point200Slice14
  · exact point200Slice15
  · exact point200Slice16
  · exact point200Slice17
  · exact point200Slice18
  · exact point200Slice19
  · exact point200Slice20
  · exact point200Slice21
  · exact point200Slice22
  · exact point200Slice23
  · exact point200Slice24
  · exact point200Slice25
  · exact point200Slice26
  · exact point200Slice27
  · exact point200Slice28

set_option maxHeartbeats 1600000 in
private theorem point201Slice0 : Part0Residual.pointSliceCheck 1 3411 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice1 : Part0Residual.pointSliceCheck 1 3411 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice2 : Part0Residual.pointSliceCheck 1 3411 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice3 : Part0Residual.pointSliceCheck 1 3411 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice4 : Part0Residual.pointSliceCheck 1 3411 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice5 : Part0Residual.pointSliceCheck 1 3411 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice6 : Part0Residual.pointSliceCheck 1 3411 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice7 : Part0Residual.pointSliceCheck 1 3411 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice8 : Part0Residual.pointSliceCheck 1 3411 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice9 : Part0Residual.pointSliceCheck 1 3411 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice10 : Part0Residual.pointSliceCheck 1 3411 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice11 : Part0Residual.pointSliceCheck 1 3411 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice12 : Part0Residual.pointSliceCheck 1 3411 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice13 : Part0Residual.pointSliceCheck 1 3411 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice14 : Part0Residual.pointSliceCheck 1 3411 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice15 : Part0Residual.pointSliceCheck 1 3411 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice16 : Part0Residual.pointSliceCheck 1 3411 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice17 : Part0Residual.pointSliceCheck 1 3411 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice18 : Part0Residual.pointSliceCheck 1 3411 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice19 : Part0Residual.pointSliceCheck 1 3411 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice20 : Part0Residual.pointSliceCheck 1 3411 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice21 : Part0Residual.pointSliceCheck 1 3411 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice22 : Part0Residual.pointSliceCheck 1 3411 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice23 : Part0Residual.pointSliceCheck 1 3411 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice24 : Part0Residual.pointSliceCheck 1 3411 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice25 : Part0Residual.pointSliceCheck 1 3411 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice26 : Part0Residual.pointSliceCheck 1 3411 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice27 : Part0Residual.pointSliceCheck 1 3411 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201Slice28 : Part0Residual.pointSliceCheck 1 3411 28 := by
  decide +kernel

public theorem point201 : stepCheck 1 3411 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point201Slice0
  · exact point201Slice1
  · exact point201Slice2
  · exact point201Slice3
  · exact point201Slice4
  · exact point201Slice5
  · exact point201Slice6
  · exact point201Slice7
  · exact point201Slice8
  · exact point201Slice9
  · exact point201Slice10
  · exact point201Slice11
  · exact point201Slice12
  · exact point201Slice13
  · exact point201Slice14
  · exact point201Slice15
  · exact point201Slice16
  · exact point201Slice17
  · exact point201Slice18
  · exact point201Slice19
  · exact point201Slice20
  · exact point201Slice21
  · exact point201Slice22
  · exact point201Slice23
  · exact point201Slice24
  · exact point201Slice25
  · exact point201Slice26
  · exact point201Slice27
  · exact point201Slice28

set_option maxHeartbeats 1600000 in
private theorem point202Slice0 : Part0Residual.pointSliceCheck 1 3412 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice1 : Part0Residual.pointSliceCheck 1 3412 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice2 : Part0Residual.pointSliceCheck 1 3412 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice3 : Part0Residual.pointSliceCheck 1 3412 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice4 : Part0Residual.pointSliceCheck 1 3412 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice5 : Part0Residual.pointSliceCheck 1 3412 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice6 : Part0Residual.pointSliceCheck 1 3412 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice7 : Part0Residual.pointSliceCheck 1 3412 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice8 : Part0Residual.pointSliceCheck 1 3412 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice9 : Part0Residual.pointSliceCheck 1 3412 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice10 : Part0Residual.pointSliceCheck 1 3412 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice11 : Part0Residual.pointSliceCheck 1 3412 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice12 : Part0Residual.pointSliceCheck 1 3412 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice13 : Part0Residual.pointSliceCheck 1 3412 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice14 : Part0Residual.pointSliceCheck 1 3412 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice15 : Part0Residual.pointSliceCheck 1 3412 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice16 : Part0Residual.pointSliceCheck 1 3412 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice17 : Part0Residual.pointSliceCheck 1 3412 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice18 : Part0Residual.pointSliceCheck 1 3412 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice19 : Part0Residual.pointSliceCheck 1 3412 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice20 : Part0Residual.pointSliceCheck 1 3412 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice21 : Part0Residual.pointSliceCheck 1 3412 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice22 : Part0Residual.pointSliceCheck 1 3412 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice23 : Part0Residual.pointSliceCheck 1 3412 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice24 : Part0Residual.pointSliceCheck 1 3412 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice25 : Part0Residual.pointSliceCheck 1 3412 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice26 : Part0Residual.pointSliceCheck 1 3412 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice27 : Part0Residual.pointSliceCheck 1 3412 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202Slice28 : Part0Residual.pointSliceCheck 1 3412 28 := by
  decide +kernel

public theorem point202 : stepCheck 1 3412 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point202Slice0
  · exact point202Slice1
  · exact point202Slice2
  · exact point202Slice3
  · exact point202Slice4
  · exact point202Slice5
  · exact point202Slice6
  · exact point202Slice7
  · exact point202Slice8
  · exact point202Slice9
  · exact point202Slice10
  · exact point202Slice11
  · exact point202Slice12
  · exact point202Slice13
  · exact point202Slice14
  · exact point202Slice15
  · exact point202Slice16
  · exact point202Slice17
  · exact point202Slice18
  · exact point202Slice19
  · exact point202Slice20
  · exact point202Slice21
  · exact point202Slice22
  · exact point202Slice23
  · exact point202Slice24
  · exact point202Slice25
  · exact point202Slice26
  · exact point202Slice27
  · exact point202Slice28

set_option maxHeartbeats 1600000 in
private theorem point203Slice0 : Part0Residual.pointSliceCheck 1 3415 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice1 : Part0Residual.pointSliceCheck 1 3415 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice2 : Part0Residual.pointSliceCheck 1 3415 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice3 : Part0Residual.pointSliceCheck 1 3415 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice4 : Part0Residual.pointSliceCheck 1 3415 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice5 : Part0Residual.pointSliceCheck 1 3415 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice6 : Part0Residual.pointSliceCheck 1 3415 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice7 : Part0Residual.pointSliceCheck 1 3415 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice8 : Part0Residual.pointSliceCheck 1 3415 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice9 : Part0Residual.pointSliceCheck 1 3415 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice10 : Part0Residual.pointSliceCheck 1 3415 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice11 : Part0Residual.pointSliceCheck 1 3415 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice12 : Part0Residual.pointSliceCheck 1 3415 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice13 : Part0Residual.pointSliceCheck 1 3415 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice14 : Part0Residual.pointSliceCheck 1 3415 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice15 : Part0Residual.pointSliceCheck 1 3415 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice16 : Part0Residual.pointSliceCheck 1 3415 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice17 : Part0Residual.pointSliceCheck 1 3415 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice18 : Part0Residual.pointSliceCheck 1 3415 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice19 : Part0Residual.pointSliceCheck 1 3415 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice20 : Part0Residual.pointSliceCheck 1 3415 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice21 : Part0Residual.pointSliceCheck 1 3415 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice22 : Part0Residual.pointSliceCheck 1 3415 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice23 : Part0Residual.pointSliceCheck 1 3415 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice24 : Part0Residual.pointSliceCheck 1 3415 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice25 : Part0Residual.pointSliceCheck 1 3415 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice26 : Part0Residual.pointSliceCheck 1 3415 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice27 : Part0Residual.pointSliceCheck 1 3415 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203Slice28 : Part0Residual.pointSliceCheck 1 3415 28 := by
  decide +kernel

public theorem point203 : stepCheck 1 3415 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point203Slice0
  · exact point203Slice1
  · exact point203Slice2
  · exact point203Slice3
  · exact point203Slice4
  · exact point203Slice5
  · exact point203Slice6
  · exact point203Slice7
  · exact point203Slice8
  · exact point203Slice9
  · exact point203Slice10
  · exact point203Slice11
  · exact point203Slice12
  · exact point203Slice13
  · exact point203Slice14
  · exact point203Slice15
  · exact point203Slice16
  · exact point203Slice17
  · exact point203Slice18
  · exact point203Slice19
  · exact point203Slice20
  · exact point203Slice21
  · exact point203Slice22
  · exact point203Slice23
  · exact point203Slice24
  · exact point203Slice25
  · exact point203Slice26
  · exact point203Slice27
  · exact point203Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
