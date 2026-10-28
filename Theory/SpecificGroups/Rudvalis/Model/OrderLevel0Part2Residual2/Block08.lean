module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 192–197

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point192Slice0 : Part0Residual.pointSliceCheck 0 3406 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice1 : Part0Residual.pointSliceCheck 0 3406 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice2 : Part0Residual.pointSliceCheck 0 3406 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice3 : Part0Residual.pointSliceCheck 0 3406 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice4 : Part0Residual.pointSliceCheck 0 3406 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice5 : Part0Residual.pointSliceCheck 0 3406 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice6 : Part0Residual.pointSliceCheck 0 3406 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice7 : Part0Residual.pointSliceCheck 0 3406 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice8 : Part0Residual.pointSliceCheck 0 3406 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice9 : Part0Residual.pointSliceCheck 0 3406 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice10 : Part0Residual.pointSliceCheck 0 3406 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice11 : Part0Residual.pointSliceCheck 0 3406 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice12 : Part0Residual.pointSliceCheck 0 3406 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice13 : Part0Residual.pointSliceCheck 0 3406 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice14 : Part0Residual.pointSliceCheck 0 3406 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice15 : Part0Residual.pointSliceCheck 0 3406 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice16 : Part0Residual.pointSliceCheck 0 3406 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice17 : Part0Residual.pointSliceCheck 0 3406 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice18 : Part0Residual.pointSliceCheck 0 3406 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice19 : Part0Residual.pointSliceCheck 0 3406 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice20 : Part0Residual.pointSliceCheck 0 3406 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice21 : Part0Residual.pointSliceCheck 0 3406 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice22 : Part0Residual.pointSliceCheck 0 3406 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice23 : Part0Residual.pointSliceCheck 0 3406 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice24 : Part0Residual.pointSliceCheck 0 3406 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice25 : Part0Residual.pointSliceCheck 0 3406 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice26 : Part0Residual.pointSliceCheck 0 3406 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice27 : Part0Residual.pointSliceCheck 0 3406 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192Slice28 : Part0Residual.pointSliceCheck 0 3406 28 := by
  decide +kernel

public theorem point192 : stepCheck 0 3406 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point192Slice0
  · exact point192Slice1
  · exact point192Slice2
  · exact point192Slice3
  · exact point192Slice4
  · exact point192Slice5
  · exact point192Slice6
  · exact point192Slice7
  · exact point192Slice8
  · exact point192Slice9
  · exact point192Slice10
  · exact point192Slice11
  · exact point192Slice12
  · exact point192Slice13
  · exact point192Slice14
  · exact point192Slice15
  · exact point192Slice16
  · exact point192Slice17
  · exact point192Slice18
  · exact point192Slice19
  · exact point192Slice20
  · exact point192Slice21
  · exact point192Slice22
  · exact point192Slice23
  · exact point192Slice24
  · exact point192Slice25
  · exact point192Slice26
  · exact point192Slice27
  · exact point192Slice28

set_option maxHeartbeats 1600000 in
private theorem point193Slice0 : Part0Residual.pointSliceCheck 0 3407 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice1 : Part0Residual.pointSliceCheck 0 3407 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice2 : Part0Residual.pointSliceCheck 0 3407 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice3 : Part0Residual.pointSliceCheck 0 3407 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice4 : Part0Residual.pointSliceCheck 0 3407 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice5 : Part0Residual.pointSliceCheck 0 3407 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice6 : Part0Residual.pointSliceCheck 0 3407 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice7 : Part0Residual.pointSliceCheck 0 3407 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice8 : Part0Residual.pointSliceCheck 0 3407 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice9 : Part0Residual.pointSliceCheck 0 3407 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice10 : Part0Residual.pointSliceCheck 0 3407 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice11 : Part0Residual.pointSliceCheck 0 3407 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice12 : Part0Residual.pointSliceCheck 0 3407 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice13 : Part0Residual.pointSliceCheck 0 3407 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice14 : Part0Residual.pointSliceCheck 0 3407 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice15 : Part0Residual.pointSliceCheck 0 3407 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice16 : Part0Residual.pointSliceCheck 0 3407 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice17 : Part0Residual.pointSliceCheck 0 3407 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice18 : Part0Residual.pointSliceCheck 0 3407 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice19 : Part0Residual.pointSliceCheck 0 3407 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice20 : Part0Residual.pointSliceCheck 0 3407 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice21 : Part0Residual.pointSliceCheck 0 3407 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice22 : Part0Residual.pointSliceCheck 0 3407 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice23 : Part0Residual.pointSliceCheck 0 3407 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice24 : Part0Residual.pointSliceCheck 0 3407 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice25 : Part0Residual.pointSliceCheck 0 3407 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice26 : Part0Residual.pointSliceCheck 0 3407 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice27 : Part0Residual.pointSliceCheck 0 3407 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point193Slice28 : Part0Residual.pointSliceCheck 0 3407 28 := by
  decide +kernel

public theorem point193 : stepCheck 0 3407 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point193Slice0
  · exact point193Slice1
  · exact point193Slice2
  · exact point193Slice3
  · exact point193Slice4
  · exact point193Slice5
  · exact point193Slice6
  · exact point193Slice7
  · exact point193Slice8
  · exact point193Slice9
  · exact point193Slice10
  · exact point193Slice11
  · exact point193Slice12
  · exact point193Slice13
  · exact point193Slice14
  · exact point193Slice15
  · exact point193Slice16
  · exact point193Slice17
  · exact point193Slice18
  · exact point193Slice19
  · exact point193Slice20
  · exact point193Slice21
  · exact point193Slice22
  · exact point193Slice23
  · exact point193Slice24
  · exact point193Slice25
  · exact point193Slice26
  · exact point193Slice27
  · exact point193Slice28

set_option maxHeartbeats 1600000 in
private theorem point194Slice0 : Part0Residual.pointSliceCheck 0 3410 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice1 : Part0Residual.pointSliceCheck 0 3410 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice2 : Part0Residual.pointSliceCheck 0 3410 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice3 : Part0Residual.pointSliceCheck 0 3410 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice4 : Part0Residual.pointSliceCheck 0 3410 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice5 : Part0Residual.pointSliceCheck 0 3410 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice6 : Part0Residual.pointSliceCheck 0 3410 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice7 : Part0Residual.pointSliceCheck 0 3410 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice8 : Part0Residual.pointSliceCheck 0 3410 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice9 : Part0Residual.pointSliceCheck 0 3410 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice10 : Part0Residual.pointSliceCheck 0 3410 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice11 : Part0Residual.pointSliceCheck 0 3410 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice12 : Part0Residual.pointSliceCheck 0 3410 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice13 : Part0Residual.pointSliceCheck 0 3410 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice14 : Part0Residual.pointSliceCheck 0 3410 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice15 : Part0Residual.pointSliceCheck 0 3410 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice16 : Part0Residual.pointSliceCheck 0 3410 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice17 : Part0Residual.pointSliceCheck 0 3410 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice18 : Part0Residual.pointSliceCheck 0 3410 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice19 : Part0Residual.pointSliceCheck 0 3410 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice20 : Part0Residual.pointSliceCheck 0 3410 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice21 : Part0Residual.pointSliceCheck 0 3410 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice22 : Part0Residual.pointSliceCheck 0 3410 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice23 : Part0Residual.pointSliceCheck 0 3410 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice24 : Part0Residual.pointSliceCheck 0 3410 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice25 : Part0Residual.pointSliceCheck 0 3410 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice26 : Part0Residual.pointSliceCheck 0 3410 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice27 : Part0Residual.pointSliceCheck 0 3410 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point194Slice28 : Part0Residual.pointSliceCheck 0 3410 28 := by
  decide +kernel

public theorem point194 : stepCheck 0 3410 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point194Slice0
  · exact point194Slice1
  · exact point194Slice2
  · exact point194Slice3
  · exact point194Slice4
  · exact point194Slice5
  · exact point194Slice6
  · exact point194Slice7
  · exact point194Slice8
  · exact point194Slice9
  · exact point194Slice10
  · exact point194Slice11
  · exact point194Slice12
  · exact point194Slice13
  · exact point194Slice14
  · exact point194Slice15
  · exact point194Slice16
  · exact point194Slice17
  · exact point194Slice18
  · exact point194Slice19
  · exact point194Slice20
  · exact point194Slice21
  · exact point194Slice22
  · exact point194Slice23
  · exact point194Slice24
  · exact point194Slice25
  · exact point194Slice26
  · exact point194Slice27
  · exact point194Slice28

set_option maxHeartbeats 1600000 in
private theorem point195Slice0 : Part0Residual.pointSliceCheck 0 3413 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice1 : Part0Residual.pointSliceCheck 0 3413 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice2 : Part0Residual.pointSliceCheck 0 3413 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice3 : Part0Residual.pointSliceCheck 0 3413 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice4 : Part0Residual.pointSliceCheck 0 3413 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice5 : Part0Residual.pointSliceCheck 0 3413 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice6 : Part0Residual.pointSliceCheck 0 3413 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice7 : Part0Residual.pointSliceCheck 0 3413 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice8 : Part0Residual.pointSliceCheck 0 3413 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice9 : Part0Residual.pointSliceCheck 0 3413 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice10 : Part0Residual.pointSliceCheck 0 3413 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice11 : Part0Residual.pointSliceCheck 0 3413 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice12 : Part0Residual.pointSliceCheck 0 3413 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice13 : Part0Residual.pointSliceCheck 0 3413 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice14 : Part0Residual.pointSliceCheck 0 3413 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice15 : Part0Residual.pointSliceCheck 0 3413 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice16 : Part0Residual.pointSliceCheck 0 3413 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice17 : Part0Residual.pointSliceCheck 0 3413 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice18 : Part0Residual.pointSliceCheck 0 3413 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice19 : Part0Residual.pointSliceCheck 0 3413 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice20 : Part0Residual.pointSliceCheck 0 3413 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice21 : Part0Residual.pointSliceCheck 0 3413 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice22 : Part0Residual.pointSliceCheck 0 3413 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice23 : Part0Residual.pointSliceCheck 0 3413 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice24 : Part0Residual.pointSliceCheck 0 3413 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice25 : Part0Residual.pointSliceCheck 0 3413 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice26 : Part0Residual.pointSliceCheck 0 3413 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice27 : Part0Residual.pointSliceCheck 0 3413 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195Slice28 : Part0Residual.pointSliceCheck 0 3413 28 := by
  decide +kernel

public theorem point195 : stepCheck 0 3413 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point195Slice0
  · exact point195Slice1
  · exact point195Slice2
  · exact point195Slice3
  · exact point195Slice4
  · exact point195Slice5
  · exact point195Slice6
  · exact point195Slice7
  · exact point195Slice8
  · exact point195Slice9
  · exact point195Slice10
  · exact point195Slice11
  · exact point195Slice12
  · exact point195Slice13
  · exact point195Slice14
  · exact point195Slice15
  · exact point195Slice16
  · exact point195Slice17
  · exact point195Slice18
  · exact point195Slice19
  · exact point195Slice20
  · exact point195Slice21
  · exact point195Slice22
  · exact point195Slice23
  · exact point195Slice24
  · exact point195Slice25
  · exact point195Slice26
  · exact point195Slice27
  · exact point195Slice28

set_option maxHeartbeats 1600000 in
private theorem point196Slice0 : Part0Residual.pointSliceCheck 0 3417 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice1 : Part0Residual.pointSliceCheck 0 3417 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice2 : Part0Residual.pointSliceCheck 0 3417 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice3 : Part0Residual.pointSliceCheck 0 3417 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice4 : Part0Residual.pointSliceCheck 0 3417 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice5 : Part0Residual.pointSliceCheck 0 3417 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice6 : Part0Residual.pointSliceCheck 0 3417 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice7 : Part0Residual.pointSliceCheck 0 3417 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice8 : Part0Residual.pointSliceCheck 0 3417 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice9 : Part0Residual.pointSliceCheck 0 3417 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice10 : Part0Residual.pointSliceCheck 0 3417 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice11 : Part0Residual.pointSliceCheck 0 3417 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice12 : Part0Residual.pointSliceCheck 0 3417 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice13 : Part0Residual.pointSliceCheck 0 3417 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice14 : Part0Residual.pointSliceCheck 0 3417 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice15 : Part0Residual.pointSliceCheck 0 3417 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice16 : Part0Residual.pointSliceCheck 0 3417 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice17 : Part0Residual.pointSliceCheck 0 3417 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice18 : Part0Residual.pointSliceCheck 0 3417 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice19 : Part0Residual.pointSliceCheck 0 3417 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice20 : Part0Residual.pointSliceCheck 0 3417 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice21 : Part0Residual.pointSliceCheck 0 3417 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice22 : Part0Residual.pointSliceCheck 0 3417 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice23 : Part0Residual.pointSliceCheck 0 3417 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice24 : Part0Residual.pointSliceCheck 0 3417 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice25 : Part0Residual.pointSliceCheck 0 3417 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice26 : Part0Residual.pointSliceCheck 0 3417 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice27 : Part0Residual.pointSliceCheck 0 3417 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point196Slice28 : Part0Residual.pointSliceCheck 0 3417 28 := by
  decide +kernel

public theorem point196 : stepCheck 0 3417 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point196Slice0
  · exact point196Slice1
  · exact point196Slice2
  · exact point196Slice3
  · exact point196Slice4
  · exact point196Slice5
  · exact point196Slice6
  · exact point196Slice7
  · exact point196Slice8
  · exact point196Slice9
  · exact point196Slice10
  · exact point196Slice11
  · exact point196Slice12
  · exact point196Slice13
  · exact point196Slice14
  · exact point196Slice15
  · exact point196Slice16
  · exact point196Slice17
  · exact point196Slice18
  · exact point196Slice19
  · exact point196Slice20
  · exact point196Slice21
  · exact point196Slice22
  · exact point196Slice23
  · exact point196Slice24
  · exact point196Slice25
  · exact point196Slice26
  · exact point196Slice27
  · exact point196Slice28

set_option maxHeartbeats 1600000 in
private theorem point197Slice0 : Part0Residual.pointSliceCheck 0 3419 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice1 : Part0Residual.pointSliceCheck 0 3419 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice2 : Part0Residual.pointSliceCheck 0 3419 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice3 : Part0Residual.pointSliceCheck 0 3419 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice4 : Part0Residual.pointSliceCheck 0 3419 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice5 : Part0Residual.pointSliceCheck 0 3419 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice6 : Part0Residual.pointSliceCheck 0 3419 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice7 : Part0Residual.pointSliceCheck 0 3419 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice8 : Part0Residual.pointSliceCheck 0 3419 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice9 : Part0Residual.pointSliceCheck 0 3419 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice10 : Part0Residual.pointSliceCheck 0 3419 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice11 : Part0Residual.pointSliceCheck 0 3419 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice12 : Part0Residual.pointSliceCheck 0 3419 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice13 : Part0Residual.pointSliceCheck 0 3419 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice14 : Part0Residual.pointSliceCheck 0 3419 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice15 : Part0Residual.pointSliceCheck 0 3419 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice16 : Part0Residual.pointSliceCheck 0 3419 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice17 : Part0Residual.pointSliceCheck 0 3419 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice18 : Part0Residual.pointSliceCheck 0 3419 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice19 : Part0Residual.pointSliceCheck 0 3419 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice20 : Part0Residual.pointSliceCheck 0 3419 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice21 : Part0Residual.pointSliceCheck 0 3419 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice22 : Part0Residual.pointSliceCheck 0 3419 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice23 : Part0Residual.pointSliceCheck 0 3419 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice24 : Part0Residual.pointSliceCheck 0 3419 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice25 : Part0Residual.pointSliceCheck 0 3419 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice26 : Part0Residual.pointSliceCheck 0 3419 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice27 : Part0Residual.pointSliceCheck 0 3419 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point197Slice28 : Part0Residual.pointSliceCheck 0 3419 28 := by
  decide +kernel

public theorem point197 : stepCheck 0 3419 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point197Slice0
  · exact point197Slice1
  · exact point197Slice2
  · exact point197Slice3
  · exact point197Slice4
  · exact point197Slice5
  · exact point197Slice6
  · exact point197Slice7
  · exact point197Slice8
  · exact point197Slice9
  · exact point197Slice10
  · exact point197Slice11
  · exact point197Slice12
  · exact point197Slice13
  · exact point197Slice14
  · exact point197Slice15
  · exact point197Slice16
  · exact point197Slice17
  · exact point197Slice18
  · exact point197Slice19
  · exact point197Slice20
  · exact point197Slice21
  · exact point197Slice22
  · exact point197Slice23
  · exact point197Slice24
  · exact point197Slice25
  · exact point197Slice26
  · exact point197Slice27
  · exact point197Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
