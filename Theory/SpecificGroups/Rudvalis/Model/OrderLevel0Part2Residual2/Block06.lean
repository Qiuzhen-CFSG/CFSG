module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 180–185

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point180Slice0 : Part0Residual.pointSliceCheck 0 3276 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice1 : Part0Residual.pointSliceCheck 0 3276 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice2 : Part0Residual.pointSliceCheck 0 3276 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice3 : Part0Residual.pointSliceCheck 0 3276 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice4 : Part0Residual.pointSliceCheck 0 3276 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice5 : Part0Residual.pointSliceCheck 0 3276 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice6 : Part0Residual.pointSliceCheck 0 3276 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice7 : Part0Residual.pointSliceCheck 0 3276 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice8 : Part0Residual.pointSliceCheck 0 3276 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice9 : Part0Residual.pointSliceCheck 0 3276 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice10 : Part0Residual.pointSliceCheck 0 3276 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice11 : Part0Residual.pointSliceCheck 0 3276 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice12 : Part0Residual.pointSliceCheck 0 3276 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice13 : Part0Residual.pointSliceCheck 0 3276 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice14 : Part0Residual.pointSliceCheck 0 3276 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice15 : Part0Residual.pointSliceCheck 0 3276 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice16 : Part0Residual.pointSliceCheck 0 3276 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice17 : Part0Residual.pointSliceCheck 0 3276 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice18 : Part0Residual.pointSliceCheck 0 3276 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice19 : Part0Residual.pointSliceCheck 0 3276 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice20 : Part0Residual.pointSliceCheck 0 3276 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice21 : Part0Residual.pointSliceCheck 0 3276 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice22 : Part0Residual.pointSliceCheck 0 3276 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice23 : Part0Residual.pointSliceCheck 0 3276 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice24 : Part0Residual.pointSliceCheck 0 3276 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice25 : Part0Residual.pointSliceCheck 0 3276 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice26 : Part0Residual.pointSliceCheck 0 3276 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice27 : Part0Residual.pointSliceCheck 0 3276 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point180Slice28 : Part0Residual.pointSliceCheck 0 3276 28 := by
  decide +kernel

public theorem point180 : stepCheck 0 3276 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point180Slice0
  · exact point180Slice1
  · exact point180Slice2
  · exact point180Slice3
  · exact point180Slice4
  · exact point180Slice5
  · exact point180Slice6
  · exact point180Slice7
  · exact point180Slice8
  · exact point180Slice9
  · exact point180Slice10
  · exact point180Slice11
  · exact point180Slice12
  · exact point180Slice13
  · exact point180Slice14
  · exact point180Slice15
  · exact point180Slice16
  · exact point180Slice17
  · exact point180Slice18
  · exact point180Slice19
  · exact point180Slice20
  · exact point180Slice21
  · exact point180Slice22
  · exact point180Slice23
  · exact point180Slice24
  · exact point180Slice25
  · exact point180Slice26
  · exact point180Slice27
  · exact point180Slice28

set_option maxHeartbeats 1600000 in
private theorem point181Slice0 : Part0Residual.pointSliceCheck 0 3277 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice1 : Part0Residual.pointSliceCheck 0 3277 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice2 : Part0Residual.pointSliceCheck 0 3277 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice3 : Part0Residual.pointSliceCheck 0 3277 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice4 : Part0Residual.pointSliceCheck 0 3277 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice5 : Part0Residual.pointSliceCheck 0 3277 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice6 : Part0Residual.pointSliceCheck 0 3277 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice7 : Part0Residual.pointSliceCheck 0 3277 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice8 : Part0Residual.pointSliceCheck 0 3277 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice9 : Part0Residual.pointSliceCheck 0 3277 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice10 : Part0Residual.pointSliceCheck 0 3277 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice11 : Part0Residual.pointSliceCheck 0 3277 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice12 : Part0Residual.pointSliceCheck 0 3277 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice13 : Part0Residual.pointSliceCheck 0 3277 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice14 : Part0Residual.pointSliceCheck 0 3277 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice15 : Part0Residual.pointSliceCheck 0 3277 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice16 : Part0Residual.pointSliceCheck 0 3277 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice17 : Part0Residual.pointSliceCheck 0 3277 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice18 : Part0Residual.pointSliceCheck 0 3277 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice19 : Part0Residual.pointSliceCheck 0 3277 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice20 : Part0Residual.pointSliceCheck 0 3277 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice21 : Part0Residual.pointSliceCheck 0 3277 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice22 : Part0Residual.pointSliceCheck 0 3277 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice23 : Part0Residual.pointSliceCheck 0 3277 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice24 : Part0Residual.pointSliceCheck 0 3277 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice25 : Part0Residual.pointSliceCheck 0 3277 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice26 : Part0Residual.pointSliceCheck 0 3277 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice27 : Part0Residual.pointSliceCheck 0 3277 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point181Slice28 : Part0Residual.pointSliceCheck 0 3277 28 := by
  decide +kernel

public theorem point181 : stepCheck 0 3277 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point181Slice0
  · exact point181Slice1
  · exact point181Slice2
  · exact point181Slice3
  · exact point181Slice4
  · exact point181Slice5
  · exact point181Slice6
  · exact point181Slice7
  · exact point181Slice8
  · exact point181Slice9
  · exact point181Slice10
  · exact point181Slice11
  · exact point181Slice12
  · exact point181Slice13
  · exact point181Slice14
  · exact point181Slice15
  · exact point181Slice16
  · exact point181Slice17
  · exact point181Slice18
  · exact point181Slice19
  · exact point181Slice20
  · exact point181Slice21
  · exact point181Slice22
  · exact point181Slice23
  · exact point181Slice24
  · exact point181Slice25
  · exact point181Slice26
  · exact point181Slice27
  · exact point181Slice28

set_option maxHeartbeats 1600000 in
private theorem point182Slice0 : Part0Residual.pointSliceCheck 0 3279 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice1 : Part0Residual.pointSliceCheck 0 3279 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice2 : Part0Residual.pointSliceCheck 0 3279 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice3 : Part0Residual.pointSliceCheck 0 3279 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice4 : Part0Residual.pointSliceCheck 0 3279 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice5 : Part0Residual.pointSliceCheck 0 3279 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice6 : Part0Residual.pointSliceCheck 0 3279 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice7 : Part0Residual.pointSliceCheck 0 3279 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice8 : Part0Residual.pointSliceCheck 0 3279 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice9 : Part0Residual.pointSliceCheck 0 3279 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice10 : Part0Residual.pointSliceCheck 0 3279 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice11 : Part0Residual.pointSliceCheck 0 3279 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice12 : Part0Residual.pointSliceCheck 0 3279 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice13 : Part0Residual.pointSliceCheck 0 3279 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice14 : Part0Residual.pointSliceCheck 0 3279 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice15 : Part0Residual.pointSliceCheck 0 3279 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice16 : Part0Residual.pointSliceCheck 0 3279 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice17 : Part0Residual.pointSliceCheck 0 3279 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice18 : Part0Residual.pointSliceCheck 0 3279 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice19 : Part0Residual.pointSliceCheck 0 3279 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice20 : Part0Residual.pointSliceCheck 0 3279 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice21 : Part0Residual.pointSliceCheck 0 3279 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice22 : Part0Residual.pointSliceCheck 0 3279 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice23 : Part0Residual.pointSliceCheck 0 3279 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice24 : Part0Residual.pointSliceCheck 0 3279 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice25 : Part0Residual.pointSliceCheck 0 3279 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice26 : Part0Residual.pointSliceCheck 0 3279 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice27 : Part0Residual.pointSliceCheck 0 3279 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point182Slice28 : Part0Residual.pointSliceCheck 0 3279 28 := by
  decide +kernel

public theorem point182 : stepCheck 0 3279 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point182Slice0
  · exact point182Slice1
  · exact point182Slice2
  · exact point182Slice3
  · exact point182Slice4
  · exact point182Slice5
  · exact point182Slice6
  · exact point182Slice7
  · exact point182Slice8
  · exact point182Slice9
  · exact point182Slice10
  · exact point182Slice11
  · exact point182Slice12
  · exact point182Slice13
  · exact point182Slice14
  · exact point182Slice15
  · exact point182Slice16
  · exact point182Slice17
  · exact point182Slice18
  · exact point182Slice19
  · exact point182Slice20
  · exact point182Slice21
  · exact point182Slice22
  · exact point182Slice23
  · exact point182Slice24
  · exact point182Slice25
  · exact point182Slice26
  · exact point182Slice27
  · exact point182Slice28

set_option maxHeartbeats 1600000 in
private theorem point183Slice0 : Part0Residual.pointSliceCheck 1 3260 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice1 : Part0Residual.pointSliceCheck 1 3260 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice2 : Part0Residual.pointSliceCheck 1 3260 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice3 : Part0Residual.pointSliceCheck 1 3260 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice4 : Part0Residual.pointSliceCheck 1 3260 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice5 : Part0Residual.pointSliceCheck 1 3260 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice6 : Part0Residual.pointSliceCheck 1 3260 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice7 : Part0Residual.pointSliceCheck 1 3260 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice8 : Part0Residual.pointSliceCheck 1 3260 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice9 : Part0Residual.pointSliceCheck 1 3260 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice10 : Part0Residual.pointSliceCheck 1 3260 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice11 : Part0Residual.pointSliceCheck 1 3260 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice12 : Part0Residual.pointSliceCheck 1 3260 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice13 : Part0Residual.pointSliceCheck 1 3260 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice14 : Part0Residual.pointSliceCheck 1 3260 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice15 : Part0Residual.pointSliceCheck 1 3260 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice16 : Part0Residual.pointSliceCheck 1 3260 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice17 : Part0Residual.pointSliceCheck 1 3260 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice18 : Part0Residual.pointSliceCheck 1 3260 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice19 : Part0Residual.pointSliceCheck 1 3260 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice20 : Part0Residual.pointSliceCheck 1 3260 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice21 : Part0Residual.pointSliceCheck 1 3260 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice22 : Part0Residual.pointSliceCheck 1 3260 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice23 : Part0Residual.pointSliceCheck 1 3260 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice24 : Part0Residual.pointSliceCheck 1 3260 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice25 : Part0Residual.pointSliceCheck 1 3260 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice26 : Part0Residual.pointSliceCheck 1 3260 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice27 : Part0Residual.pointSliceCheck 1 3260 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point183Slice28 : Part0Residual.pointSliceCheck 1 3260 28 := by
  decide +kernel

public theorem point183 : stepCheck 1 3260 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point183Slice0
  · exact point183Slice1
  · exact point183Slice2
  · exact point183Slice3
  · exact point183Slice4
  · exact point183Slice5
  · exact point183Slice6
  · exact point183Slice7
  · exact point183Slice8
  · exact point183Slice9
  · exact point183Slice10
  · exact point183Slice11
  · exact point183Slice12
  · exact point183Slice13
  · exact point183Slice14
  · exact point183Slice15
  · exact point183Slice16
  · exact point183Slice17
  · exact point183Slice18
  · exact point183Slice19
  · exact point183Slice20
  · exact point183Slice21
  · exact point183Slice22
  · exact point183Slice23
  · exact point183Slice24
  · exact point183Slice25
  · exact point183Slice26
  · exact point183Slice27
  · exact point183Slice28

set_option maxHeartbeats 1600000 in
private theorem point184Slice0 : Part0Residual.pointSliceCheck 1 3263 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice1 : Part0Residual.pointSliceCheck 1 3263 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice2 : Part0Residual.pointSliceCheck 1 3263 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice3 : Part0Residual.pointSliceCheck 1 3263 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice4 : Part0Residual.pointSliceCheck 1 3263 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice5 : Part0Residual.pointSliceCheck 1 3263 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice6 : Part0Residual.pointSliceCheck 1 3263 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice7 : Part0Residual.pointSliceCheck 1 3263 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice8 : Part0Residual.pointSliceCheck 1 3263 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice9 : Part0Residual.pointSliceCheck 1 3263 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice10 : Part0Residual.pointSliceCheck 1 3263 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice11 : Part0Residual.pointSliceCheck 1 3263 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice12 : Part0Residual.pointSliceCheck 1 3263 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice13 : Part0Residual.pointSliceCheck 1 3263 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice14 : Part0Residual.pointSliceCheck 1 3263 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice15 : Part0Residual.pointSliceCheck 1 3263 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice16 : Part0Residual.pointSliceCheck 1 3263 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice17 : Part0Residual.pointSliceCheck 1 3263 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice18 : Part0Residual.pointSliceCheck 1 3263 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice19 : Part0Residual.pointSliceCheck 1 3263 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice20 : Part0Residual.pointSliceCheck 1 3263 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice21 : Part0Residual.pointSliceCheck 1 3263 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice22 : Part0Residual.pointSliceCheck 1 3263 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice23 : Part0Residual.pointSliceCheck 1 3263 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice24 : Part0Residual.pointSliceCheck 1 3263 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice25 : Part0Residual.pointSliceCheck 1 3263 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice26 : Part0Residual.pointSliceCheck 1 3263 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice27 : Part0Residual.pointSliceCheck 1 3263 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point184Slice28 : Part0Residual.pointSliceCheck 1 3263 28 := by
  decide +kernel

public theorem point184 : stepCheck 1 3263 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point184Slice0
  · exact point184Slice1
  · exact point184Slice2
  · exact point184Slice3
  · exact point184Slice4
  · exact point184Slice5
  · exact point184Slice6
  · exact point184Slice7
  · exact point184Slice8
  · exact point184Slice9
  · exact point184Slice10
  · exact point184Slice11
  · exact point184Slice12
  · exact point184Slice13
  · exact point184Slice14
  · exact point184Slice15
  · exact point184Slice16
  · exact point184Slice17
  · exact point184Slice18
  · exact point184Slice19
  · exact point184Slice20
  · exact point184Slice21
  · exact point184Slice22
  · exact point184Slice23
  · exact point184Slice24
  · exact point184Slice25
  · exact point184Slice26
  · exact point184Slice27
  · exact point184Slice28

set_option maxHeartbeats 1600000 in
private theorem point185Slice0 : Part0Residual.pointSliceCheck 1 3266 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice1 : Part0Residual.pointSliceCheck 1 3266 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice2 : Part0Residual.pointSliceCheck 1 3266 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice3 : Part0Residual.pointSliceCheck 1 3266 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice4 : Part0Residual.pointSliceCheck 1 3266 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice5 : Part0Residual.pointSliceCheck 1 3266 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice6 : Part0Residual.pointSliceCheck 1 3266 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice7 : Part0Residual.pointSliceCheck 1 3266 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice8 : Part0Residual.pointSliceCheck 1 3266 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice9 : Part0Residual.pointSliceCheck 1 3266 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice10 : Part0Residual.pointSliceCheck 1 3266 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice11 : Part0Residual.pointSliceCheck 1 3266 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice12 : Part0Residual.pointSliceCheck 1 3266 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice13 : Part0Residual.pointSliceCheck 1 3266 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice14 : Part0Residual.pointSliceCheck 1 3266 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice15 : Part0Residual.pointSliceCheck 1 3266 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice16 : Part0Residual.pointSliceCheck 1 3266 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice17 : Part0Residual.pointSliceCheck 1 3266 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice18 : Part0Residual.pointSliceCheck 1 3266 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice19 : Part0Residual.pointSliceCheck 1 3266 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice20 : Part0Residual.pointSliceCheck 1 3266 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice21 : Part0Residual.pointSliceCheck 1 3266 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice22 : Part0Residual.pointSliceCheck 1 3266 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice23 : Part0Residual.pointSliceCheck 1 3266 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice24 : Part0Residual.pointSliceCheck 1 3266 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice25 : Part0Residual.pointSliceCheck 1 3266 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice26 : Part0Residual.pointSliceCheck 1 3266 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice27 : Part0Residual.pointSliceCheck 1 3266 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point185Slice28 : Part0Residual.pointSliceCheck 1 3266 28 := by
  decide +kernel

public theorem point185 : stepCheck 1 3266 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point185Slice0
  · exact point185Slice1
  · exact point185Slice2
  · exact point185Slice3
  · exact point185Slice4
  · exact point185Slice5
  · exact point185Slice6
  · exact point185Slice7
  · exact point185Slice8
  · exact point185Slice9
  · exact point185Slice10
  · exact point185Slice11
  · exact point185Slice12
  · exact point185Slice13
  · exact point185Slice14
  · exact point185Slice15
  · exact point185Slice16
  · exact point185Slice17
  · exact point185Slice18
  · exact point185Slice19
  · exact point185Slice20
  · exact point185Slice21
  · exact point185Slice22
  · exact point185Slice23
  · exact point185Slice24
  · exact point185Slice25
  · exact point185Slice26
  · exact point185Slice27
  · exact point185Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
