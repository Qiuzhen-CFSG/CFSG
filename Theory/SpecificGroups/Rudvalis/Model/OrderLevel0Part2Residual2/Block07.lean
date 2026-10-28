module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 186–191

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point186Slice0 : Part0Residual.pointSliceCheck 1 3269 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice1 : Part0Residual.pointSliceCheck 1 3269 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice2 : Part0Residual.pointSliceCheck 1 3269 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice3 : Part0Residual.pointSliceCheck 1 3269 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice4 : Part0Residual.pointSliceCheck 1 3269 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice5 : Part0Residual.pointSliceCheck 1 3269 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice6 : Part0Residual.pointSliceCheck 1 3269 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice7 : Part0Residual.pointSliceCheck 1 3269 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice8 : Part0Residual.pointSliceCheck 1 3269 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice9 : Part0Residual.pointSliceCheck 1 3269 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice10 : Part0Residual.pointSliceCheck 1 3269 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice11 : Part0Residual.pointSliceCheck 1 3269 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice12 : Part0Residual.pointSliceCheck 1 3269 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice13 : Part0Residual.pointSliceCheck 1 3269 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice14 : Part0Residual.pointSliceCheck 1 3269 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice15 : Part0Residual.pointSliceCheck 1 3269 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice16 : Part0Residual.pointSliceCheck 1 3269 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice17 : Part0Residual.pointSliceCheck 1 3269 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice18 : Part0Residual.pointSliceCheck 1 3269 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice19 : Part0Residual.pointSliceCheck 1 3269 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice20 : Part0Residual.pointSliceCheck 1 3269 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice21 : Part0Residual.pointSliceCheck 1 3269 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice22 : Part0Residual.pointSliceCheck 1 3269 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice23 : Part0Residual.pointSliceCheck 1 3269 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice24 : Part0Residual.pointSliceCheck 1 3269 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice25 : Part0Residual.pointSliceCheck 1 3269 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice26 : Part0Residual.pointSliceCheck 1 3269 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice27 : Part0Residual.pointSliceCheck 1 3269 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point186Slice28 : Part0Residual.pointSliceCheck 1 3269 28 := by
  decide +kernel

public theorem point186 : stepCheck 1 3269 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point186Slice0
  · exact point186Slice1
  · exact point186Slice2
  · exact point186Slice3
  · exact point186Slice4
  · exact point186Slice5
  · exact point186Slice6
  · exact point186Slice7
  · exact point186Slice8
  · exact point186Slice9
  · exact point186Slice10
  · exact point186Slice11
  · exact point186Slice12
  · exact point186Slice13
  · exact point186Slice14
  · exact point186Slice15
  · exact point186Slice16
  · exact point186Slice17
  · exact point186Slice18
  · exact point186Slice19
  · exact point186Slice20
  · exact point186Slice21
  · exact point186Slice22
  · exact point186Slice23
  · exact point186Slice24
  · exact point186Slice25
  · exact point186Slice26
  · exact point186Slice27
  · exact point186Slice28

set_option maxHeartbeats 1600000 in
private theorem point187Slice0 : Part0Residual.pointSliceCheck 1 3270 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice1 : Part0Residual.pointSliceCheck 1 3270 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice2 : Part0Residual.pointSliceCheck 1 3270 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice3 : Part0Residual.pointSliceCheck 1 3270 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice4 : Part0Residual.pointSliceCheck 1 3270 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice5 : Part0Residual.pointSliceCheck 1 3270 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice6 : Part0Residual.pointSliceCheck 1 3270 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice7 : Part0Residual.pointSliceCheck 1 3270 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice8 : Part0Residual.pointSliceCheck 1 3270 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice9 : Part0Residual.pointSliceCheck 1 3270 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice10 : Part0Residual.pointSliceCheck 1 3270 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice11 : Part0Residual.pointSliceCheck 1 3270 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice12 : Part0Residual.pointSliceCheck 1 3270 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice13 : Part0Residual.pointSliceCheck 1 3270 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice14 : Part0Residual.pointSliceCheck 1 3270 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice15 : Part0Residual.pointSliceCheck 1 3270 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice16 : Part0Residual.pointSliceCheck 1 3270 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice17 : Part0Residual.pointSliceCheck 1 3270 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice18 : Part0Residual.pointSliceCheck 1 3270 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice19 : Part0Residual.pointSliceCheck 1 3270 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice20 : Part0Residual.pointSliceCheck 1 3270 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice21 : Part0Residual.pointSliceCheck 1 3270 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice22 : Part0Residual.pointSliceCheck 1 3270 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice23 : Part0Residual.pointSliceCheck 1 3270 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice24 : Part0Residual.pointSliceCheck 1 3270 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice25 : Part0Residual.pointSliceCheck 1 3270 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice26 : Part0Residual.pointSliceCheck 1 3270 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice27 : Part0Residual.pointSliceCheck 1 3270 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point187Slice28 : Part0Residual.pointSliceCheck 1 3270 28 := by
  decide +kernel

public theorem point187 : stepCheck 1 3270 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point187Slice0
  · exact point187Slice1
  · exact point187Slice2
  · exact point187Slice3
  · exact point187Slice4
  · exact point187Slice5
  · exact point187Slice6
  · exact point187Slice7
  · exact point187Slice8
  · exact point187Slice9
  · exact point187Slice10
  · exact point187Slice11
  · exact point187Slice12
  · exact point187Slice13
  · exact point187Slice14
  · exact point187Slice15
  · exact point187Slice16
  · exact point187Slice17
  · exact point187Slice18
  · exact point187Slice19
  · exact point187Slice20
  · exact point187Slice21
  · exact point187Slice22
  · exact point187Slice23
  · exact point187Slice24
  · exact point187Slice25
  · exact point187Slice26
  · exact point187Slice27
  · exact point187Slice28

set_option maxHeartbeats 1600000 in
private theorem point188Slice0 : Part0Residual.pointSliceCheck 1 3272 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice1 : Part0Residual.pointSliceCheck 1 3272 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice2 : Part0Residual.pointSliceCheck 1 3272 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice3 : Part0Residual.pointSliceCheck 1 3272 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice4 : Part0Residual.pointSliceCheck 1 3272 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice5 : Part0Residual.pointSliceCheck 1 3272 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice6 : Part0Residual.pointSliceCheck 1 3272 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice7 : Part0Residual.pointSliceCheck 1 3272 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice8 : Part0Residual.pointSliceCheck 1 3272 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice9 : Part0Residual.pointSliceCheck 1 3272 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice10 : Part0Residual.pointSliceCheck 1 3272 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice11 : Part0Residual.pointSliceCheck 1 3272 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice12 : Part0Residual.pointSliceCheck 1 3272 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice13 : Part0Residual.pointSliceCheck 1 3272 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice14 : Part0Residual.pointSliceCheck 1 3272 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice15 : Part0Residual.pointSliceCheck 1 3272 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice16 : Part0Residual.pointSliceCheck 1 3272 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice17 : Part0Residual.pointSliceCheck 1 3272 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice18 : Part0Residual.pointSliceCheck 1 3272 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice19 : Part0Residual.pointSliceCheck 1 3272 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice20 : Part0Residual.pointSliceCheck 1 3272 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice21 : Part0Residual.pointSliceCheck 1 3272 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice22 : Part0Residual.pointSliceCheck 1 3272 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice23 : Part0Residual.pointSliceCheck 1 3272 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice24 : Part0Residual.pointSliceCheck 1 3272 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice25 : Part0Residual.pointSliceCheck 1 3272 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice26 : Part0Residual.pointSliceCheck 1 3272 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice27 : Part0Residual.pointSliceCheck 1 3272 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point188Slice28 : Part0Residual.pointSliceCheck 1 3272 28 := by
  decide +kernel

public theorem point188 : stepCheck 1 3272 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point188Slice0
  · exact point188Slice1
  · exact point188Slice2
  · exact point188Slice3
  · exact point188Slice4
  · exact point188Slice5
  · exact point188Slice6
  · exact point188Slice7
  · exact point188Slice8
  · exact point188Slice9
  · exact point188Slice10
  · exact point188Slice11
  · exact point188Slice12
  · exact point188Slice13
  · exact point188Slice14
  · exact point188Slice15
  · exact point188Slice16
  · exact point188Slice17
  · exact point188Slice18
  · exact point188Slice19
  · exact point188Slice20
  · exact point188Slice21
  · exact point188Slice22
  · exact point188Slice23
  · exact point188Slice24
  · exact point188Slice25
  · exact point188Slice26
  · exact point188Slice27
  · exact point188Slice28

set_option maxHeartbeats 1600000 in
private theorem point189Slice0 : Part0Residual.pointSliceCheck 1 3275 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice1 : Part0Residual.pointSliceCheck 1 3275 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice2 : Part0Residual.pointSliceCheck 1 3275 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice3 : Part0Residual.pointSliceCheck 1 3275 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice4 : Part0Residual.pointSliceCheck 1 3275 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice5 : Part0Residual.pointSliceCheck 1 3275 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice6 : Part0Residual.pointSliceCheck 1 3275 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice7 : Part0Residual.pointSliceCheck 1 3275 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice8 : Part0Residual.pointSliceCheck 1 3275 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice9 : Part0Residual.pointSliceCheck 1 3275 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice10 : Part0Residual.pointSliceCheck 1 3275 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice11 : Part0Residual.pointSliceCheck 1 3275 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice12 : Part0Residual.pointSliceCheck 1 3275 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice13 : Part0Residual.pointSliceCheck 1 3275 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice14 : Part0Residual.pointSliceCheck 1 3275 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice15 : Part0Residual.pointSliceCheck 1 3275 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice16 : Part0Residual.pointSliceCheck 1 3275 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice17 : Part0Residual.pointSliceCheck 1 3275 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice18 : Part0Residual.pointSliceCheck 1 3275 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice19 : Part0Residual.pointSliceCheck 1 3275 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice20 : Part0Residual.pointSliceCheck 1 3275 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice21 : Part0Residual.pointSliceCheck 1 3275 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice22 : Part0Residual.pointSliceCheck 1 3275 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice23 : Part0Residual.pointSliceCheck 1 3275 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice24 : Part0Residual.pointSliceCheck 1 3275 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice25 : Part0Residual.pointSliceCheck 1 3275 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice26 : Part0Residual.pointSliceCheck 1 3275 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice27 : Part0Residual.pointSliceCheck 1 3275 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point189Slice28 : Part0Residual.pointSliceCheck 1 3275 28 := by
  decide +kernel

public theorem point189 : stepCheck 1 3275 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point189Slice0
  · exact point189Slice1
  · exact point189Slice2
  · exact point189Slice3
  · exact point189Slice4
  · exact point189Slice5
  · exact point189Slice6
  · exact point189Slice7
  · exact point189Slice8
  · exact point189Slice9
  · exact point189Slice10
  · exact point189Slice11
  · exact point189Slice12
  · exact point189Slice13
  · exact point189Slice14
  · exact point189Slice15
  · exact point189Slice16
  · exact point189Slice17
  · exact point189Slice18
  · exact point189Slice19
  · exact point189Slice20
  · exact point189Slice21
  · exact point189Slice22
  · exact point189Slice23
  · exact point189Slice24
  · exact point189Slice25
  · exact point189Slice26
  · exact point189Slice27
  · exact point189Slice28

set_option maxHeartbeats 1600000 in
private theorem point190Slice0 : Part0Residual.pointSliceCheck 0 3400 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice1 : Part0Residual.pointSliceCheck 0 3400 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice2 : Part0Residual.pointSliceCheck 0 3400 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice3 : Part0Residual.pointSliceCheck 0 3400 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice4 : Part0Residual.pointSliceCheck 0 3400 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice5 : Part0Residual.pointSliceCheck 0 3400 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice6 : Part0Residual.pointSliceCheck 0 3400 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice7 : Part0Residual.pointSliceCheck 0 3400 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice8 : Part0Residual.pointSliceCheck 0 3400 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice9 : Part0Residual.pointSliceCheck 0 3400 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice10 : Part0Residual.pointSliceCheck 0 3400 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice11 : Part0Residual.pointSliceCheck 0 3400 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice12 : Part0Residual.pointSliceCheck 0 3400 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice13 : Part0Residual.pointSliceCheck 0 3400 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice14 : Part0Residual.pointSliceCheck 0 3400 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice15 : Part0Residual.pointSliceCheck 0 3400 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice16 : Part0Residual.pointSliceCheck 0 3400 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice17 : Part0Residual.pointSliceCheck 0 3400 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice18 : Part0Residual.pointSliceCheck 0 3400 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice19 : Part0Residual.pointSliceCheck 0 3400 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice20 : Part0Residual.pointSliceCheck 0 3400 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice21 : Part0Residual.pointSliceCheck 0 3400 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice22 : Part0Residual.pointSliceCheck 0 3400 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice23 : Part0Residual.pointSliceCheck 0 3400 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice24 : Part0Residual.pointSliceCheck 0 3400 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice25 : Part0Residual.pointSliceCheck 0 3400 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice26 : Part0Residual.pointSliceCheck 0 3400 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice27 : Part0Residual.pointSliceCheck 0 3400 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point190Slice28 : Part0Residual.pointSliceCheck 0 3400 28 := by
  decide +kernel

public theorem point190 : stepCheck 0 3400 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point190Slice0
  · exact point190Slice1
  · exact point190Slice2
  · exact point190Slice3
  · exact point190Slice4
  · exact point190Slice5
  · exact point190Slice6
  · exact point190Slice7
  · exact point190Slice8
  · exact point190Slice9
  · exact point190Slice10
  · exact point190Slice11
  · exact point190Slice12
  · exact point190Slice13
  · exact point190Slice14
  · exact point190Slice15
  · exact point190Slice16
  · exact point190Slice17
  · exact point190Slice18
  · exact point190Slice19
  · exact point190Slice20
  · exact point190Slice21
  · exact point190Slice22
  · exact point190Slice23
  · exact point190Slice24
  · exact point190Slice25
  · exact point190Slice26
  · exact point190Slice27
  · exact point190Slice28

set_option maxHeartbeats 1600000 in
private theorem point191Slice0 : Part0Residual.pointSliceCheck 0 3403 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice1 : Part0Residual.pointSliceCheck 0 3403 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice2 : Part0Residual.pointSliceCheck 0 3403 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice3 : Part0Residual.pointSliceCheck 0 3403 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice4 : Part0Residual.pointSliceCheck 0 3403 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice5 : Part0Residual.pointSliceCheck 0 3403 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice6 : Part0Residual.pointSliceCheck 0 3403 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice7 : Part0Residual.pointSliceCheck 0 3403 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice8 : Part0Residual.pointSliceCheck 0 3403 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice9 : Part0Residual.pointSliceCheck 0 3403 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice10 : Part0Residual.pointSliceCheck 0 3403 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice11 : Part0Residual.pointSliceCheck 0 3403 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice12 : Part0Residual.pointSliceCheck 0 3403 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice13 : Part0Residual.pointSliceCheck 0 3403 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice14 : Part0Residual.pointSliceCheck 0 3403 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice15 : Part0Residual.pointSliceCheck 0 3403 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice16 : Part0Residual.pointSliceCheck 0 3403 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice17 : Part0Residual.pointSliceCheck 0 3403 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice18 : Part0Residual.pointSliceCheck 0 3403 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice19 : Part0Residual.pointSliceCheck 0 3403 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice20 : Part0Residual.pointSliceCheck 0 3403 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice21 : Part0Residual.pointSliceCheck 0 3403 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice22 : Part0Residual.pointSliceCheck 0 3403 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice23 : Part0Residual.pointSliceCheck 0 3403 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice24 : Part0Residual.pointSliceCheck 0 3403 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice25 : Part0Residual.pointSliceCheck 0 3403 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice26 : Part0Residual.pointSliceCheck 0 3403 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice27 : Part0Residual.pointSliceCheck 0 3403 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point191Slice28 : Part0Residual.pointSliceCheck 0 3403 28 := by
  decide +kernel

public theorem point191 : stepCheck 0 3403 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point191Slice0
  · exact point191Slice1
  · exact point191Slice2
  · exact point191Slice3
  · exact point191Slice4
  · exact point191Slice5
  · exact point191Slice6
  · exact point191Slice7
  · exact point191Slice8
  · exact point191Slice9
  · exact point191Slice10
  · exact point191Slice11
  · exact point191Slice12
  · exact point191Slice13
  · exact point191Slice14
  · exact point191Slice15
  · exact point191Slice16
  · exact point191Slice17
  · exact point191Slice18
  · exact point191Slice19
  · exact point191Slice20
  · exact point191Slice21
  · exact point191Slice22
  · exact point191Slice23
  · exact point191Slice24
  · exact point191Slice25
  · exact point191Slice26
  · exact point191Slice27
  · exact point191Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
