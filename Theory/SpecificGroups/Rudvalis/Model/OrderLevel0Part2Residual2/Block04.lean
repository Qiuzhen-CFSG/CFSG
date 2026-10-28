module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 168–173

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point168Slice0 : Part0Residual.pointSliceCheck 1 3129 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice1 : Part0Residual.pointSliceCheck 1 3129 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice2 : Part0Residual.pointSliceCheck 1 3129 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice3 : Part0Residual.pointSliceCheck 1 3129 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice4 : Part0Residual.pointSliceCheck 1 3129 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice5 : Part0Residual.pointSliceCheck 1 3129 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice6 : Part0Residual.pointSliceCheck 1 3129 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice7 : Part0Residual.pointSliceCheck 1 3129 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice8 : Part0Residual.pointSliceCheck 1 3129 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice9 : Part0Residual.pointSliceCheck 1 3129 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice10 : Part0Residual.pointSliceCheck 1 3129 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice11 : Part0Residual.pointSliceCheck 1 3129 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice12 : Part0Residual.pointSliceCheck 1 3129 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice13 : Part0Residual.pointSliceCheck 1 3129 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice14 : Part0Residual.pointSliceCheck 1 3129 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice15 : Part0Residual.pointSliceCheck 1 3129 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice16 : Part0Residual.pointSliceCheck 1 3129 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice17 : Part0Residual.pointSliceCheck 1 3129 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice18 : Part0Residual.pointSliceCheck 1 3129 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice19 : Part0Residual.pointSliceCheck 1 3129 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice20 : Part0Residual.pointSliceCheck 1 3129 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice21 : Part0Residual.pointSliceCheck 1 3129 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice22 : Part0Residual.pointSliceCheck 1 3129 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice23 : Part0Residual.pointSliceCheck 1 3129 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice24 : Part0Residual.pointSliceCheck 1 3129 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice25 : Part0Residual.pointSliceCheck 1 3129 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice26 : Part0Residual.pointSliceCheck 1 3129 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice27 : Part0Residual.pointSliceCheck 1 3129 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point168Slice28 : Part0Residual.pointSliceCheck 1 3129 28 := by
  decide +kernel

public theorem point168 : stepCheck 1 3129 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point168Slice0
  · exact point168Slice1
  · exact point168Slice2
  · exact point168Slice3
  · exact point168Slice4
  · exact point168Slice5
  · exact point168Slice6
  · exact point168Slice7
  · exact point168Slice8
  · exact point168Slice9
  · exact point168Slice10
  · exact point168Slice11
  · exact point168Slice12
  · exact point168Slice13
  · exact point168Slice14
  · exact point168Slice15
  · exact point168Slice16
  · exact point168Slice17
  · exact point168Slice18
  · exact point168Slice19
  · exact point168Slice20
  · exact point168Slice21
  · exact point168Slice22
  · exact point168Slice23
  · exact point168Slice24
  · exact point168Slice25
  · exact point168Slice26
  · exact point168Slice27
  · exact point168Slice28

set_option maxHeartbeats 1600000 in
private theorem point169Slice0 : Part0Residual.pointSliceCheck 1 3135 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice1 : Part0Residual.pointSliceCheck 1 3135 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice2 : Part0Residual.pointSliceCheck 1 3135 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice3 : Part0Residual.pointSliceCheck 1 3135 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice4 : Part0Residual.pointSliceCheck 1 3135 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice5 : Part0Residual.pointSliceCheck 1 3135 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice6 : Part0Residual.pointSliceCheck 1 3135 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice7 : Part0Residual.pointSliceCheck 1 3135 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice8 : Part0Residual.pointSliceCheck 1 3135 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice9 : Part0Residual.pointSliceCheck 1 3135 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice10 : Part0Residual.pointSliceCheck 1 3135 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice11 : Part0Residual.pointSliceCheck 1 3135 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice12 : Part0Residual.pointSliceCheck 1 3135 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice13 : Part0Residual.pointSliceCheck 1 3135 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice14 : Part0Residual.pointSliceCheck 1 3135 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice15 : Part0Residual.pointSliceCheck 1 3135 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice16 : Part0Residual.pointSliceCheck 1 3135 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice17 : Part0Residual.pointSliceCheck 1 3135 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice18 : Part0Residual.pointSliceCheck 1 3135 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice19 : Part0Residual.pointSliceCheck 1 3135 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice20 : Part0Residual.pointSliceCheck 1 3135 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice21 : Part0Residual.pointSliceCheck 1 3135 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice22 : Part0Residual.pointSliceCheck 1 3135 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice23 : Part0Residual.pointSliceCheck 1 3135 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice24 : Part0Residual.pointSliceCheck 1 3135 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice25 : Part0Residual.pointSliceCheck 1 3135 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice26 : Part0Residual.pointSliceCheck 1 3135 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice27 : Part0Residual.pointSliceCheck 1 3135 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point169Slice28 : Part0Residual.pointSliceCheck 1 3135 28 := by
  decide +kernel

public theorem point169 : stepCheck 1 3135 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point169Slice0
  · exact point169Slice1
  · exact point169Slice2
  · exact point169Slice3
  · exact point169Slice4
  · exact point169Slice5
  · exact point169Slice6
  · exact point169Slice7
  · exact point169Slice8
  · exact point169Slice9
  · exact point169Slice10
  · exact point169Slice11
  · exact point169Slice12
  · exact point169Slice13
  · exact point169Slice14
  · exact point169Slice15
  · exact point169Slice16
  · exact point169Slice17
  · exact point169Slice18
  · exact point169Slice19
  · exact point169Slice20
  · exact point169Slice21
  · exact point169Slice22
  · exact point169Slice23
  · exact point169Slice24
  · exact point169Slice25
  · exact point169Slice26
  · exact point169Slice27
  · exact point169Slice28

set_option maxHeartbeats 1600000 in
private theorem point170Slice0 : Part0Residual.pointSliceCheck 1 3138 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice1 : Part0Residual.pointSliceCheck 1 3138 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice2 : Part0Residual.pointSliceCheck 1 3138 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice3 : Part0Residual.pointSliceCheck 1 3138 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice4 : Part0Residual.pointSliceCheck 1 3138 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice5 : Part0Residual.pointSliceCheck 1 3138 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice6 : Part0Residual.pointSliceCheck 1 3138 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice7 : Part0Residual.pointSliceCheck 1 3138 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice8 : Part0Residual.pointSliceCheck 1 3138 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice9 : Part0Residual.pointSliceCheck 1 3138 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice10 : Part0Residual.pointSliceCheck 1 3138 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice11 : Part0Residual.pointSliceCheck 1 3138 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice12 : Part0Residual.pointSliceCheck 1 3138 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice13 : Part0Residual.pointSliceCheck 1 3138 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice14 : Part0Residual.pointSliceCheck 1 3138 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice15 : Part0Residual.pointSliceCheck 1 3138 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice16 : Part0Residual.pointSliceCheck 1 3138 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice17 : Part0Residual.pointSliceCheck 1 3138 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice18 : Part0Residual.pointSliceCheck 1 3138 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice19 : Part0Residual.pointSliceCheck 1 3138 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice20 : Part0Residual.pointSliceCheck 1 3138 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice21 : Part0Residual.pointSliceCheck 1 3138 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice22 : Part0Residual.pointSliceCheck 1 3138 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice23 : Part0Residual.pointSliceCheck 1 3138 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice24 : Part0Residual.pointSliceCheck 1 3138 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice25 : Part0Residual.pointSliceCheck 1 3138 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice26 : Part0Residual.pointSliceCheck 1 3138 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice27 : Part0Residual.pointSliceCheck 1 3138 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point170Slice28 : Part0Residual.pointSliceCheck 1 3138 28 := by
  decide +kernel

public theorem point170 : stepCheck 1 3138 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point170Slice0
  · exact point170Slice1
  · exact point170Slice2
  · exact point170Slice3
  · exact point170Slice4
  · exact point170Slice5
  · exact point170Slice6
  · exact point170Slice7
  · exact point170Slice8
  · exact point170Slice9
  · exact point170Slice10
  · exact point170Slice11
  · exact point170Slice12
  · exact point170Slice13
  · exact point170Slice14
  · exact point170Slice15
  · exact point170Slice16
  · exact point170Slice17
  · exact point170Slice18
  · exact point170Slice19
  · exact point170Slice20
  · exact point170Slice21
  · exact point170Slice22
  · exact point170Slice23
  · exact point170Slice24
  · exact point170Slice25
  · exact point170Slice26
  · exact point170Slice27
  · exact point170Slice28

set_option maxHeartbeats 1600000 in
private theorem point171Slice0 : Part0Residual.pointSliceCheck 0 3264 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice1 : Part0Residual.pointSliceCheck 0 3264 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice2 : Part0Residual.pointSliceCheck 0 3264 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice3 : Part0Residual.pointSliceCheck 0 3264 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice4 : Part0Residual.pointSliceCheck 0 3264 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice5 : Part0Residual.pointSliceCheck 0 3264 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice6 : Part0Residual.pointSliceCheck 0 3264 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice7 : Part0Residual.pointSliceCheck 0 3264 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice8 : Part0Residual.pointSliceCheck 0 3264 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice9 : Part0Residual.pointSliceCheck 0 3264 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice10 : Part0Residual.pointSliceCheck 0 3264 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice11 : Part0Residual.pointSliceCheck 0 3264 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice12 : Part0Residual.pointSliceCheck 0 3264 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice13 : Part0Residual.pointSliceCheck 0 3264 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice14 : Part0Residual.pointSliceCheck 0 3264 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice15 : Part0Residual.pointSliceCheck 0 3264 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice16 : Part0Residual.pointSliceCheck 0 3264 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice17 : Part0Residual.pointSliceCheck 0 3264 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice18 : Part0Residual.pointSliceCheck 0 3264 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice19 : Part0Residual.pointSliceCheck 0 3264 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice20 : Part0Residual.pointSliceCheck 0 3264 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice21 : Part0Residual.pointSliceCheck 0 3264 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice22 : Part0Residual.pointSliceCheck 0 3264 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice23 : Part0Residual.pointSliceCheck 0 3264 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice24 : Part0Residual.pointSliceCheck 0 3264 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice25 : Part0Residual.pointSliceCheck 0 3264 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice26 : Part0Residual.pointSliceCheck 0 3264 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice27 : Part0Residual.pointSliceCheck 0 3264 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point171Slice28 : Part0Residual.pointSliceCheck 0 3264 28 := by
  decide +kernel

public theorem point171 : stepCheck 0 3264 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point171Slice0
  · exact point171Slice1
  · exact point171Slice2
  · exact point171Slice3
  · exact point171Slice4
  · exact point171Slice5
  · exact point171Slice6
  · exact point171Slice7
  · exact point171Slice8
  · exact point171Slice9
  · exact point171Slice10
  · exact point171Slice11
  · exact point171Slice12
  · exact point171Slice13
  · exact point171Slice14
  · exact point171Slice15
  · exact point171Slice16
  · exact point171Slice17
  · exact point171Slice18
  · exact point171Slice19
  · exact point171Slice20
  · exact point171Slice21
  · exact point171Slice22
  · exact point171Slice23
  · exact point171Slice24
  · exact point171Slice25
  · exact point171Slice26
  · exact point171Slice27
  · exact point171Slice28

set_option maxHeartbeats 1600000 in
private theorem point172Slice0 : Part0Residual.pointSliceCheck 0 3265 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice1 : Part0Residual.pointSliceCheck 0 3265 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice2 : Part0Residual.pointSliceCheck 0 3265 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice3 : Part0Residual.pointSliceCheck 0 3265 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice4 : Part0Residual.pointSliceCheck 0 3265 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice5 : Part0Residual.pointSliceCheck 0 3265 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice6 : Part0Residual.pointSliceCheck 0 3265 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice7 : Part0Residual.pointSliceCheck 0 3265 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice8 : Part0Residual.pointSliceCheck 0 3265 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice9 : Part0Residual.pointSliceCheck 0 3265 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice10 : Part0Residual.pointSliceCheck 0 3265 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice11 : Part0Residual.pointSliceCheck 0 3265 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice12 : Part0Residual.pointSliceCheck 0 3265 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice13 : Part0Residual.pointSliceCheck 0 3265 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice14 : Part0Residual.pointSliceCheck 0 3265 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice15 : Part0Residual.pointSliceCheck 0 3265 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice16 : Part0Residual.pointSliceCheck 0 3265 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice17 : Part0Residual.pointSliceCheck 0 3265 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice18 : Part0Residual.pointSliceCheck 0 3265 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice19 : Part0Residual.pointSliceCheck 0 3265 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice20 : Part0Residual.pointSliceCheck 0 3265 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice21 : Part0Residual.pointSliceCheck 0 3265 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice22 : Part0Residual.pointSliceCheck 0 3265 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice23 : Part0Residual.pointSliceCheck 0 3265 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice24 : Part0Residual.pointSliceCheck 0 3265 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice25 : Part0Residual.pointSliceCheck 0 3265 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice26 : Part0Residual.pointSliceCheck 0 3265 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice27 : Part0Residual.pointSliceCheck 0 3265 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point172Slice28 : Part0Residual.pointSliceCheck 0 3265 28 := by
  decide +kernel

public theorem point172 : stepCheck 0 3265 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point172Slice0
  · exact point172Slice1
  · exact point172Slice2
  · exact point172Slice3
  · exact point172Slice4
  · exact point172Slice5
  · exact point172Slice6
  · exact point172Slice7
  · exact point172Slice8
  · exact point172Slice9
  · exact point172Slice10
  · exact point172Slice11
  · exact point172Slice12
  · exact point172Slice13
  · exact point172Slice14
  · exact point172Slice15
  · exact point172Slice16
  · exact point172Slice17
  · exact point172Slice18
  · exact point172Slice19
  · exact point172Slice20
  · exact point172Slice21
  · exact point172Slice22
  · exact point172Slice23
  · exact point172Slice24
  · exact point172Slice25
  · exact point172Slice26
  · exact point172Slice27
  · exact point172Slice28

set_option maxHeartbeats 1600000 in
private theorem point173Slice0 : Part0Residual.pointSliceCheck 0 3266 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice1 : Part0Residual.pointSliceCheck 0 3266 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice2 : Part0Residual.pointSliceCheck 0 3266 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice3 : Part0Residual.pointSliceCheck 0 3266 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice4 : Part0Residual.pointSliceCheck 0 3266 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice5 : Part0Residual.pointSliceCheck 0 3266 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice6 : Part0Residual.pointSliceCheck 0 3266 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice7 : Part0Residual.pointSliceCheck 0 3266 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice8 : Part0Residual.pointSliceCheck 0 3266 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice9 : Part0Residual.pointSliceCheck 0 3266 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice10 : Part0Residual.pointSliceCheck 0 3266 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice11 : Part0Residual.pointSliceCheck 0 3266 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice12 : Part0Residual.pointSliceCheck 0 3266 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice13 : Part0Residual.pointSliceCheck 0 3266 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice14 : Part0Residual.pointSliceCheck 0 3266 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice15 : Part0Residual.pointSliceCheck 0 3266 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice16 : Part0Residual.pointSliceCheck 0 3266 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice17 : Part0Residual.pointSliceCheck 0 3266 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice18 : Part0Residual.pointSliceCheck 0 3266 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice19 : Part0Residual.pointSliceCheck 0 3266 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice20 : Part0Residual.pointSliceCheck 0 3266 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice21 : Part0Residual.pointSliceCheck 0 3266 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice22 : Part0Residual.pointSliceCheck 0 3266 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice23 : Part0Residual.pointSliceCheck 0 3266 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice24 : Part0Residual.pointSliceCheck 0 3266 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice25 : Part0Residual.pointSliceCheck 0 3266 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice26 : Part0Residual.pointSliceCheck 0 3266 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice27 : Part0Residual.pointSliceCheck 0 3266 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point173Slice28 : Part0Residual.pointSliceCheck 0 3266 28 := by
  decide +kernel

public theorem point173 : stepCheck 0 3266 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point173Slice0
  · exact point173Slice1
  · exact point173Slice2
  · exact point173Slice3
  · exact point173Slice4
  · exact point173Slice5
  · exact point173Slice6
  · exact point173Slice7
  · exact point173Slice8
  · exact point173Slice9
  · exact point173Slice10
  · exact point173Slice11
  · exact point173Slice12
  · exact point173Slice13
  · exact point173Slice14
  · exact point173Slice15
  · exact point173Slice16
  · exact point173Slice17
  · exact point173Slice18
  · exact point173Slice19
  · exact point173Slice20
  · exact point173Slice21
  · exact point173Slice22
  · exact point173Slice23
  · exact point173Slice24
  · exact point173Slice25
  · exact point173Slice26
  · exact point173Slice27
  · exact point173Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
