module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 162–167

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point162Slice0 : Part0Residual.pointSliceCheck 0 3136 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice1 : Part0Residual.pointSliceCheck 0 3136 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice2 : Part0Residual.pointSliceCheck 0 3136 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice3 : Part0Residual.pointSliceCheck 0 3136 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice4 : Part0Residual.pointSliceCheck 0 3136 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice5 : Part0Residual.pointSliceCheck 0 3136 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice6 : Part0Residual.pointSliceCheck 0 3136 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice7 : Part0Residual.pointSliceCheck 0 3136 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice8 : Part0Residual.pointSliceCheck 0 3136 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice9 : Part0Residual.pointSliceCheck 0 3136 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice10 : Part0Residual.pointSliceCheck 0 3136 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice11 : Part0Residual.pointSliceCheck 0 3136 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice12 : Part0Residual.pointSliceCheck 0 3136 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice13 : Part0Residual.pointSliceCheck 0 3136 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice14 : Part0Residual.pointSliceCheck 0 3136 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice15 : Part0Residual.pointSliceCheck 0 3136 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice16 : Part0Residual.pointSliceCheck 0 3136 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice17 : Part0Residual.pointSliceCheck 0 3136 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice18 : Part0Residual.pointSliceCheck 0 3136 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice19 : Part0Residual.pointSliceCheck 0 3136 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice20 : Part0Residual.pointSliceCheck 0 3136 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice21 : Part0Residual.pointSliceCheck 0 3136 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice22 : Part0Residual.pointSliceCheck 0 3136 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice23 : Part0Residual.pointSliceCheck 0 3136 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice24 : Part0Residual.pointSliceCheck 0 3136 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice25 : Part0Residual.pointSliceCheck 0 3136 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice26 : Part0Residual.pointSliceCheck 0 3136 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice27 : Part0Residual.pointSliceCheck 0 3136 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point162Slice28 : Part0Residual.pointSliceCheck 0 3136 28 := by
  decide +kernel

public theorem point162 : stepCheck 0 3136 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point162Slice0
  · exact point162Slice1
  · exact point162Slice2
  · exact point162Slice3
  · exact point162Slice4
  · exact point162Slice5
  · exact point162Slice6
  · exact point162Slice7
  · exact point162Slice8
  · exact point162Slice9
  · exact point162Slice10
  · exact point162Slice11
  · exact point162Slice12
  · exact point162Slice13
  · exact point162Slice14
  · exact point162Slice15
  · exact point162Slice16
  · exact point162Slice17
  · exact point162Slice18
  · exact point162Slice19
  · exact point162Slice20
  · exact point162Slice21
  · exact point162Slice22
  · exact point162Slice23
  · exact point162Slice24
  · exact point162Slice25
  · exact point162Slice26
  · exact point162Slice27
  · exact point162Slice28

set_option maxHeartbeats 1600000 in
private theorem point163Slice0 : Part0Residual.pointSliceCheck 0 3138 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice1 : Part0Residual.pointSliceCheck 0 3138 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice2 : Part0Residual.pointSliceCheck 0 3138 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice3 : Part0Residual.pointSliceCheck 0 3138 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice4 : Part0Residual.pointSliceCheck 0 3138 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice5 : Part0Residual.pointSliceCheck 0 3138 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice6 : Part0Residual.pointSliceCheck 0 3138 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice7 : Part0Residual.pointSliceCheck 0 3138 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice8 : Part0Residual.pointSliceCheck 0 3138 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice9 : Part0Residual.pointSliceCheck 0 3138 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice10 : Part0Residual.pointSliceCheck 0 3138 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice11 : Part0Residual.pointSliceCheck 0 3138 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice12 : Part0Residual.pointSliceCheck 0 3138 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice13 : Part0Residual.pointSliceCheck 0 3138 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice14 : Part0Residual.pointSliceCheck 0 3138 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice15 : Part0Residual.pointSliceCheck 0 3138 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice16 : Part0Residual.pointSliceCheck 0 3138 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice17 : Part0Residual.pointSliceCheck 0 3138 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice18 : Part0Residual.pointSliceCheck 0 3138 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice19 : Part0Residual.pointSliceCheck 0 3138 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice20 : Part0Residual.pointSliceCheck 0 3138 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice21 : Part0Residual.pointSliceCheck 0 3138 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice22 : Part0Residual.pointSliceCheck 0 3138 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice23 : Part0Residual.pointSliceCheck 0 3138 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice24 : Part0Residual.pointSliceCheck 0 3138 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice25 : Part0Residual.pointSliceCheck 0 3138 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice26 : Part0Residual.pointSliceCheck 0 3138 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice27 : Part0Residual.pointSliceCheck 0 3138 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point163Slice28 : Part0Residual.pointSliceCheck 0 3138 28 := by
  decide +kernel

public theorem point163 : stepCheck 0 3138 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point163Slice0
  · exact point163Slice1
  · exact point163Slice2
  · exact point163Slice3
  · exact point163Slice4
  · exact point163Slice5
  · exact point163Slice6
  · exact point163Slice7
  · exact point163Slice8
  · exact point163Slice9
  · exact point163Slice10
  · exact point163Slice11
  · exact point163Slice12
  · exact point163Slice13
  · exact point163Slice14
  · exact point163Slice15
  · exact point163Slice16
  · exact point163Slice17
  · exact point163Slice18
  · exact point163Slice19
  · exact point163Slice20
  · exact point163Slice21
  · exact point163Slice22
  · exact point163Slice23
  · exact point163Slice24
  · exact point163Slice25
  · exact point163Slice26
  · exact point163Slice27
  · exact point163Slice28

set_option maxHeartbeats 1600000 in
private theorem point164Slice0 : Part0Residual.pointSliceCheck 0 3139 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice1 : Part0Residual.pointSliceCheck 0 3139 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice2 : Part0Residual.pointSliceCheck 0 3139 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice3 : Part0Residual.pointSliceCheck 0 3139 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice4 : Part0Residual.pointSliceCheck 0 3139 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice5 : Part0Residual.pointSliceCheck 0 3139 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice6 : Part0Residual.pointSliceCheck 0 3139 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice7 : Part0Residual.pointSliceCheck 0 3139 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice8 : Part0Residual.pointSliceCheck 0 3139 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice9 : Part0Residual.pointSliceCheck 0 3139 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice10 : Part0Residual.pointSliceCheck 0 3139 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice11 : Part0Residual.pointSliceCheck 0 3139 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice12 : Part0Residual.pointSliceCheck 0 3139 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice13 : Part0Residual.pointSliceCheck 0 3139 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice14 : Part0Residual.pointSliceCheck 0 3139 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice15 : Part0Residual.pointSliceCheck 0 3139 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice16 : Part0Residual.pointSliceCheck 0 3139 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice17 : Part0Residual.pointSliceCheck 0 3139 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice18 : Part0Residual.pointSliceCheck 0 3139 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice19 : Part0Residual.pointSliceCheck 0 3139 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice20 : Part0Residual.pointSliceCheck 0 3139 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice21 : Part0Residual.pointSliceCheck 0 3139 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice22 : Part0Residual.pointSliceCheck 0 3139 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice23 : Part0Residual.pointSliceCheck 0 3139 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice24 : Part0Residual.pointSliceCheck 0 3139 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice25 : Part0Residual.pointSliceCheck 0 3139 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice26 : Part0Residual.pointSliceCheck 0 3139 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice27 : Part0Residual.pointSliceCheck 0 3139 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point164Slice28 : Part0Residual.pointSliceCheck 0 3139 28 := by
  decide +kernel

public theorem point164 : stepCheck 0 3139 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point164Slice0
  · exact point164Slice1
  · exact point164Slice2
  · exact point164Slice3
  · exact point164Slice4
  · exact point164Slice5
  · exact point164Slice6
  · exact point164Slice7
  · exact point164Slice8
  · exact point164Slice9
  · exact point164Slice10
  · exact point164Slice11
  · exact point164Slice12
  · exact point164Slice13
  · exact point164Slice14
  · exact point164Slice15
  · exact point164Slice16
  · exact point164Slice17
  · exact point164Slice18
  · exact point164Slice19
  · exact point164Slice20
  · exact point164Slice21
  · exact point164Slice22
  · exact point164Slice23
  · exact point164Slice24
  · exact point164Slice25
  · exact point164Slice26
  · exact point164Slice27
  · exact point164Slice28

set_option maxHeartbeats 1600000 in
private theorem point165Slice0 : Part0Residual.pointSliceCheck 1 3122 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice1 : Part0Residual.pointSliceCheck 1 3122 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice2 : Part0Residual.pointSliceCheck 1 3122 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice3 : Part0Residual.pointSliceCheck 1 3122 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice4 : Part0Residual.pointSliceCheck 1 3122 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice5 : Part0Residual.pointSliceCheck 1 3122 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice6 : Part0Residual.pointSliceCheck 1 3122 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice7 : Part0Residual.pointSliceCheck 1 3122 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice8 : Part0Residual.pointSliceCheck 1 3122 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice9 : Part0Residual.pointSliceCheck 1 3122 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice10 : Part0Residual.pointSliceCheck 1 3122 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice11 : Part0Residual.pointSliceCheck 1 3122 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice12 : Part0Residual.pointSliceCheck 1 3122 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice13 : Part0Residual.pointSliceCheck 1 3122 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice14 : Part0Residual.pointSliceCheck 1 3122 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice15 : Part0Residual.pointSliceCheck 1 3122 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice16 : Part0Residual.pointSliceCheck 1 3122 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice17 : Part0Residual.pointSliceCheck 1 3122 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice18 : Part0Residual.pointSliceCheck 1 3122 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice19 : Part0Residual.pointSliceCheck 1 3122 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice20 : Part0Residual.pointSliceCheck 1 3122 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice21 : Part0Residual.pointSliceCheck 1 3122 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice22 : Part0Residual.pointSliceCheck 1 3122 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice23 : Part0Residual.pointSliceCheck 1 3122 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice24 : Part0Residual.pointSliceCheck 1 3122 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice25 : Part0Residual.pointSliceCheck 1 3122 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice26 : Part0Residual.pointSliceCheck 1 3122 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice27 : Part0Residual.pointSliceCheck 1 3122 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point165Slice28 : Part0Residual.pointSliceCheck 1 3122 28 := by
  decide +kernel

public theorem point165 : stepCheck 1 3122 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point165Slice0
  · exact point165Slice1
  · exact point165Slice2
  · exact point165Slice3
  · exact point165Slice4
  · exact point165Slice5
  · exact point165Slice6
  · exact point165Slice7
  · exact point165Slice8
  · exact point165Slice9
  · exact point165Slice10
  · exact point165Slice11
  · exact point165Slice12
  · exact point165Slice13
  · exact point165Slice14
  · exact point165Slice15
  · exact point165Slice16
  · exact point165Slice17
  · exact point165Slice18
  · exact point165Slice19
  · exact point165Slice20
  · exact point165Slice21
  · exact point165Slice22
  · exact point165Slice23
  · exact point165Slice24
  · exact point165Slice25
  · exact point165Slice26
  · exact point165Slice27
  · exact point165Slice28

set_option maxHeartbeats 1600000 in
private theorem point166Slice0 : Part0Residual.pointSliceCheck 1 3123 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice1 : Part0Residual.pointSliceCheck 1 3123 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice2 : Part0Residual.pointSliceCheck 1 3123 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice3 : Part0Residual.pointSliceCheck 1 3123 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice4 : Part0Residual.pointSliceCheck 1 3123 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice5 : Part0Residual.pointSliceCheck 1 3123 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice6 : Part0Residual.pointSliceCheck 1 3123 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice7 : Part0Residual.pointSliceCheck 1 3123 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice8 : Part0Residual.pointSliceCheck 1 3123 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice9 : Part0Residual.pointSliceCheck 1 3123 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice10 : Part0Residual.pointSliceCheck 1 3123 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice11 : Part0Residual.pointSliceCheck 1 3123 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice12 : Part0Residual.pointSliceCheck 1 3123 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice13 : Part0Residual.pointSliceCheck 1 3123 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice14 : Part0Residual.pointSliceCheck 1 3123 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice15 : Part0Residual.pointSliceCheck 1 3123 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice16 : Part0Residual.pointSliceCheck 1 3123 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice17 : Part0Residual.pointSliceCheck 1 3123 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice18 : Part0Residual.pointSliceCheck 1 3123 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice19 : Part0Residual.pointSliceCheck 1 3123 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice20 : Part0Residual.pointSliceCheck 1 3123 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice21 : Part0Residual.pointSliceCheck 1 3123 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice22 : Part0Residual.pointSliceCheck 1 3123 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice23 : Part0Residual.pointSliceCheck 1 3123 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice24 : Part0Residual.pointSliceCheck 1 3123 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice25 : Part0Residual.pointSliceCheck 1 3123 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice26 : Part0Residual.pointSliceCheck 1 3123 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice27 : Part0Residual.pointSliceCheck 1 3123 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point166Slice28 : Part0Residual.pointSliceCheck 1 3123 28 := by
  decide +kernel

public theorem point166 : stepCheck 1 3123 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point166Slice0
  · exact point166Slice1
  · exact point166Slice2
  · exact point166Slice3
  · exact point166Slice4
  · exact point166Slice5
  · exact point166Slice6
  · exact point166Slice7
  · exact point166Slice8
  · exact point166Slice9
  · exact point166Slice10
  · exact point166Slice11
  · exact point166Slice12
  · exact point166Slice13
  · exact point166Slice14
  · exact point166Slice15
  · exact point166Slice16
  · exact point166Slice17
  · exact point166Slice18
  · exact point166Slice19
  · exact point166Slice20
  · exact point166Slice21
  · exact point166Slice22
  · exact point166Slice23
  · exact point166Slice24
  · exact point166Slice25
  · exact point166Slice26
  · exact point166Slice27
  · exact point166Slice28

set_option maxHeartbeats 1600000 in
private theorem point167Slice0 : Part0Residual.pointSliceCheck 1 3126 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice1 : Part0Residual.pointSliceCheck 1 3126 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice2 : Part0Residual.pointSliceCheck 1 3126 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice3 : Part0Residual.pointSliceCheck 1 3126 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice4 : Part0Residual.pointSliceCheck 1 3126 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice5 : Part0Residual.pointSliceCheck 1 3126 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice6 : Part0Residual.pointSliceCheck 1 3126 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice7 : Part0Residual.pointSliceCheck 1 3126 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice8 : Part0Residual.pointSliceCheck 1 3126 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice9 : Part0Residual.pointSliceCheck 1 3126 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice10 : Part0Residual.pointSliceCheck 1 3126 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice11 : Part0Residual.pointSliceCheck 1 3126 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice12 : Part0Residual.pointSliceCheck 1 3126 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice13 : Part0Residual.pointSliceCheck 1 3126 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice14 : Part0Residual.pointSliceCheck 1 3126 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice15 : Part0Residual.pointSliceCheck 1 3126 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice16 : Part0Residual.pointSliceCheck 1 3126 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice17 : Part0Residual.pointSliceCheck 1 3126 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice18 : Part0Residual.pointSliceCheck 1 3126 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice19 : Part0Residual.pointSliceCheck 1 3126 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice20 : Part0Residual.pointSliceCheck 1 3126 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice21 : Part0Residual.pointSliceCheck 1 3126 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice22 : Part0Residual.pointSliceCheck 1 3126 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice23 : Part0Residual.pointSliceCheck 1 3126 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice24 : Part0Residual.pointSliceCheck 1 3126 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice25 : Part0Residual.pointSliceCheck 1 3126 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice26 : Part0Residual.pointSliceCheck 1 3126 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice27 : Part0Residual.pointSliceCheck 1 3126 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point167Slice28 : Part0Residual.pointSliceCheck 1 3126 28 := by
  decide +kernel

public theorem point167 : stepCheck 1 3126 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point167Slice0
  · exact point167Slice1
  · exact point167Slice2
  · exact point167Slice3
  · exact point167Slice4
  · exact point167Slice5
  · exact point167Slice6
  · exact point167Slice7
  · exact point167Slice8
  · exact point167Slice9
  · exact point167Slice10
  · exact point167Slice11
  · exact point167Slice12
  · exact point167Slice13
  · exact point167Slice14
  · exact point167Slice15
  · exact point167Slice16
  · exact point167Slice17
  · exact point167Slice18
  · exact point167Slice19
  · exact point167Slice20
  · exact point167Slice21
  · exact point167Slice22
  · exact point167Slice23
  · exact point167Slice24
  · exact point167Slice25
  · exact point167Slice26
  · exact point167Slice27
  · exact point167Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
