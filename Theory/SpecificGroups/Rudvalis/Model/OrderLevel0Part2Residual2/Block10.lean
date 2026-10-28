module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 204–209

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point204Slice0 : Part0Residual.pointSliceCheck 1 3416 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice1 : Part0Residual.pointSliceCheck 1 3416 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice2 : Part0Residual.pointSliceCheck 1 3416 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice3 : Part0Residual.pointSliceCheck 1 3416 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice4 : Part0Residual.pointSliceCheck 1 3416 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice5 : Part0Residual.pointSliceCheck 1 3416 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice6 : Part0Residual.pointSliceCheck 1 3416 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice7 : Part0Residual.pointSliceCheck 1 3416 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice8 : Part0Residual.pointSliceCheck 1 3416 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice9 : Part0Residual.pointSliceCheck 1 3416 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice10 : Part0Residual.pointSliceCheck 1 3416 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice11 : Part0Residual.pointSliceCheck 1 3416 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice12 : Part0Residual.pointSliceCheck 1 3416 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice13 : Part0Residual.pointSliceCheck 1 3416 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice14 : Part0Residual.pointSliceCheck 1 3416 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice15 : Part0Residual.pointSliceCheck 1 3416 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice16 : Part0Residual.pointSliceCheck 1 3416 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice17 : Part0Residual.pointSliceCheck 1 3416 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice18 : Part0Residual.pointSliceCheck 1 3416 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice19 : Part0Residual.pointSliceCheck 1 3416 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice20 : Part0Residual.pointSliceCheck 1 3416 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice21 : Part0Residual.pointSliceCheck 1 3416 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice22 : Part0Residual.pointSliceCheck 1 3416 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice23 : Part0Residual.pointSliceCheck 1 3416 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice24 : Part0Residual.pointSliceCheck 1 3416 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice25 : Part0Residual.pointSliceCheck 1 3416 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice26 : Part0Residual.pointSliceCheck 1 3416 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice27 : Part0Residual.pointSliceCheck 1 3416 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point204Slice28 : Part0Residual.pointSliceCheck 1 3416 28 := by
  decide +kernel

public theorem point204 : stepCheck 1 3416 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point204Slice0
  · exact point204Slice1
  · exact point204Slice2
  · exact point204Slice3
  · exact point204Slice4
  · exact point204Slice5
  · exact point204Slice6
  · exact point204Slice7
  · exact point204Slice8
  · exact point204Slice9
  · exact point204Slice10
  · exact point204Slice11
  · exact point204Slice12
  · exact point204Slice13
  · exact point204Slice14
  · exact point204Slice15
  · exact point204Slice16
  · exact point204Slice17
  · exact point204Slice18
  · exact point204Slice19
  · exact point204Slice20
  · exact point204Slice21
  · exact point204Slice22
  · exact point204Slice23
  · exact point204Slice24
  · exact point204Slice25
  · exact point204Slice26
  · exact point204Slice27
  · exact point204Slice28

set_option maxHeartbeats 1600000 in
private theorem point205Slice0 : Part0Residual.pointSliceCheck 1 3418 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice1 : Part0Residual.pointSliceCheck 1 3418 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice2 : Part0Residual.pointSliceCheck 1 3418 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice3 : Part0Residual.pointSliceCheck 1 3418 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice4 : Part0Residual.pointSliceCheck 1 3418 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice5 : Part0Residual.pointSliceCheck 1 3418 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice6 : Part0Residual.pointSliceCheck 1 3418 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice7 : Part0Residual.pointSliceCheck 1 3418 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice8 : Part0Residual.pointSliceCheck 1 3418 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice9 : Part0Residual.pointSliceCheck 1 3418 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice10 : Part0Residual.pointSliceCheck 1 3418 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice11 : Part0Residual.pointSliceCheck 1 3418 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice12 : Part0Residual.pointSliceCheck 1 3418 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice13 : Part0Residual.pointSliceCheck 1 3418 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice14 : Part0Residual.pointSliceCheck 1 3418 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice15 : Part0Residual.pointSliceCheck 1 3418 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice16 : Part0Residual.pointSliceCheck 1 3418 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice17 : Part0Residual.pointSliceCheck 1 3418 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice18 : Part0Residual.pointSliceCheck 1 3418 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice19 : Part0Residual.pointSliceCheck 1 3418 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice20 : Part0Residual.pointSliceCheck 1 3418 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice21 : Part0Residual.pointSliceCheck 1 3418 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice22 : Part0Residual.pointSliceCheck 1 3418 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice23 : Part0Residual.pointSliceCheck 1 3418 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice24 : Part0Residual.pointSliceCheck 1 3418 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice25 : Part0Residual.pointSliceCheck 1 3418 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice26 : Part0Residual.pointSliceCheck 1 3418 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice27 : Part0Residual.pointSliceCheck 1 3418 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205Slice28 : Part0Residual.pointSliceCheck 1 3418 28 := by
  decide +kernel

public theorem point205 : stepCheck 1 3418 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point205Slice0
  · exact point205Slice1
  · exact point205Slice2
  · exact point205Slice3
  · exact point205Slice4
  · exact point205Slice5
  · exact point205Slice6
  · exact point205Slice7
  · exact point205Slice8
  · exact point205Slice9
  · exact point205Slice10
  · exact point205Slice11
  · exact point205Slice12
  · exact point205Slice13
  · exact point205Slice14
  · exact point205Slice15
  · exact point205Slice16
  · exact point205Slice17
  · exact point205Slice18
  · exact point205Slice19
  · exact point205Slice20
  · exact point205Slice21
  · exact point205Slice22
  · exact point205Slice23
  · exact point205Slice24
  · exact point205Slice25
  · exact point205Slice26
  · exact point205Slice27
  · exact point205Slice28

set_option maxHeartbeats 1600000 in
private theorem point206Slice0 : Part0Residual.pointSliceCheck 1 3419 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice1 : Part0Residual.pointSliceCheck 1 3419 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice2 : Part0Residual.pointSliceCheck 1 3419 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice3 : Part0Residual.pointSliceCheck 1 3419 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice4 : Part0Residual.pointSliceCheck 1 3419 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice5 : Part0Residual.pointSliceCheck 1 3419 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice6 : Part0Residual.pointSliceCheck 1 3419 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice7 : Part0Residual.pointSliceCheck 1 3419 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice8 : Part0Residual.pointSliceCheck 1 3419 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice9 : Part0Residual.pointSliceCheck 1 3419 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice10 : Part0Residual.pointSliceCheck 1 3419 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice11 : Part0Residual.pointSliceCheck 1 3419 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice12 : Part0Residual.pointSliceCheck 1 3419 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice13 : Part0Residual.pointSliceCheck 1 3419 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice14 : Part0Residual.pointSliceCheck 1 3419 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice15 : Part0Residual.pointSliceCheck 1 3419 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice16 : Part0Residual.pointSliceCheck 1 3419 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice17 : Part0Residual.pointSliceCheck 1 3419 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice18 : Part0Residual.pointSliceCheck 1 3419 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice19 : Part0Residual.pointSliceCheck 1 3419 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice20 : Part0Residual.pointSliceCheck 1 3419 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice21 : Part0Residual.pointSliceCheck 1 3419 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice22 : Part0Residual.pointSliceCheck 1 3419 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice23 : Part0Residual.pointSliceCheck 1 3419 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice24 : Part0Residual.pointSliceCheck 1 3419 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice25 : Part0Residual.pointSliceCheck 1 3419 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice26 : Part0Residual.pointSliceCheck 1 3419 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice27 : Part0Residual.pointSliceCheck 1 3419 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206Slice28 : Part0Residual.pointSliceCheck 1 3419 28 := by
  decide +kernel

public theorem point206 : stepCheck 1 3419 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point206Slice0
  · exact point206Slice1
  · exact point206Slice2
  · exact point206Slice3
  · exact point206Slice4
  · exact point206Slice5
  · exact point206Slice6
  · exact point206Slice7
  · exact point206Slice8
  · exact point206Slice9
  · exact point206Slice10
  · exact point206Slice11
  · exact point206Slice12
  · exact point206Slice13
  · exact point206Slice14
  · exact point206Slice15
  · exact point206Slice16
  · exact point206Slice17
  · exact point206Slice18
  · exact point206Slice19
  · exact point206Slice20
  · exact point206Slice21
  · exact point206Slice22
  · exact point206Slice23
  · exact point206Slice24
  · exact point206Slice25
  · exact point206Slice26
  · exact point206Slice27
  · exact point206Slice28

set_option maxHeartbeats 1600000 in
private theorem point207Slice0 : Part0Residual.pointSliceCheck 0 3540 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice1 : Part0Residual.pointSliceCheck 0 3540 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice2 : Part0Residual.pointSliceCheck 0 3540 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice3 : Part0Residual.pointSliceCheck 0 3540 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice4 : Part0Residual.pointSliceCheck 0 3540 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice5 : Part0Residual.pointSliceCheck 0 3540 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice6 : Part0Residual.pointSliceCheck 0 3540 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice7 : Part0Residual.pointSliceCheck 0 3540 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice8 : Part0Residual.pointSliceCheck 0 3540 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice9 : Part0Residual.pointSliceCheck 0 3540 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice10 : Part0Residual.pointSliceCheck 0 3540 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice11 : Part0Residual.pointSliceCheck 0 3540 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice12 : Part0Residual.pointSliceCheck 0 3540 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice13 : Part0Residual.pointSliceCheck 0 3540 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice14 : Part0Residual.pointSliceCheck 0 3540 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice15 : Part0Residual.pointSliceCheck 0 3540 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice16 : Part0Residual.pointSliceCheck 0 3540 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice17 : Part0Residual.pointSliceCheck 0 3540 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice18 : Part0Residual.pointSliceCheck 0 3540 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice19 : Part0Residual.pointSliceCheck 0 3540 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice20 : Part0Residual.pointSliceCheck 0 3540 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice21 : Part0Residual.pointSliceCheck 0 3540 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice22 : Part0Residual.pointSliceCheck 0 3540 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice23 : Part0Residual.pointSliceCheck 0 3540 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice24 : Part0Residual.pointSliceCheck 0 3540 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice25 : Part0Residual.pointSliceCheck 0 3540 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice26 : Part0Residual.pointSliceCheck 0 3540 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice27 : Part0Residual.pointSliceCheck 0 3540 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207Slice28 : Part0Residual.pointSliceCheck 0 3540 28 := by
  decide +kernel

public theorem point207 : stepCheck 0 3540 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point207Slice0
  · exact point207Slice1
  · exact point207Slice2
  · exact point207Slice3
  · exact point207Slice4
  · exact point207Slice5
  · exact point207Slice6
  · exact point207Slice7
  · exact point207Slice8
  · exact point207Slice9
  · exact point207Slice10
  · exact point207Slice11
  · exact point207Slice12
  · exact point207Slice13
  · exact point207Slice14
  · exact point207Slice15
  · exact point207Slice16
  · exact point207Slice17
  · exact point207Slice18
  · exact point207Slice19
  · exact point207Slice20
  · exact point207Slice21
  · exact point207Slice22
  · exact point207Slice23
  · exact point207Slice24
  · exact point207Slice25
  · exact point207Slice26
  · exact point207Slice27
  · exact point207Slice28

set_option maxHeartbeats 1600000 in
private theorem point208Slice0 : Part0Residual.pointSliceCheck 0 3542 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice1 : Part0Residual.pointSliceCheck 0 3542 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice2 : Part0Residual.pointSliceCheck 0 3542 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice3 : Part0Residual.pointSliceCheck 0 3542 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice4 : Part0Residual.pointSliceCheck 0 3542 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice5 : Part0Residual.pointSliceCheck 0 3542 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice6 : Part0Residual.pointSliceCheck 0 3542 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice7 : Part0Residual.pointSliceCheck 0 3542 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice8 : Part0Residual.pointSliceCheck 0 3542 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice9 : Part0Residual.pointSliceCheck 0 3542 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice10 : Part0Residual.pointSliceCheck 0 3542 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice11 : Part0Residual.pointSliceCheck 0 3542 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice12 : Part0Residual.pointSliceCheck 0 3542 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice13 : Part0Residual.pointSliceCheck 0 3542 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice14 : Part0Residual.pointSliceCheck 0 3542 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice15 : Part0Residual.pointSliceCheck 0 3542 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice16 : Part0Residual.pointSliceCheck 0 3542 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice17 : Part0Residual.pointSliceCheck 0 3542 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice18 : Part0Residual.pointSliceCheck 0 3542 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice19 : Part0Residual.pointSliceCheck 0 3542 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice20 : Part0Residual.pointSliceCheck 0 3542 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice21 : Part0Residual.pointSliceCheck 0 3542 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice22 : Part0Residual.pointSliceCheck 0 3542 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice23 : Part0Residual.pointSliceCheck 0 3542 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice24 : Part0Residual.pointSliceCheck 0 3542 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice25 : Part0Residual.pointSliceCheck 0 3542 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice26 : Part0Residual.pointSliceCheck 0 3542 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice27 : Part0Residual.pointSliceCheck 0 3542 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point208Slice28 : Part0Residual.pointSliceCheck 0 3542 28 := by
  decide +kernel

public theorem point208 : stepCheck 0 3542 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point208Slice0
  · exact point208Slice1
  · exact point208Slice2
  · exact point208Slice3
  · exact point208Slice4
  · exact point208Slice5
  · exact point208Slice6
  · exact point208Slice7
  · exact point208Slice8
  · exact point208Slice9
  · exact point208Slice10
  · exact point208Slice11
  · exact point208Slice12
  · exact point208Slice13
  · exact point208Slice14
  · exact point208Slice15
  · exact point208Slice16
  · exact point208Slice17
  · exact point208Slice18
  · exact point208Slice19
  · exact point208Slice20
  · exact point208Slice21
  · exact point208Slice22
  · exact point208Slice23
  · exact point208Slice24
  · exact point208Slice25
  · exact point208Slice26
  · exact point208Slice27
  · exact point208Slice28

set_option maxHeartbeats 1600000 in
private theorem point209Slice0 : Part0Residual.pointSliceCheck 0 3543 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice1 : Part0Residual.pointSliceCheck 0 3543 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice2 : Part0Residual.pointSliceCheck 0 3543 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice3 : Part0Residual.pointSliceCheck 0 3543 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice4 : Part0Residual.pointSliceCheck 0 3543 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice5 : Part0Residual.pointSliceCheck 0 3543 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice6 : Part0Residual.pointSliceCheck 0 3543 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice7 : Part0Residual.pointSliceCheck 0 3543 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice8 : Part0Residual.pointSliceCheck 0 3543 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice9 : Part0Residual.pointSliceCheck 0 3543 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice10 : Part0Residual.pointSliceCheck 0 3543 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice11 : Part0Residual.pointSliceCheck 0 3543 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice12 : Part0Residual.pointSliceCheck 0 3543 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice13 : Part0Residual.pointSliceCheck 0 3543 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice14 : Part0Residual.pointSliceCheck 0 3543 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice15 : Part0Residual.pointSliceCheck 0 3543 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice16 : Part0Residual.pointSliceCheck 0 3543 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice17 : Part0Residual.pointSliceCheck 0 3543 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice18 : Part0Residual.pointSliceCheck 0 3543 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice19 : Part0Residual.pointSliceCheck 0 3543 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice20 : Part0Residual.pointSliceCheck 0 3543 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice21 : Part0Residual.pointSliceCheck 0 3543 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice22 : Part0Residual.pointSliceCheck 0 3543 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice23 : Part0Residual.pointSliceCheck 0 3543 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice24 : Part0Residual.pointSliceCheck 0 3543 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice25 : Part0Residual.pointSliceCheck 0 3543 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice26 : Part0Residual.pointSliceCheck 0 3543 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice27 : Part0Residual.pointSliceCheck 0 3543 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point209Slice28 : Part0Residual.pointSliceCheck 0 3543 28 := by
  decide +kernel

public theorem point209 : stepCheck 0 3543 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point209Slice0
  · exact point209Slice1
  · exact point209Slice2
  · exact point209Slice3
  · exact point209Slice4
  · exact point209Slice5
  · exact point209Slice6
  · exact point209Slice7
  · exact point209Slice8
  · exact point209Slice9
  · exact point209Slice10
  · exact point209Slice11
  · exact point209Slice12
  · exact point209Slice13
  · exact point209Slice14
  · exact point209Slice15
  · exact point209Slice16
  · exact point209Slice17
  · exact point209Slice18
  · exact point209Slice19
  · exact point209Slice20
  · exact point209Slice21
  · exact point209Slice22
  · exact point209Slice23
  · exact point209Slice24
  · exact point209Slice25
  · exact point209Slice26
  · exact point209Slice27
  · exact point209Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
