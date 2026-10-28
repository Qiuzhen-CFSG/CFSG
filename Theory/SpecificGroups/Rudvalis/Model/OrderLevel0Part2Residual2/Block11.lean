module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 210–215

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point210Slice0 : Part0Residual.pointSliceCheck 0 3545 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice1 : Part0Residual.pointSliceCheck 0 3545 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice2 : Part0Residual.pointSliceCheck 0 3545 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice3 : Part0Residual.pointSliceCheck 0 3545 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice4 : Part0Residual.pointSliceCheck 0 3545 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice5 : Part0Residual.pointSliceCheck 0 3545 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice6 : Part0Residual.pointSliceCheck 0 3545 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice7 : Part0Residual.pointSliceCheck 0 3545 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice8 : Part0Residual.pointSliceCheck 0 3545 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice9 : Part0Residual.pointSliceCheck 0 3545 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice10 : Part0Residual.pointSliceCheck 0 3545 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice11 : Part0Residual.pointSliceCheck 0 3545 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice12 : Part0Residual.pointSliceCheck 0 3545 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice13 : Part0Residual.pointSliceCheck 0 3545 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice14 : Part0Residual.pointSliceCheck 0 3545 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice15 : Part0Residual.pointSliceCheck 0 3545 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice16 : Part0Residual.pointSliceCheck 0 3545 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice17 : Part0Residual.pointSliceCheck 0 3545 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice18 : Part0Residual.pointSliceCheck 0 3545 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice19 : Part0Residual.pointSliceCheck 0 3545 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice20 : Part0Residual.pointSliceCheck 0 3545 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice21 : Part0Residual.pointSliceCheck 0 3545 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice22 : Part0Residual.pointSliceCheck 0 3545 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice23 : Part0Residual.pointSliceCheck 0 3545 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice24 : Part0Residual.pointSliceCheck 0 3545 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice25 : Part0Residual.pointSliceCheck 0 3545 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice26 : Part0Residual.pointSliceCheck 0 3545 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice27 : Part0Residual.pointSliceCheck 0 3545 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point210Slice28 : Part0Residual.pointSliceCheck 0 3545 28 := by
  decide +kernel

public theorem point210 : stepCheck 0 3545 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point210Slice0
  · exact point210Slice1
  · exact point210Slice2
  · exact point210Slice3
  · exact point210Slice4
  · exact point210Slice5
  · exact point210Slice6
  · exact point210Slice7
  · exact point210Slice8
  · exact point210Slice9
  · exact point210Slice10
  · exact point210Slice11
  · exact point210Slice12
  · exact point210Slice13
  · exact point210Slice14
  · exact point210Slice15
  · exact point210Slice16
  · exact point210Slice17
  · exact point210Slice18
  · exact point210Slice19
  · exact point210Slice20
  · exact point210Slice21
  · exact point210Slice22
  · exact point210Slice23
  · exact point210Slice24
  · exact point210Slice25
  · exact point210Slice26
  · exact point210Slice27
  · exact point210Slice28

set_option maxHeartbeats 1600000 in
private theorem point211Slice0 : Part0Residual.pointSliceCheck 0 3546 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice1 : Part0Residual.pointSliceCheck 0 3546 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice2 : Part0Residual.pointSliceCheck 0 3546 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice3 : Part0Residual.pointSliceCheck 0 3546 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice4 : Part0Residual.pointSliceCheck 0 3546 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice5 : Part0Residual.pointSliceCheck 0 3546 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice6 : Part0Residual.pointSliceCheck 0 3546 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice7 : Part0Residual.pointSliceCheck 0 3546 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice8 : Part0Residual.pointSliceCheck 0 3546 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice9 : Part0Residual.pointSliceCheck 0 3546 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice10 : Part0Residual.pointSliceCheck 0 3546 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice11 : Part0Residual.pointSliceCheck 0 3546 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice12 : Part0Residual.pointSliceCheck 0 3546 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice13 : Part0Residual.pointSliceCheck 0 3546 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice14 : Part0Residual.pointSliceCheck 0 3546 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice15 : Part0Residual.pointSliceCheck 0 3546 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice16 : Part0Residual.pointSliceCheck 0 3546 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice17 : Part0Residual.pointSliceCheck 0 3546 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice18 : Part0Residual.pointSliceCheck 0 3546 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice19 : Part0Residual.pointSliceCheck 0 3546 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice20 : Part0Residual.pointSliceCheck 0 3546 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice21 : Part0Residual.pointSliceCheck 0 3546 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice22 : Part0Residual.pointSliceCheck 0 3546 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice23 : Part0Residual.pointSliceCheck 0 3546 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice24 : Part0Residual.pointSliceCheck 0 3546 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice25 : Part0Residual.pointSliceCheck 0 3546 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice26 : Part0Residual.pointSliceCheck 0 3546 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice27 : Part0Residual.pointSliceCheck 0 3546 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211Slice28 : Part0Residual.pointSliceCheck 0 3546 28 := by
  decide +kernel

public theorem point211 : stepCheck 0 3546 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point211Slice0
  · exact point211Slice1
  · exact point211Slice2
  · exact point211Slice3
  · exact point211Slice4
  · exact point211Slice5
  · exact point211Slice6
  · exact point211Slice7
  · exact point211Slice8
  · exact point211Slice9
  · exact point211Slice10
  · exact point211Slice11
  · exact point211Slice12
  · exact point211Slice13
  · exact point211Slice14
  · exact point211Slice15
  · exact point211Slice16
  · exact point211Slice17
  · exact point211Slice18
  · exact point211Slice19
  · exact point211Slice20
  · exact point211Slice21
  · exact point211Slice22
  · exact point211Slice23
  · exact point211Slice24
  · exact point211Slice25
  · exact point211Slice26
  · exact point211Slice27
  · exact point211Slice28

set_option maxHeartbeats 1600000 in
private theorem point212Slice0 : Part0Residual.pointSliceCheck 0 3548 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice1 : Part0Residual.pointSliceCheck 0 3548 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice2 : Part0Residual.pointSliceCheck 0 3548 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice3 : Part0Residual.pointSliceCheck 0 3548 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice4 : Part0Residual.pointSliceCheck 0 3548 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice5 : Part0Residual.pointSliceCheck 0 3548 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice6 : Part0Residual.pointSliceCheck 0 3548 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice7 : Part0Residual.pointSliceCheck 0 3548 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice8 : Part0Residual.pointSliceCheck 0 3548 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice9 : Part0Residual.pointSliceCheck 0 3548 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice10 : Part0Residual.pointSliceCheck 0 3548 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice11 : Part0Residual.pointSliceCheck 0 3548 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice12 : Part0Residual.pointSliceCheck 0 3548 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice13 : Part0Residual.pointSliceCheck 0 3548 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice14 : Part0Residual.pointSliceCheck 0 3548 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice15 : Part0Residual.pointSliceCheck 0 3548 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice16 : Part0Residual.pointSliceCheck 0 3548 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice17 : Part0Residual.pointSliceCheck 0 3548 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice18 : Part0Residual.pointSliceCheck 0 3548 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice19 : Part0Residual.pointSliceCheck 0 3548 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice20 : Part0Residual.pointSliceCheck 0 3548 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice21 : Part0Residual.pointSliceCheck 0 3548 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice22 : Part0Residual.pointSliceCheck 0 3548 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice23 : Part0Residual.pointSliceCheck 0 3548 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice24 : Part0Residual.pointSliceCheck 0 3548 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice25 : Part0Residual.pointSliceCheck 0 3548 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice26 : Part0Residual.pointSliceCheck 0 3548 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice27 : Part0Residual.pointSliceCheck 0 3548 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point212Slice28 : Part0Residual.pointSliceCheck 0 3548 28 := by
  decide +kernel

public theorem point212 : stepCheck 0 3548 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point212Slice0
  · exact point212Slice1
  · exact point212Slice2
  · exact point212Slice3
  · exact point212Slice4
  · exact point212Slice5
  · exact point212Slice6
  · exact point212Slice7
  · exact point212Slice8
  · exact point212Slice9
  · exact point212Slice10
  · exact point212Slice11
  · exact point212Slice12
  · exact point212Slice13
  · exact point212Slice14
  · exact point212Slice15
  · exact point212Slice16
  · exact point212Slice17
  · exact point212Slice18
  · exact point212Slice19
  · exact point212Slice20
  · exact point212Slice21
  · exact point212Slice22
  · exact point212Slice23
  · exact point212Slice24
  · exact point212Slice25
  · exact point212Slice26
  · exact point212Slice27
  · exact point212Slice28

set_option maxHeartbeats 1600000 in
private theorem point213Slice0 : Part0Residual.pointSliceCheck 0 3553 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice1 : Part0Residual.pointSliceCheck 0 3553 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice2 : Part0Residual.pointSliceCheck 0 3553 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice3 : Part0Residual.pointSliceCheck 0 3553 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice4 : Part0Residual.pointSliceCheck 0 3553 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice5 : Part0Residual.pointSliceCheck 0 3553 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice6 : Part0Residual.pointSliceCheck 0 3553 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice7 : Part0Residual.pointSliceCheck 0 3553 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice8 : Part0Residual.pointSliceCheck 0 3553 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice9 : Part0Residual.pointSliceCheck 0 3553 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice10 : Part0Residual.pointSliceCheck 0 3553 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice11 : Part0Residual.pointSliceCheck 0 3553 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice12 : Part0Residual.pointSliceCheck 0 3553 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice13 : Part0Residual.pointSliceCheck 0 3553 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice14 : Part0Residual.pointSliceCheck 0 3553 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice15 : Part0Residual.pointSliceCheck 0 3553 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice16 : Part0Residual.pointSliceCheck 0 3553 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice17 : Part0Residual.pointSliceCheck 0 3553 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice18 : Part0Residual.pointSliceCheck 0 3553 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice19 : Part0Residual.pointSliceCheck 0 3553 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice20 : Part0Residual.pointSliceCheck 0 3553 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice21 : Part0Residual.pointSliceCheck 0 3553 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice22 : Part0Residual.pointSliceCheck 0 3553 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice23 : Part0Residual.pointSliceCheck 0 3553 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice24 : Part0Residual.pointSliceCheck 0 3553 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice25 : Part0Residual.pointSliceCheck 0 3553 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice26 : Part0Residual.pointSliceCheck 0 3553 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice27 : Part0Residual.pointSliceCheck 0 3553 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213Slice28 : Part0Residual.pointSliceCheck 0 3553 28 := by
  decide +kernel

public theorem point213 : stepCheck 0 3553 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point213Slice0
  · exact point213Slice1
  · exact point213Slice2
  · exact point213Slice3
  · exact point213Slice4
  · exact point213Slice5
  · exact point213Slice6
  · exact point213Slice7
  · exact point213Slice8
  · exact point213Slice9
  · exact point213Slice10
  · exact point213Slice11
  · exact point213Slice12
  · exact point213Slice13
  · exact point213Slice14
  · exact point213Slice15
  · exact point213Slice16
  · exact point213Slice17
  · exact point213Slice18
  · exact point213Slice19
  · exact point213Slice20
  · exact point213Slice21
  · exact point213Slice22
  · exact point213Slice23
  · exact point213Slice24
  · exact point213Slice25
  · exact point213Slice26
  · exact point213Slice27
  · exact point213Slice28

set_option maxHeartbeats 1600000 in
private theorem point214Slice0 : Part0Residual.pointSliceCheck 0 3555 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice1 : Part0Residual.pointSliceCheck 0 3555 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice2 : Part0Residual.pointSliceCheck 0 3555 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice3 : Part0Residual.pointSliceCheck 0 3555 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice4 : Part0Residual.pointSliceCheck 0 3555 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice5 : Part0Residual.pointSliceCheck 0 3555 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice6 : Part0Residual.pointSliceCheck 0 3555 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice7 : Part0Residual.pointSliceCheck 0 3555 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice8 : Part0Residual.pointSliceCheck 0 3555 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice9 : Part0Residual.pointSliceCheck 0 3555 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice10 : Part0Residual.pointSliceCheck 0 3555 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice11 : Part0Residual.pointSliceCheck 0 3555 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice12 : Part0Residual.pointSliceCheck 0 3555 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice13 : Part0Residual.pointSliceCheck 0 3555 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice14 : Part0Residual.pointSliceCheck 0 3555 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice15 : Part0Residual.pointSliceCheck 0 3555 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice16 : Part0Residual.pointSliceCheck 0 3555 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice17 : Part0Residual.pointSliceCheck 0 3555 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice18 : Part0Residual.pointSliceCheck 0 3555 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice19 : Part0Residual.pointSliceCheck 0 3555 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice20 : Part0Residual.pointSliceCheck 0 3555 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice21 : Part0Residual.pointSliceCheck 0 3555 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice22 : Part0Residual.pointSliceCheck 0 3555 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice23 : Part0Residual.pointSliceCheck 0 3555 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice24 : Part0Residual.pointSliceCheck 0 3555 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice25 : Part0Residual.pointSliceCheck 0 3555 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice26 : Part0Residual.pointSliceCheck 0 3555 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice27 : Part0Residual.pointSliceCheck 0 3555 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point214Slice28 : Part0Residual.pointSliceCheck 0 3555 28 := by
  decide +kernel

public theorem point214 : stepCheck 0 3555 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point214Slice0
  · exact point214Slice1
  · exact point214Slice2
  · exact point214Slice3
  · exact point214Slice4
  · exact point214Slice5
  · exact point214Slice6
  · exact point214Slice7
  · exact point214Slice8
  · exact point214Slice9
  · exact point214Slice10
  · exact point214Slice11
  · exact point214Slice12
  · exact point214Slice13
  · exact point214Slice14
  · exact point214Slice15
  · exact point214Slice16
  · exact point214Slice17
  · exact point214Slice18
  · exact point214Slice19
  · exact point214Slice20
  · exact point214Slice21
  · exact point214Slice22
  · exact point214Slice23
  · exact point214Slice24
  · exact point214Slice25
  · exact point214Slice26
  · exact point214Slice27
  · exact point214Slice28

set_option maxHeartbeats 1600000 in
private theorem point215Slice0 : Part0Residual.pointSliceCheck 0 3556 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice1 : Part0Residual.pointSliceCheck 0 3556 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice2 : Part0Residual.pointSliceCheck 0 3556 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice3 : Part0Residual.pointSliceCheck 0 3556 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice4 : Part0Residual.pointSliceCheck 0 3556 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice5 : Part0Residual.pointSliceCheck 0 3556 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice6 : Part0Residual.pointSliceCheck 0 3556 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice7 : Part0Residual.pointSliceCheck 0 3556 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice8 : Part0Residual.pointSliceCheck 0 3556 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice9 : Part0Residual.pointSliceCheck 0 3556 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice10 : Part0Residual.pointSliceCheck 0 3556 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice11 : Part0Residual.pointSliceCheck 0 3556 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice12 : Part0Residual.pointSliceCheck 0 3556 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice13 : Part0Residual.pointSliceCheck 0 3556 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice14 : Part0Residual.pointSliceCheck 0 3556 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice15 : Part0Residual.pointSliceCheck 0 3556 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice16 : Part0Residual.pointSliceCheck 0 3556 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice17 : Part0Residual.pointSliceCheck 0 3556 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice18 : Part0Residual.pointSliceCheck 0 3556 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice19 : Part0Residual.pointSliceCheck 0 3556 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice20 : Part0Residual.pointSliceCheck 0 3556 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice21 : Part0Residual.pointSliceCheck 0 3556 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice22 : Part0Residual.pointSliceCheck 0 3556 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice23 : Part0Residual.pointSliceCheck 0 3556 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice24 : Part0Residual.pointSliceCheck 0 3556 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice25 : Part0Residual.pointSliceCheck 0 3556 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice26 : Part0Residual.pointSliceCheck 0 3556 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice27 : Part0Residual.pointSliceCheck 0 3556 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215Slice28 : Part0Residual.pointSliceCheck 0 3556 28 := by
  decide +kernel

public theorem point215 : stepCheck 0 3556 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point215Slice0
  · exact point215Slice1
  · exact point215Slice2
  · exact point215Slice3
  · exact point215Slice4
  · exact point215Slice5
  · exact point215Slice6
  · exact point215Slice7
  · exact point215Slice8
  · exact point215Slice9
  · exact point215Slice10
  · exact point215Slice11
  · exact point215Slice12
  · exact point215Slice13
  · exact point215Slice14
  · exact point215Slice15
  · exact point215Slice16
  · exact point215Slice17
  · exact point215Slice18
  · exact point215Slice19
  · exact point215Slice20
  · exact point215Slice21
  · exact point215Slice22
  · exact point215Slice23
  · exact point215Slice24
  · exact point215Slice25
  · exact point215Slice26
  · exact point215Slice27
  · exact point215Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
