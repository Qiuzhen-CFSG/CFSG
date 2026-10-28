module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 156–161

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point156Slice0 : Part0Residual.pointSliceCheck 1 2988 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice1 : Part0Residual.pointSliceCheck 1 2988 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice2 : Part0Residual.pointSliceCheck 1 2988 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice3 : Part0Residual.pointSliceCheck 1 2988 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice4 : Part0Residual.pointSliceCheck 1 2988 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice5 : Part0Residual.pointSliceCheck 1 2988 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice6 : Part0Residual.pointSliceCheck 1 2988 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice7 : Part0Residual.pointSliceCheck 1 2988 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice8 : Part0Residual.pointSliceCheck 1 2988 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice9 : Part0Residual.pointSliceCheck 1 2988 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice10 : Part0Residual.pointSliceCheck 1 2988 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice11 : Part0Residual.pointSliceCheck 1 2988 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice12 : Part0Residual.pointSliceCheck 1 2988 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice13 : Part0Residual.pointSliceCheck 1 2988 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice14 : Part0Residual.pointSliceCheck 1 2988 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice15 : Part0Residual.pointSliceCheck 1 2988 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice16 : Part0Residual.pointSliceCheck 1 2988 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice17 : Part0Residual.pointSliceCheck 1 2988 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice18 : Part0Residual.pointSliceCheck 1 2988 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice19 : Part0Residual.pointSliceCheck 1 2988 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice20 : Part0Residual.pointSliceCheck 1 2988 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice21 : Part0Residual.pointSliceCheck 1 2988 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice22 : Part0Residual.pointSliceCheck 1 2988 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice23 : Part0Residual.pointSliceCheck 1 2988 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice24 : Part0Residual.pointSliceCheck 1 2988 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice25 : Part0Residual.pointSliceCheck 1 2988 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice26 : Part0Residual.pointSliceCheck 1 2988 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice27 : Part0Residual.pointSliceCheck 1 2988 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point156Slice28 : Part0Residual.pointSliceCheck 1 2988 28 := by
  decide +kernel

public theorem point156 : stepCheck 1 2988 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point156Slice0
  · exact point156Slice1
  · exact point156Slice2
  · exact point156Slice3
  · exact point156Slice4
  · exact point156Slice5
  · exact point156Slice6
  · exact point156Slice7
  · exact point156Slice8
  · exact point156Slice9
  · exact point156Slice10
  · exact point156Slice11
  · exact point156Slice12
  · exact point156Slice13
  · exact point156Slice14
  · exact point156Slice15
  · exact point156Slice16
  · exact point156Slice17
  · exact point156Slice18
  · exact point156Slice19
  · exact point156Slice20
  · exact point156Slice21
  · exact point156Slice22
  · exact point156Slice23
  · exact point156Slice24
  · exact point156Slice25
  · exact point156Slice26
  · exact point156Slice27
  · exact point156Slice28

set_option maxHeartbeats 1600000 in
private theorem point157Slice0 : Part0Residual.pointSliceCheck 1 2990 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice1 : Part0Residual.pointSliceCheck 1 2990 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice2 : Part0Residual.pointSliceCheck 1 2990 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice3 : Part0Residual.pointSliceCheck 1 2990 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice4 : Part0Residual.pointSliceCheck 1 2990 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice5 : Part0Residual.pointSliceCheck 1 2990 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice6 : Part0Residual.pointSliceCheck 1 2990 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice7 : Part0Residual.pointSliceCheck 1 2990 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice8 : Part0Residual.pointSliceCheck 1 2990 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice9 : Part0Residual.pointSliceCheck 1 2990 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice10 : Part0Residual.pointSliceCheck 1 2990 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice11 : Part0Residual.pointSliceCheck 1 2990 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice12 : Part0Residual.pointSliceCheck 1 2990 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice13 : Part0Residual.pointSliceCheck 1 2990 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice14 : Part0Residual.pointSliceCheck 1 2990 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice15 : Part0Residual.pointSliceCheck 1 2990 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice16 : Part0Residual.pointSliceCheck 1 2990 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice17 : Part0Residual.pointSliceCheck 1 2990 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice18 : Part0Residual.pointSliceCheck 1 2990 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice19 : Part0Residual.pointSliceCheck 1 2990 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice20 : Part0Residual.pointSliceCheck 1 2990 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice21 : Part0Residual.pointSliceCheck 1 2990 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice22 : Part0Residual.pointSliceCheck 1 2990 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice23 : Part0Residual.pointSliceCheck 1 2990 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice24 : Part0Residual.pointSliceCheck 1 2990 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice25 : Part0Residual.pointSliceCheck 1 2990 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice26 : Part0Residual.pointSliceCheck 1 2990 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice27 : Part0Residual.pointSliceCheck 1 2990 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point157Slice28 : Part0Residual.pointSliceCheck 1 2990 28 := by
  decide +kernel

public theorem point157 : stepCheck 1 2990 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point157Slice0
  · exact point157Slice1
  · exact point157Slice2
  · exact point157Slice3
  · exact point157Slice4
  · exact point157Slice5
  · exact point157Slice6
  · exact point157Slice7
  · exact point157Slice8
  · exact point157Slice9
  · exact point157Slice10
  · exact point157Slice11
  · exact point157Slice12
  · exact point157Slice13
  · exact point157Slice14
  · exact point157Slice15
  · exact point157Slice16
  · exact point157Slice17
  · exact point157Slice18
  · exact point157Slice19
  · exact point157Slice20
  · exact point157Slice21
  · exact point157Slice22
  · exact point157Slice23
  · exact point157Slice24
  · exact point157Slice25
  · exact point157Slice26
  · exact point157Slice27
  · exact point157Slice28

set_option maxHeartbeats 1600000 in
private theorem point158Slice0 : Part0Residual.pointSliceCheck 1 2996 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice1 : Part0Residual.pointSliceCheck 1 2996 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice2 : Part0Residual.pointSliceCheck 1 2996 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice3 : Part0Residual.pointSliceCheck 1 2996 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice4 : Part0Residual.pointSliceCheck 1 2996 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice5 : Part0Residual.pointSliceCheck 1 2996 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice6 : Part0Residual.pointSliceCheck 1 2996 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice7 : Part0Residual.pointSliceCheck 1 2996 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice8 : Part0Residual.pointSliceCheck 1 2996 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice9 : Part0Residual.pointSliceCheck 1 2996 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice10 : Part0Residual.pointSliceCheck 1 2996 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice11 : Part0Residual.pointSliceCheck 1 2996 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice12 : Part0Residual.pointSliceCheck 1 2996 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice13 : Part0Residual.pointSliceCheck 1 2996 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice14 : Part0Residual.pointSliceCheck 1 2996 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice15 : Part0Residual.pointSliceCheck 1 2996 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice16 : Part0Residual.pointSliceCheck 1 2996 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice17 : Part0Residual.pointSliceCheck 1 2996 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice18 : Part0Residual.pointSliceCheck 1 2996 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice19 : Part0Residual.pointSliceCheck 1 2996 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice20 : Part0Residual.pointSliceCheck 1 2996 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice21 : Part0Residual.pointSliceCheck 1 2996 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice22 : Part0Residual.pointSliceCheck 1 2996 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice23 : Part0Residual.pointSliceCheck 1 2996 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice24 : Part0Residual.pointSliceCheck 1 2996 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice25 : Part0Residual.pointSliceCheck 1 2996 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice26 : Part0Residual.pointSliceCheck 1 2996 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice27 : Part0Residual.pointSliceCheck 1 2996 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point158Slice28 : Part0Residual.pointSliceCheck 1 2996 28 := by
  decide +kernel

public theorem point158 : stepCheck 1 2996 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point158Slice0
  · exact point158Slice1
  · exact point158Slice2
  · exact point158Slice3
  · exact point158Slice4
  · exact point158Slice5
  · exact point158Slice6
  · exact point158Slice7
  · exact point158Slice8
  · exact point158Slice9
  · exact point158Slice10
  · exact point158Slice11
  · exact point158Slice12
  · exact point158Slice13
  · exact point158Slice14
  · exact point158Slice15
  · exact point158Slice16
  · exact point158Slice17
  · exact point158Slice18
  · exact point158Slice19
  · exact point158Slice20
  · exact point158Slice21
  · exact point158Slice22
  · exact point158Slice23
  · exact point158Slice24
  · exact point158Slice25
  · exact point158Slice26
  · exact point158Slice27
  · exact point158Slice28

set_option maxHeartbeats 1600000 in
private theorem point159Slice0 : Part0Residual.pointSliceCheck 1 2999 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice1 : Part0Residual.pointSliceCheck 1 2999 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice2 : Part0Residual.pointSliceCheck 1 2999 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice3 : Part0Residual.pointSliceCheck 1 2999 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice4 : Part0Residual.pointSliceCheck 1 2999 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice5 : Part0Residual.pointSliceCheck 1 2999 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice6 : Part0Residual.pointSliceCheck 1 2999 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice7 : Part0Residual.pointSliceCheck 1 2999 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice8 : Part0Residual.pointSliceCheck 1 2999 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice9 : Part0Residual.pointSliceCheck 1 2999 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice10 : Part0Residual.pointSliceCheck 1 2999 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice11 : Part0Residual.pointSliceCheck 1 2999 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice12 : Part0Residual.pointSliceCheck 1 2999 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice13 : Part0Residual.pointSliceCheck 1 2999 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice14 : Part0Residual.pointSliceCheck 1 2999 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice15 : Part0Residual.pointSliceCheck 1 2999 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice16 : Part0Residual.pointSliceCheck 1 2999 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice17 : Part0Residual.pointSliceCheck 1 2999 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice18 : Part0Residual.pointSliceCheck 1 2999 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice19 : Part0Residual.pointSliceCheck 1 2999 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice20 : Part0Residual.pointSliceCheck 1 2999 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice21 : Part0Residual.pointSliceCheck 1 2999 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice22 : Part0Residual.pointSliceCheck 1 2999 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice23 : Part0Residual.pointSliceCheck 1 2999 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice24 : Part0Residual.pointSliceCheck 1 2999 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice25 : Part0Residual.pointSliceCheck 1 2999 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice26 : Part0Residual.pointSliceCheck 1 2999 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice27 : Part0Residual.pointSliceCheck 1 2999 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point159Slice28 : Part0Residual.pointSliceCheck 1 2999 28 := by
  decide +kernel

public theorem point159 : stepCheck 1 2999 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point159Slice0
  · exact point159Slice1
  · exact point159Slice2
  · exact point159Slice3
  · exact point159Slice4
  · exact point159Slice5
  · exact point159Slice6
  · exact point159Slice7
  · exact point159Slice8
  · exact point159Slice9
  · exact point159Slice10
  · exact point159Slice11
  · exact point159Slice12
  · exact point159Slice13
  · exact point159Slice14
  · exact point159Slice15
  · exact point159Slice16
  · exact point159Slice17
  · exact point159Slice18
  · exact point159Slice19
  · exact point159Slice20
  · exact point159Slice21
  · exact point159Slice22
  · exact point159Slice23
  · exact point159Slice24
  · exact point159Slice25
  · exact point159Slice26
  · exact point159Slice27
  · exact point159Slice28

set_option maxHeartbeats 1600000 in
private theorem point160Slice0 : Part0Residual.pointSliceCheck 0 3122 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice1 : Part0Residual.pointSliceCheck 0 3122 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice2 : Part0Residual.pointSliceCheck 0 3122 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice3 : Part0Residual.pointSliceCheck 0 3122 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice4 : Part0Residual.pointSliceCheck 0 3122 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice5 : Part0Residual.pointSliceCheck 0 3122 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice6 : Part0Residual.pointSliceCheck 0 3122 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice7 : Part0Residual.pointSliceCheck 0 3122 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice8 : Part0Residual.pointSliceCheck 0 3122 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice9 : Part0Residual.pointSliceCheck 0 3122 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice10 : Part0Residual.pointSliceCheck 0 3122 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice11 : Part0Residual.pointSliceCheck 0 3122 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice12 : Part0Residual.pointSliceCheck 0 3122 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice13 : Part0Residual.pointSliceCheck 0 3122 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice14 : Part0Residual.pointSliceCheck 0 3122 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice15 : Part0Residual.pointSliceCheck 0 3122 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice16 : Part0Residual.pointSliceCheck 0 3122 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice17 : Part0Residual.pointSliceCheck 0 3122 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice18 : Part0Residual.pointSliceCheck 0 3122 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice19 : Part0Residual.pointSliceCheck 0 3122 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice20 : Part0Residual.pointSliceCheck 0 3122 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice21 : Part0Residual.pointSliceCheck 0 3122 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice22 : Part0Residual.pointSliceCheck 0 3122 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice23 : Part0Residual.pointSliceCheck 0 3122 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice24 : Part0Residual.pointSliceCheck 0 3122 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice25 : Part0Residual.pointSliceCheck 0 3122 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice26 : Part0Residual.pointSliceCheck 0 3122 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice27 : Part0Residual.pointSliceCheck 0 3122 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point160Slice28 : Part0Residual.pointSliceCheck 0 3122 28 := by
  decide +kernel

public theorem point160 : stepCheck 0 3122 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point160Slice0
  · exact point160Slice1
  · exact point160Slice2
  · exact point160Slice3
  · exact point160Slice4
  · exact point160Slice5
  · exact point160Slice6
  · exact point160Slice7
  · exact point160Slice8
  · exact point160Slice9
  · exact point160Slice10
  · exact point160Slice11
  · exact point160Slice12
  · exact point160Slice13
  · exact point160Slice14
  · exact point160Slice15
  · exact point160Slice16
  · exact point160Slice17
  · exact point160Slice18
  · exact point160Slice19
  · exact point160Slice20
  · exact point160Slice21
  · exact point160Slice22
  · exact point160Slice23
  · exact point160Slice24
  · exact point160Slice25
  · exact point160Slice26
  · exact point160Slice27
  · exact point160Slice28

set_option maxHeartbeats 1600000 in
private theorem point161Slice0 : Part0Residual.pointSliceCheck 0 3125 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice1 : Part0Residual.pointSliceCheck 0 3125 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice2 : Part0Residual.pointSliceCheck 0 3125 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice3 : Part0Residual.pointSliceCheck 0 3125 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice4 : Part0Residual.pointSliceCheck 0 3125 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice5 : Part0Residual.pointSliceCheck 0 3125 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice6 : Part0Residual.pointSliceCheck 0 3125 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice7 : Part0Residual.pointSliceCheck 0 3125 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice8 : Part0Residual.pointSliceCheck 0 3125 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice9 : Part0Residual.pointSliceCheck 0 3125 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice10 : Part0Residual.pointSliceCheck 0 3125 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice11 : Part0Residual.pointSliceCheck 0 3125 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice12 : Part0Residual.pointSliceCheck 0 3125 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice13 : Part0Residual.pointSliceCheck 0 3125 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice14 : Part0Residual.pointSliceCheck 0 3125 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice15 : Part0Residual.pointSliceCheck 0 3125 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice16 : Part0Residual.pointSliceCheck 0 3125 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice17 : Part0Residual.pointSliceCheck 0 3125 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice18 : Part0Residual.pointSliceCheck 0 3125 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice19 : Part0Residual.pointSliceCheck 0 3125 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice20 : Part0Residual.pointSliceCheck 0 3125 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice21 : Part0Residual.pointSliceCheck 0 3125 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice22 : Part0Residual.pointSliceCheck 0 3125 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice23 : Part0Residual.pointSliceCheck 0 3125 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice24 : Part0Residual.pointSliceCheck 0 3125 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice25 : Part0Residual.pointSliceCheck 0 3125 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice26 : Part0Residual.pointSliceCheck 0 3125 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice27 : Part0Residual.pointSliceCheck 0 3125 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point161Slice28 : Part0Residual.pointSliceCheck 0 3125 28 := by
  decide +kernel

public theorem point161 : stepCheck 0 3125 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point161Slice0
  · exact point161Slice1
  · exact point161Slice2
  · exact point161Slice3
  · exact point161Slice4
  · exact point161Slice5
  · exact point161Slice6
  · exact point161Slice7
  · exact point161Slice8
  · exact point161Slice9
  · exact point161Slice10
  · exact point161Slice11
  · exact point161Slice12
  · exact point161Slice13
  · exact point161Slice14
  · exact point161Slice15
  · exact point161Slice16
  · exact point161Slice17
  · exact point161Slice18
  · exact point161Slice19
  · exact point161Slice20
  · exact point161Slice21
  · exact point161Slice22
  · exact point161Slice23
  · exact point161Slice24
  · exact point161Slice25
  · exact point161Slice26
  · exact point161Slice27
  · exact point161Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
